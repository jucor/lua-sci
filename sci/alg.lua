--------------------------------------------------------------------------------
-- Dense vector and matrix algebra module.
--
-- Copyright (C) 2011-2013 Stefano Peluchetti. All rights reserved.
--
-- Features, documention and more: http://www.scilua.org .
--
-- This file is part of the SciLua library, which is released under the MIT 
-- license: full text in file LICENSE.TXT in the library's root folder.
--------------------------------------------------------------------------------

-- SAFETY:
-- TODO: Introduce safety for objs which do not own the allocated memory.
-- TODO: Re-introduce contness (__immutable__?) when initialization of structs
-- TODO: JIT-ed.

-- PERFORMANCE:
-- TODO: Dotprodquad based on template_mat (or similar) with 4 unrolling combos.
-- TODO: Benchmark use of ffi.copy and use it whenever possible.
-- TODO: Specialize for multi-args min, max.
-- TODO: Investigate optimal unrolling strategies.
-- TODO: Fast matmul.
-- TODO: LT, UT matrices, specialize computations and checks on __newindex.

-- FEATURES:
-- TODO: Introduce __new, remove vec_ct, mat_ct.
-- TODO: Generic dotprod for ntbe.
-- TODO: Element-wise * and ^ for matrices.
-- TODO: Cholesky (nil, err on failure, same for other algorithms).
-- TODO: Allow M(A..B, C..D) for matrices.
-- TODO: Elw function for matrix objects.

-- REFACTOR/IMPROVEMENTS:
-- TODO: Instead of parsing $-expr with xsys.process, execute no$-expr to obtain
-- TODO: memebrs, index, eval; at the moment (x+y)+z == x+(y+z) in terms of
-- TODO: members and ntbe-eval is complicated; index would be easier as well.
-- TODO: Use only one version of dim checks (template or code).
-- TODO: Use consistently _n or #.

-- NOTES:
-- The mt spec is used only in expr-expr, not in ntbe-expr.

local ffi  = require "ffi"
local cfg  = require "sci.alg.config"
local xsys = require "xsys"
local math = require "sci.math"
 
local MAXCTNUM = 1e7
assert(MAXCTNUM^2 < 2^52-1) -- In 1eX terms, maximum is 1e7.
 
local DEBUG = false, {
  heap   = false,
  struct = false,
  index  = false,
  op	   = false,
  eval   = false,
}

local err, chk = xsys.handlers("sci.alg")
local RCHECK, SAFESET, UNROLL = xsys.from(cfg,
     "rcheck, safeset, unroll")
 
local type, tonumber, typeof = type, tonumber, ffi.typeof
local concat, insert = table.concat, table.insert
local gsub, upper, find = string.gsub, string.upper, string.find
local fill, istype, cast = ffi.fill, ffi.istype, ffi.cast
local C = ffi.C
local ceil, max, min, isinteger, iseven = xsys.from(math, 
     "ceil, max, min, isinteger, iseven")
local compile = xsys.compile
local process = xsys.preprocess -- TODO: move to process.
local join = xsys.table.join
 
local double_ct    = typeof("double")
local int32_ct     = typeof("int32_t")
local double_ctnum = tonumber(double_ct)
 
ffi.cdef[[
void* malloc(size_t n);
void* realloc (void* p, size_t n);
void free(void *p);
]]
 
-- UTILITY ---------------------------------------------------------------------
local function ptoint(p)
  return tonumber(cast("intptr_t", p))
end

-- Returns unique id string for any given function.
local function ftoname(f)
  if type(f) == "string" then return f end
  local s = "f_"..tostring(f):sub(11):gsub("#", "_")
  return s
end
 
-- Merge two tables making sure that if two keys are the same then the same 
-- holds for the value.
local function mergetbl(x, y)
  local o = {}
  for k,v in pairs(x) do 
    o[k] = v 
  end
  for k,v in pairs(y) do
    if o[k] then 
      assert(o[k] == v)
    else
      o[k] = v
    end
  end
  return o
end
 
local function copytbl(t)
  local o = {}
  for k,v in pairs(t) do
    o[k] = v
  end
  return o
end
 
local function brk(s)
  return "("..s..")"
end
 
-- IDNODE ----------------------------------------------------------------------
local allalg = {}
 
local function associate(ct, ctn)
  chk(ctn < MAXCTNUM, "error", "too many algebra ctypes")
  allalg[ctn] = ct
end
 
-- TODO: The reference registering could be avoided by having an 
-- TODO: ffi.unqualified(ct) function.
local function metatype(...)
  local ct = ffi.metatype(...)
  associate(ct, tonumber(ct))
  if DEBUG and DEBUG.struct then print("metatype", ct) end
  local id = ct():_idnode()
  if id.spec ~= "ntbe" then
    associate(ct, tonumber(typeof("$ &", ct)))
  end
  if id.spec == "orig" then
    associate(ct, tonumber(typeof("$ const &", ct)))
  end  
  return ct
end
 
-- True if x is an algebra object.
local function isalg(x)
  return type(x) == "cdata" and (allalg[tonumber(typeof(x))] ~= nil)
end
 
local idnode_scalar = xsys.cache(function(el_ct)
  return {
    res  = "s",
    tran = false,
    spec = "orig",
    data = { el_ct },
    env  = {},    
    expr = "$(s)",
    nidx = { function(i) return "self._p"..i, 1 end },
    ct   = el_ct,
  }
end, "strong", tonumber)
 
-- Return idnode for any object x assuming non cdata types are doubles. 
local function idnode(x)
  if isalg(x) then 
    return x:_idnode() 
  else
    local ct = type(x) == "cdata" and typeof(x) or double_ct
    return idnode_scalar(ct)
  end
end
 
-- EXPR IDNODE -----------------------------------------------------------------
local function scalarfirst(x, y)
  if x.res == "s" then 
    return x, y
  elseif y.res == "s" then
    return y, x
  else
    return nil
  end
end
 
local function restrans(id) -- Take care of restricting allowed ops as well.
  local op, arg = id.op, id.arg
  if #arg == 1 then -- Unary op, can be "-", "" (transpose), function_name.
    local xid = arg[1]
    local opt = id.op == "" -- Transpose op?
    if opt and xid.res == "m" then
      chk(xid.expr == "$(m)" or xid.expr == "$(mt)", "constraint", 
        "matrix expressions cannot be transposed")
    end
    return xid.res, xid.tran ~= opt
  else -- Binary op.
    local xid, yid = arg[1], arg[2]
    local sid, aid = scalarfirst(xid, yid)
    if sid then                                -- m/v <op> s, s <op> m/v.
      if aid.res == "m" then
        if (op == "^" or op == "%" or op == "/") then
          -- s ^ m, s % m, s / m are confusing.
          chk(xid.res == "m", "constraint", 
            "unsupported matrix-scalar operator") 
        end
        return "m", false
      end
      return "v", aid.tran
    else -- Algebra <op> algebra.
      local xre, yre, xtr, ytr = xid.res, yid.res, xid.tran, yid.tran
      if xre == "m" and yre == "v" then                         -- m * v.
        chk(not ytr, "constraint", "A*x with transposed x")
        chk(op == "*", "constraint", "unsupported matrix-vector operator")
        return "v", ytr
      elseif xre == "v" and yre == "m" then                     -- v * m.
        chk(xtr, "constraint", "x*A with not-transposed x")
        chk(op == "*", "constraint", "unsupported matrix-vector operator")
        return "v", xtr
      elseif xre == "v" and yre == "v" and xtr and not ytr then -- vt * v.
        chk(op == "*", "constraint", 
          "cannot combine transposed and not transposed vectors")
        return "s", false
      elseif xre == "m" and yre == "m" then                     -- m <op> m.
        chk(op == "+" or op == "-" or op == "*", "constraint", 
          "unsupported matrix-matrix operator")
        return "m", false
      else                                                      -- v <op> v.
        chk(xtr == ytr, "constraint", 
          "cannot combine transposed and not transposed vectors")
        assert(xre == yre)
        return "v", xtr
      end
    end
  end
end

local function ismatvecmul(id)
  local op, arg = id.op, id.arg
  if op == "*" then
    local xid, yid = arg[1], arg[2]
    local xre, yre = xid.res, yid.res
    if (xre == "m" and yre == "v") or (xre == "v" and yre == "m") then
      return true
    end
  end
  return false
end

local function ismatmatmul(id)
  local op, arg = id.op, id.arg
  if op == "*" then
    local xid, yid = arg[1], arg[2]
    local xre, yre = xid.res, yid.res
    local xsp, ysp = xid.spec, yid.spec
    if xre == "m" and yre == "m" and xsp ~= "ntbe" and ysp ~= "ntbe" then
      return true
    end
  end
  return false
end

local function ismatscapow(id)
  local op, arg = id.op, id.arg
  if op == "^" then
    local xid, yid = arg[1], arg[2]
    local xre, yre = xid.res, yid.res
    local xsp, ysp = xid.spec, yid.spec
    if xre == "m" and yre == "s" and xsp ~= "ntbe" and ysp ~= "ntbe" then
      return true
    end
  end
  return false
end
 
local function hasmatvecmul(id)
  local arg, op = id.arg, id.op
  -- Stopping criteria.
  if not op then
    return false
  elseif ismatvecmul(id) then
    return true
  end
  -- Recursion.
  if #arg == 1 then
    return hasmatvecmul(arg[1])
  else
    return hasmatvecmul(arg[1]) or hasmatvecmul(arg[2])
  end
end
 
local function spec(id)
  local arg, op = id.arg, id.op
  if #arg == 1 then
    local xid = arg[1]
    if op ~= "" then
      return xid.spec
    else
      return xid.spec ~= "orig" and xid.spec or "expr"
    end
  else
    local xid, yid = arg[1], arg[2]
    local xre, yre = xid.res, yid.res
    if (xid.spec == "ntbe" or yid.spec == "ntbe")         -- Propagate ntbe.
    or (op == "*" and xre == "m" and yre == "m")          -- m * m.
    or (op == "^" and xre == "m" and yre == "s") then     -- m ^ s.
      return "ntbe"
    elseif (op == "*" and xre == "m" and yre == "v") then -- m * v.      
      return hasmatvecmul(yid) and "ntbe" or "expr"
    elseif (op == "*" and xre == "v" and yre == "m") then -- vt * m.
      return "ntbe"
    else
      return "expr"
    end
  end
end

local function data(id)
  local arg, spec, op = id.arg, id.spec, id.op
  if #arg == 1 then
    local xid = arg[1]
    return xid.data
  else
    local xid, yid = id.arg[1], id.arg[2]
    local xre, yre = xid.res, yid.res
    if spec == "ntbe" then
      local xda = xid.spec ~= "ntbe" and { xid.ct } or xid.data
      local yda = yid.spec ~= "ntbe" and { yid.ct } or yid.data
      return join(xda, yda)
    elseif ismatvecmul(id) then
      return join({ xid.ct }, { yid.ct }) 
    else
      return join(xid.data, yid.data)
   end
  end
end
 
local function env(id, op)
  local xen, yen = id.arg[1].env, id.arg[2] and id.arg[2].env or {}
  return type(op) == "string" 
     and mergetbl(xen, yen)
      or mergetbl(mergetbl({ [id.op] = op }, xen), yen)
end
 
local function expr(id)
  local arg, op, spec = id.arg, id.op, id.spec
  if #arg == 1 then
    local xid = arg[1]
    if op == "" then -- Transpose.
      local xex = xid.expr
      if id.res == "v" then
        return xex
      else
        return xex == "$(m)" and "$(mt)" or "$(m)"
      end
    else
      chk(id.res ~= "m", "NYI", "element-wise functions for matrices are NYI")
      return op..brk(xid.expr)
    end
  else
    local xid, yid = id.arg[1], id.arg[2]
    if spec ~= "ntbe" then
      if ismatvecmul(id) then
        local xex = xid.expr == "$(mt)" and "$(mt)" or "$(m)"
        return "ker("..xex..",$(v), 0)"
      else
        return brk(xid.expr)..op..brk(yid.expr)
      end
    else
      local xex = xid.spec ~= "ntbe" and "$("..xid.res..")" or xid.expr
      local yex = yid.spec ~= "ntbe" and "$("..yid.res..")" or yid.expr
      return brk(xex)..op..brk(yex)
    end
  end
end
 
local matnidx = { function(i) 
  return "self._p"..i.."+self._p"..(i+1).."*(k-1)", 2 
end }
local mattidx = { function(i) 
  return "self._p"..i.."+k-1,self._p"..(i+1) , 2 
end }

local mvmulnidx = { function(i)
  return "self._p"..i.."._m,self._p"..i.."[k]" , 1
  end, function(i)
  return "self._p"..i, 1
end }
 
local function nidx(id)
  local op, arg, res, spec = id.op, id.arg, id.res, id.spec
  if spec == "ntbe" then
    return {}
  elseif #arg == 1 then
    local xid = arg[1]
    if op == "" and res == "m" then
      return id.tran and mattidx or matnidx
    else
      return xid.nidx
    end
  elseif ismatvecmul(id) then
    -- local xid = id.arg[1]
    -- return xid.res == "m" and mvmulnidx or vmmulnidx
    return mvmulnidx
  else
    local xid, yid = id.arg[1], id.arg[2]
    return join(xid.nidx, yid.nidx)
  end
end
 
local function stac(id)
  local op, arg = id.op, id.arg
  if #arg == 1 then
    local xid = arg[1]
    return xid.stac
  else -- Binary op.
    local xid, yid = arg[1], arg[2]
    local sid, aid = scalarfirst(xid, yid)
    if sid then
      return aid.stac
    else
      local xre, yre = xid.res, yid.res
      if xre == "m" and yre == "v" then      -- m * v.
        return yid.stac
      elseif xre == "v" and yre == "m" then  -- v * m.
        return xid.stac
      else -- Prefer lhs, consistent with metatable selection for ops.
        return xid.stac
      end
    end
  end    
end
 
-- EXPR CTYPE ------------------------------------------------------------------
local function members1(id1, var, id)
  local res, data = id1.res, id1.data
  if res == "s" then 
    return var, nil
  elseif id.spec == "ntbe" and id1.spec ~= "ntbe" then -- Ntbe case.
    return var, (res == "v" and var.."._n" or var.."._n,"..var.."._m")
  elseif id.spec ~= "ntbe" and ismatvecmul(id) then
    return var, (res == "v" and var.."._n" or var.."._n,"..var.."._m")
  else
    local dat = {}  
    for i=1,#data do
      dat[i] = var.."._p"..i
    end
    dat = concat(dat, ",")
    return dat, (res == "v" and var.."._n" or var.."._n,"..var.."._m")
  end
end
 
local function members(id)
  local arg = id.arg
  if #arg == 1 then
    local xid = arg[1]
    local dat, dim = members1(xid, "x", id)
    if id.op == "" and xid.res == "m" then
      dim = "x._m,x._n"
    end
    return dim and dat..","..dim or dat
  else
    local xid, yid = id.arg[1], id.arg[2]
    local xda, xdi = members1(xid, "x", id)
    local yda, ydi = members1(yid, "y", id)
    if id.op == "*" then -- Handle special cases.
      local xre, yre = xid.res, yid.res
      if xre == "m" and yre == "m" then
          xdi = "x._n,y._m"
      elseif xre == "m" and yre == "v" then
        xdi = "x._n"
      elseif xre == "v" and yre == "m" then
        xdi = "y._m"
      end
    end
    return xda..","..yda..","..(xdi or ydi)
  end
end
 
local dimcheck_vec = [[
if not (#x == #y) then 
  err("range", "#x="..#x.." ~= #y="..#y) 
end ]]
local dimcheck_mat = [[
if not (x:nrow() == y:nrow() and x:ncol() == y:ncol()) then
  err("range", "x:nrow()="..x:nrow().." ~= y:nrow()="..y:nrow()
         .." or x:ncol()="..x:ncol().." ~= y:ncol()="..y:ncol())
end
]]
local dimcheck_matprod = [[
if not (x:ncol() == y:nrow()) then
  err("range", "x:ncol()="..x:ncol().." ~= y:nrow()="..y:nrow())
end
]]
local dimcheck_square = [[
if not (x:nrow() == x:ncol()) then
  err("range", "matrix not square: nrow="..x:nrow()..", ncol="..x:ncol())
end
]]
local dimcheck_mat_vec = [[
if not (x:ncol() == #y) then
  err("range", "x:ncol()="..x:ncol().." ~= #y="..#y)
end
]]
local dimcheck_vec_mat = [[
if not (#x == y:nrow()) then
  err("range", "#x="..#x.." ~= y:nrow()="..y:nrow())
end
]]
 
local function check(id)
  if not RCHECK then 
    return nil 
  end
  local arg, op = id.arg, id.op
  if #arg == 1 then
    return nil
  else
    local xre, yre = arg[1].res, arg[2].res
    if xre == "v" and yre == "v" then
      return dimcheck_vec
    elseif xre == "m" and yre == "m" then
      return op ~= "*" and dimcheck_mat or dimcheck_matprod
    elseif xre == "m" and op == "^" then
      return dimcheck_square
    elseif xre == "m" and yre == "v" then
      return dimcheck_mat_vec
    elseif xre == "v" and yre == "m" then
      return dimcheck_vec_mat
    else
      return nil
    end
  end
end
 
local function pre(id)
  local res, data, spec = id.res, id.data, id.spec
  if spec == "ntbe" or hasmatvecmul(id) then
    local o = {}
    for i=1,#data do
      o[i] = "o._p"..i
    end
    o[#o+1] = res == "v" and "o._n" or "o._n,o._m"
    return concat(o, ",")
  else
    return nil
  end
end
 
-- Return ctype for the anonymous struct for an algebra object.
local function algct(id)
  local res, data = id.res, id.data
  assert(res == "v" or res == "m", res)
  local o = { "struct {" }
  for i=1,#data do
    o[i+1] = "$ _p"..i..";"
  end
  o[#o+1] = res == "v" and "int32_t _n;\n}" 
    or "int32_t _n;\nint32_t _m;\n}"
  local struct = concat(o, "\n")
  if DEBUG and DEBUG.struct then print(struct, unpack(data)) end
  return typeof(struct, unpack(data))
end
 
-- T0D0: Remove nested struct by hand init when this gets JIT-supported.
-- Return constructor function for any algebra ctype ct for a given op.
local function exprct(ct, members, check, pre)
  check = check or ""  
  if DEBUG and DEBUG.struct then 
    print("members", members)
    print("check", check) 
    print("pre", pre) 
  end
  local s = [[$(pre and 'local o = ct()') 
return function(x, y) 
  $(check)
  $(pre and pre..'='..members)  
  return $(pre and 'o' or 'ct('..members..')')
end]]
  return compile(s, "exprct", { ct = ct, err = err }, 
    { pre = pre, check = check, members = members })
end
 
-- COMPUTATIONS ----------------------------------------------------------------
local function setvec(x, y, safe)
  if safe or SAFESET then
    local t = x:_stackcreate(x._n)
    y._eval(t, y) -- Strategy for eval is always based on the rhs!
    t._eval(x, t)
    t:_stackrelease(x._n)
  else
    y._eval(x, y) -- Strategy for eval is always based on the rhs!
  end
end

local function setmat(x, y, safe)
  if safe or SAFESET then
    local t = x:_stackcreate(x._n, x._m)
    y._eval(t, y) -- Strategy for eval is always based on the rhs!
    t._eval(x, t)
    t:_stackrelease(x._n, x._m)
  else
    y._eval(x, y) -- Strategy for eval is always based on the rhs!
  end
end
 
local template_vec = [[
local function ker(n, x, y, v)
# for n=1,unroll do
  $(n==1 and 'if' or 'elseif') n == $(n) then
#   for i=1,n do  
    $(elw(i))
#   end
# end
  $(unroll>=1 and 'else')
    for i=1,n do
      $(elw("i"))
    end
  $(unroll>=1 and 'end')
  $(init and 'return v')
end
 
local function com(x, y)
  local n = #x
  $(dimcheck)  
  $(init and 'return ')ker(n, x, y, $(init or 'nil'))
end
 
return com, ker
]]
 
local env_vec = { err = err, min = min, max = max }
 
local function compile_vec(name, pre, dcheck)
  local dimcheck = (RCHECK and dcheck) and dimcheck_vec or nil
  local pre_vec = mergetbl(pre, { unroll = UNROLL, dimcheck = dimcheck })
  return compile(template_vec, name.."vec", env_vec, pre_vec)
end
 
local applyvec, applyvecker = compile_vec("apply", {
  elw = function(i) return "x["..i.."] = y(x["..i.."])" end,
}, false)
local genvec, genvecker = compile_vec("gen", {
  elw = function(i) return "x["..i.."] = y()" end,
}, false)
local fillvec, fillvecker = compile_vec("fill", {
  elw = function(i) return "x["..i.."] = y" end,
}, false)
 
local evalvec, evalvecker = compile_vec("eval", {
  elw = function(i) return "x["..i.."] = y["..i.."]" end,
}, true)
 
local dotprodvec, dotprodvecker = compile_vec("dotprod", {
  init = "0",
  elw  = function(i) return "v = v + x["..i.."]*y["..i.."]" end,
}, true) -- Return 0 if size is 0.
 
local eqvec, eqvecker = compile_vec("eq", {
  init = "true",
  elw  = function(i) 
    return "if not (x["..i.."] == y["..i.."]) then v = false end" 
  end,
}, true) -- Return true if size is 0.
local ltvec, ltvecker = compile_vec("lt", {
  init = "true",
  elw  = function(i) 
    return "if not (x["..i.."] < y["..i.."]) then v = false end" 
  end,
}, true) -- Return true if size is 0.
local levec, levecker = compile_vec("le", {
  init = "true",
  elw  = function(i) 
    return "if not (x["..i.."] <= y["..i.."]) then v = false end" 
  end,
}, true) -- Return true if size is 0.
 
local maxvec, maxvecker = compile_vec("max", {
  init = "-1/0",
  elw = function (i) return "v = max(v, x["..i.."])" end,
}, false) -- Return -1/0 if size is 0.
local minvec, minvecker = compile_vec("min", {
  init = "1/0",
  elw = function (i) return "v = min(v, x["..i.."])" end,
}, false) -- Return 1/0 if size is 0.
local sumvec, sumvecker = compile_vec("sum", {
  init = "0",
  elw = function (i) return "v = v + x["..i.."]" end,
}, false) -- Return 0 if size is 0.
local prodvec, prodvecker = compile_vec("prod", {
  init = "1",
  elw = function (i) return "v = v * x["..i.."]" end,
}, false) -- Return 1 if size is 0.
local avgvec = function(x)
  return sumvec(x)/#x
end -- Return 0/0 if size is 0.
 
local template_mat = [[
return function(x, y)
  local n, m = x:nrow(), x:ncol()
  $(dimcheck)
  $(init and 'local v = '..init)
# if unroll == 0 then
  for i=1,n do
    for j=1,m do
      $(elw("i", "j"))
    end
  end
# else
  if m <= $(unroll) then 
#   for n=1,unroll do -- Unroll r, c.
    $(n==1 and 'if' or 'elseif') n == $(n) then
#     for i=1,n do 
      $(elwfix(i))
#     end
#   end
    else -- Unroll c.
      for i=1,n do
        $(elwfix("i"))
      end
    end
  else
#   for n=1,unroll do -- Unroll r.
    $(n==1 and 'if' or 'elseif') n == $(n) then
#     for i=1,n do 
      for j=1,m do
        $(elw(i, "j"))
      end
#     end
#   end
    else -- No unroll.
      for i=1,n do
        for j=1,m do
          $(elw("i", "j"))
        end
      end
    end
  end
# end
  $(init and 'return v')
end
]]
 
local env_mat = env_vec
 
local function compile_mat(name, pre, ker, dcheck)
  local dimcheck = (RCHECK and dcheck) and dimcheck_mat or nil
  local pre_mat = mergetbl(pre, { unroll = UNROLL, dimcheck = dimcheck })
  local env_mat = mergetbl(env_mat, { ker = ker })
  return compile(template_mat, name.."mat", env_mat, pre_mat)
end
 
local function idx2dstr(i, j)
  return "["..i.."]["..j.."]"
end
 
local function elwfix1(i)
  return "ker(m, x["..i.."], y)"
end
 
local function elwfix1v(i)
  return "v = ker(m, x["..i.."], y, v)"
end
 
local function elwfix2(i)
  return "ker(m, x["..i.."], y["..i.."])"
end
 
local function elwfix2v(i)
 return "v = ker(m, x["..i.."], y["..i.."], v)"
end
 
local applymat = compile_mat("apply", {
  elw = function(i, j) 
    local idx2 = idx2dstr(i, j)
    return "x"..idx2.." = y(x"..idx2..")"
  end,
  elwfix = elwfix1,
}, applyvecker, false)
local genmat = compile_mat("gen", {
  elw = function(i, j) 
    local idx2 = idx2dstr(i, j)
    return "x"..idx2.." = y()"
  end,
  elwfix = elwfix1,
}, genvecker, false)
local fillmat = compile_mat("fill", {
  elw = function(i, j) 
    local idx2 = idx2dstr(i, j)
    return "x"..idx2.." = y"
  end,
  elwfix = elwfix1,
}, fillvecker, false)
 
local evalmat = compile_mat("eval", {
  elw = function(i, j) 
    local idx2 = idx2dstr(i, j)
    return "x"..idx2.." = y"..idx2 
  end,
  elwfix = elwfix2,
}, evalvecker, true)
 
local evalmatnorcheck = compile_mat("eval", {
  elw = function(i, j) 
    local idx2 = idx2dstr(i, j)
    return "x"..idx2.." = y"..idx2 
  end,
  elwfix = elwfix2,
}, evalvecker, false)
 
local eqmat = compile_mat("eq", {
  init = "true",
  elw  = function(i, j)
    local idx2 = idx2dstr(i, j)
    return "if not (x"..idx2.." == y"..idx2..") then v = false end"
  end,
  elwfix = elwfix2v,
}, eqvecker, true) -- Return true if size is 0.
local ltmat = compile_mat("lt", {
  init = "true",
  elw  = function(i, j)
    local idx2 = idx2dstr(i, j)
    return "if not (x"..idx2.." < y"..idx2..") then v = false end"
  end,
  elwfix = elwfix2v,
}, ltvecker, true) -- Return true if size is 0.
local lemat = compile_mat("le", {
  init = "true",
  elw  = function(i, j)
    local idx2 = idx2dstr(i, j)
    return "if not (x"..idx2.." <= y"..idx2..") then v = false end"
  end,
  elwfix = elwfix2v,
}, levecker, true) -- Return true if size is 0.
 
local maxmat = compile_mat("max", {
  init = "-1/0",
  elw  = function(i, j)
    local idx2 = idx2dstr(i, j)
    return "v = max(v , x"..idx2..")"
  end,
  elwfix = elwfix1v,
}, maxvecker, false) -- Return -1/0 if size is 0.
local minmat = compile_mat("min", {
  init = "1/0",
  elw  = function(i, j)
    local idx2 = idx2dstr(i, j)
    return "v = min(v , x"..idx2..")"
  end,
  elwfix = elwfix1v,
}, minvecker, false) -- Return 1/0 if size is 0.
local summat = compile_mat("sum", {
  init = "0",
  elw  = function(i, j)
    local idx2 = idx2dstr(i, j)
    return "v = v + x"..idx2
  end,
  elwfix = elwfix1v,
}, sumvecker, false) -- Return 0 if size is 0.
local prodmat = compile_mat("prod", {
  init = "1",
  elw  = function(i, j)
    local idx2 = idx2dstr(i, j)
    return "v = v * x"..idx2
  end,
  elwfix = elwfix1v,
}, prodvecker, false) -- Return 1 if size is 0.
local avgmat = function(x)
  return summat(x)/(x:nrow()*x:ncol())
end -- Return 0/0 if size is 0.
 
local methods_orig = { v = {
  apply = applyvec,
  fill  = fillvec,   
  gen   = genvec,
  set   = setvec,
}, m = {
  apply = applymat,
  fill  = fillmat,
  gen   = genmat,
  set   = setmat,
} }
 
--------------------------------------------------------------------------------
local __add, __sub, __mul, __div, __pow, __mod, __unm, __t
 
local function setlazyops(mt, id) -- Lazy operators.
  mt.__add = __add
  mt.__sub = __sub
  mt.__mul = __mul
  mt.__div = __div
  mt.__pow = __pow
  mt.__mod = __mod
  mt.__unm = __unm
  mt.t     = __t
end
 
local indextemplate = [[
return function(self, k)
  if type(k) == "number" then
    $(rcheck)
    return $(index)
  else    
    return mt[k]
  end
end
]]
 
local newindextemplate = [[
return function(self, k, v)
  $(rcheck)
  $(index) = v
end
]]
 
local rchecktemplate = [[
if not (1 <= k and k <= self._n) then 
  err("range", "out of range index: i="..k..", #="..self._n) 
end
]]
  
local parse_plain = { __index = function(self, k)
  local idx, inc = self.nidx[self.e](self.i)
  self.e = self.e + 1
  self.i = self.i + inc
  return idx
end
}
 
local parse_mat_expr = { __index = function(self, k)
  if k == "s" then
    local idx, inc = self.nidx[self.e](self.i)
    self.e = self.e + 1
    self.i = self.i + inc
    return idx
  elseif k == "m" then
    local idx, inc = self.nidx[self.e](self.i)
    self.e = self.e + 1
    self.i = self.i + inc
    return "vecv_ct("..idx..", self._n)"
  elseif k == "mt" then
    local idx, inc = self.nidx[self.e](self.i)
    self.e = self.e + 1
    self.i = self.i + inc
    return "vecs_ct("..idx..", self._n)"
  else
    error(k)
  end
end
}

local function exprdedollar(s)
  return gsub(s, "%$%(%a%a?%)", function(x) return x:sub(3,-2) end)
end

local ntbe_mt

local function ntbebinop(op)
  return function(x, y)
    assert(x.i == y.i)
    local xex, yex
    if x.o then
      x.i[1] = x.i[1] + 1
      xex = x.o..x.i[1]    
    else
      xex = x.re
    end
    if y.o then
      y.i[1] = y.i[1] + 1
      yex = y.o..y.i[1]    
    else
      yex = y.re
    end
    local re = brk(xex)..op..brk(yex)
    return setmetatable({ i = x.i, re = re }, expr_mt)
  end
end

local function ntbeunaop(op)
  return function(x)
    local xex
    if not x.re then
      x.i[1] = x.i[1] + 1
      xex = x.o..x.i[1]    
    else
      xex = x.re
    end
    local re = op..brk(xex)
    return setmetatable({ i = x.i, re = re }, expr_mt)
  end
end

ntbe_mt = {
  __add = ntbebinop("+"),
  __sub = ntbebinop("-"),
  __mul = ntbebinop("*"),
  __div = ntbebinop("/"),
  __pow = ntbebinop("^"),
  __mod = ntbebinop("%"),
  __unm = ntbeunaop("-"),
}

local function ntbect(itbl)
  return setmetatable({ i = itbl, o = "self._p" })
end
 
local function index(id, parser, expr)
  expr = expr or id.expr
  if DEBUG and DEBUG.index then print("expr", expr) end
  local s = process(expr, 
    setmetatable({ e = 1, i = 1, nidx = id.nidx }, parser))  
  if DEBUG and DEBUG.index then print("index", s) end
  return s
end
 
local function setindex(mt, id, ct) -- For all algebra obj.
  if id.spec == "ntbe" then
    mt.__index = mt
  else
    local rcheck = RCHECK and rchecktemplate or ""
    local env = { type = type, mt = mt, err = err, ker = dotprodvecker }
    xsys.import(env, id.env)
    if id.res == "v" or id.spec == "orig" then
      local index = index(id, parse_plain)
      if id.res == "m" then
        index = RCHECK and "vecv_ct("..index..", self._m)" or index.."-1"
      end
      mt.__index = compile(indextemplate, "algindex", env,
        { rcheck = rcheck, index = index })
    else
      local tindex = index(id, parse_mat_expr)
      local tindex = compile(indextemplate, "talgindex", env, 
        { index = tindex })
      local trow_ct = tindex(ct(), 0)
      local row_ct = allalg[tonumber(typeof(trow_ct))]
      env.row_ct = row_ct
      local expr = {}
      gsub(id.expr, "%$%(%a%a?%)", function(x) insert(expr, x) end)
      expr = "row_ct("..concat(expr, ",")..",self._m)"
      if DEBUG and DEBUG.index then print("expr", expr) end
      local index = index(id, parse_plain, expr)
      mt.__index = compile(indextemplate, "algindex", env,
        { rcheck = rcheck, index = index })
    end
  end
end
 
local function setnewindex(mt, id) -- For v & orig only.
  local rcheck = RCHECK and rchecktemplate or ""
  local env = { err = err }
  local index = index(id, parse_plain)
  mt.__newindex = compile(newindextemplate, "algnewindex", env,
    { rcheck = rcheck, index = index })
end
 
local function setstack(mt, id)
  mt._stackcreate, mt._stackrelease = id.stac[1], id.stac[2]
end
 
local methods_ntbe = { 
  v = {
  __len = function(self)
    return self._n
  end,
  __tostring = function(self)
    return "v("..#self..")"
  end,
  }, m = {
  nrow = function(self)
    return self._n
  end,
  ncol = function(self)
    return self._m
  end,
  __tostring = function(self)
    return "m("..self:nrow()..","..self:ncol()..")"
  end,
  }
}
 
local methods_expr = { 
  v = {
  __tostring = function(self)
    local o = {}
    for i=1,#self do 
      o[i] = tostring(self[i]) 
    end
    return "{"..concat(o, ",").."}"
  end,
  totable = function(self)
    local o = {}
    for i=1,#self do 
      o[i] = self[i] 
    end
    return o
  end,
  __eq = eqvec,
  __lt = ltvec,
  __le = levec,
  max  = maxvec,
  min  = minvec,
  sum  = sumvec,
  prod = prodvec,
  avg  = avgvec,
}, m = { 
  __tostring = function(self)
    local o = {}
    for r=1,self:nrow() do
      local oo = {}
      for c=1,self:ncol() do
        oo[c] = tostring(self[r][c])
      end
      o[r] = "{"..concat(oo, ",").."}"
    end
    return "{"..concat(o, ",").."}"
  end,
  totable = function(self)
    local o = {}
    for r=1,self:nrow() do
      local oo = {}
      for c=1,self:ncol() do
        oo[c] = self[r][c]
      end
      o[r] = oo
    end
    return o
  end,
  __eq = eqmat,
  __lt = ltmat,
  __le = lemat,
  max  = maxmat,
  min  = minmat,
  sum  = summat,
  prod = prodmat,
  avg  = avgmat,
}}
 
local function setmethods(mt, id, methods)
  for k,v in pairs(methods[id.res]) do
    mt[k] = v
  end
end
 
--------------------------------------------------------------------------------
local matmul_template = [[
local function inner(R, A, B, r, c, s)
#	for s=1,unroll do
  $(s==1 and 'if' or 'elseif') s == $(s) then
#	  for i=1,s do
    R[r][c] = R[r][c] + A[r][$(i)]*B[$(i)][c]
#   end
#	end
  $(unroll>=1 and 'else')
  for i=1,s do
    R[r][c] = R[r][c] + A[r][i]*B[i][c]
  end
  $(unroll>=1 and 'end')
end

return function(R, A, B)
  local n, m, s = A._n, B._m, A._m
#	if unroll == 0 then
  for r=1,n do
    for c=1,m do
      R[r][c] = 0
      for i=1,s do
        R[r][c] = R[r][c] + A[r][i]*B[i][c]
      end
    end
  end
#	else
  for r=1,n do
    for c=1,m do
      R[r][c] = 0
      inner(R, A, B, r, c, s)
    end
  end
#	end
end
]]

-- Compute R = A*B.
local matmul = compile(matmul_template, "matmul", {}, { unroll = UNROLL })

-- Arg 4 must never alias arg 1 or 2.
local function matpowrec(R, A, s, T1, T2)
  if s == 1 then
    T1:set(R*A)
    R:set(T1)
  elseif iseven(s) then
    T1:set (A*A)
    matpowrec(R, T1, s/2, T2, T1)
  else
    T1:set(R*A)
    R:set(T1)
    T1:set (A*A)
    matpowrec(R, T1, (s-1)/2, T2, T1)
  end
end

-- Compute R = A^s.
local function matpow(R, A, s)
  if RCHECK then
    chk(isinteger(s) and s >= 0, "error", "power of a matrix must be an integer ",
    ">= 0, is ",s)
  end
  if s == 0 then
    R:fill(0)
    R:diag():fill(1)
  elseif s == 1 then
    R:set(A)
  elseif s == 2 then
    R:set(A*A)
  elseif s == 3 then
    R:set(A*A*A)
  elseif s == 4 then
    local T = R:_stackcreate(R._n, R._m)
    T:set(A*A)
    R:set(T*T)
    R:_stackrelease(R._n, R._m)
  else
    local T1, T2 = R:_stackcreate(R._n, R._m), R:_stackcreate(R._n, R._m)
    R:fill(0)
    R:diag():fill(1)
    matpowrec(R, A, s, T1, T2)
    R:_stackrelease(R._n, R._m)
    R:_stackrelease(R._n, R._m)
  end
end

local template_dotprodquad = [[
return function(x, A, y)
  local n, m = #x, #y -- Dimensions are already checked.
  local v = 0
# for n=1,unroll do
  $(n==1 and 'if' or 'elseif') n == $(n) then
#   for i=1,n do  
    v = v + x[$(i)]*ker(m, A[$(i)], y, 0)
#   end
# end
  $(unroll>=1 and 'else')
    for i=1,n do
      v = v + x[i]*ker(m, A[i], y, 0)
    end
  $(unroll>=1 and 'end')
  return v
end
]]
 
local dotprodquad = compile(template_dotprodquad, "vecdotprodquad",
  { ker = dotprodvecker }, { unroll = UNROLL })
 
local function dotprodquadl(vt, q)
  local m, v = q._p1, q._p2
  return dotprodquad(vt, m, v)
end
 
local function dotprodquadr(q, v)
  local vt, m = q._p1, q._p2
  return dotprodquad(vt, m, v)
end

local function mmmuleval(x, y)
  matmul(x, y._p1, y._p2)
end

local function mspoweval(x, y)
  matpow(x, y._p1, y._p2)
end

local function numberexpr(s, n, pre)
  s = gsub(s, "%a-%$%((%a%a?)%)", function(x)
    n = n + 1
    local p = x..n
    insert(pre, p)
    return "("..p..")"
  end)
  return s, n
end

local function matmatmulexpr(s, n, pre, comp, post)
  s = gsub(s, "(%(%(m%d-%)%)%*%(%(m%d-%)%))", function(x)
    n = n + 1
    local R, _, _, A, B = "m"..n, find(x, "%(%((m%d-)%)%)%*%(%((m%d-)%)%)")
    local An, Bm = A.."._n", B.."._m"
    insert(pre, "local "..R.." = "..A..":_stackcreate("..An..","..Bm..")")
    insert(comp, "matmul("..concat({ R, A, B }, ",")..")")
    insert(post, A..":_stackrelease("..An..","..Bm..")")
    return "("..R..")"
  end)
  return s, n
end

local function matmatpowexpr(s, n, pre, comp, post)
  s = gsub(s, "(%(%(m%d-%)%)%^%(%(s%d-%)%))", function(x)
    n = n + 1
    local R, _, _, A, B = "m"..n, find(x, "%(%((m%d-)%)%)%^%(%((s%d-)%)%)")
    local An, Am = A.."._n", A.."._m"
    insert(pre, "local "..R.." = "..A..":_stackcreate("..An..","..Am..")")
    insert(comp, "matpow("..concat({ R, A, B }, ",")..")")
    insert(post, A..":_stackrelease("..An..","..Am..")")
    return "("..R..")"
  end)
  return s, n
end
 
local function dotprod(id)
  local spec, xid, yid = id.spec, id.arg[1], id.arg[2]
  if ismatvecmul(xid) then
    local vsp, msp = xid.arg[1].spec, xid.arg[2].spec
    if vsp ~= "ntbe" and msp ~= "ntbe" then
      return dotprodquadr -- (vt * m) * v not-ntbe.
    end
  elseif spec ~= "ntbe" then
    if ismatvecmul(yid) then
      return dotprodquadl -- vt * (m * v) not-ntbe.  
    else
      return dotprodvec   -- vt * v non-ntbe.
    end
  else
    error("NYI")
  end
end

local function seteval(mt, id) -- After dotprod.
  local res, spec = id.res, id.spec
  if spec ~= "ntbe" then
    if res == "v" then
      mt._eval = evalvec
    else
      mt._eval = evalmat
    end
  elseif ismatmatmul(id) then
    mt._eval = mmmuleval
  elseif ismatscapow(id) then
    mt._eval = mspoweval
  else
    local pre, comp, post = {}, {}, {}
    local s, n = numberexpr(id.expr, 0, pre)
    local ypn = {}
    for i=1,n do
      ypn[i] = "y._p"..i
    end
    pre = { "local "..concat(pre, ",").." = "..concat(ypn, ",") }
    while true do
      local s2, n2 = matmatmulexpr(s, n, pre, comp, post)
      s2, n2 = matmatpowexpr(s2, n2, pre, comp, post)
      if n == n2 then break end
      s, n = s2, n2
    end
    local evalcode = concat({
      "return function(x, y)",
      concat(pre, "\n"),
      concat(comp, "\n"),
      "x:set("..s..")",
      concat(post, "\n"),
      "end"}, "\n")
    if DEBUG and DEBUG.eval then print("eval", evalcode) end
    local eval = compile(evalcode, "evalntbe",
      { matmul = matmul, matpow = matpow })
    mt._eval = eval
  end
end

--------------------------------------------------------------------------------
local function opf(id, op)
  if id.res ~= "s" then
    id.data = data(id)
    id.env  = env(id, op)
    id.expr = expr(id)
    id.nidx = nidx(id)
    id.stac = stac(id)
    
    local ct = algct(id)
    local mt = {}
    mt._idnode = function()
      return id
    end
    
    setlazyops(mt, id)
    seteval(mt, id)
    setmethods(mt, id, methods_ntbe)
    setindex(mt, id, ct)
    setstack(mt, id)
    
    if id.spec ~= "ntbe" then
      setmethods(mt, id, methods_expr)
    end
    
    local ct = metatype(ct, mt)
    id.ct = ct
    return exprct(ct, members(id), check(id), pre(id))      
  else
    return dotprod(id)
  end
end
 
local function dispatcher(op)
  return setmetatable({}, { __index = function(self, ctnum)  
    return function(x, y) 
      local idlhs, idrhs = idnode(x), y and idnode(y) or nil
      local id = {
        op   = ftoname(op),
        arg  = { idlhs, idrhs }
      }
      id.res, id.tran  = restrans(id)
      id.spec = spec(id)
      if DEBUG and DEBUG.op then 
        print("op", "<"..id.op..">", "res", id.res, "spec", id.spec) 
      end
      local f = opf(id, op)
      self[ctnum] = f
      return f(x, y)
    end
  end })
end
 
local function binop(op)
  local dispatch = dispatcher(op)  
  return function(x, y)
    local rhst = type(y) == "cdata" and tonumber(typeof(y)) or double_ctnum
    local lhst = type(x) == "cdata" and tonumber(typeof(x)) or double_ctnum
    return dispatch[lhst + rhst*MAXCTNUM](x, y)
  end
end
 
local function unaop(op)
  local dispatch = dispatcher(op)  
  return function(self)
    return dispatch[tonumber(typeof(self))](self)
  end
end
 
__add = binop("+")
__sub = binop("-")
__mul = binop("*")
__div = binop("/")
__pow = binop("^")
__mod = binop("%")
__unm = unaop("-")
__t   = unaop("") -- Transpose.
--------------------------------------------------------------------------------
local function __gc(self)
  if DEBUG and DEBUG.heap then print("free", ptoint(self._p1)) end
  C.free(self._p1)
end
 
local algtypeof = xsys.cache(function(el_ct)
 
local elptr_ct  = typeof("$*",    el_ct)
local elsize    = ffi.sizeof(el_ct)
 
-- Tags: v = view, s = strided view, o = owner.
local vecv_mt, vecs_mt, veco_mt = {}, {}
local vecv_ct, vecs_ct, veco_ct, vec
local matv_mt, mato_mt = {}
local matv_ct, mato_ct, mat
 
--------------------------------------------------------------------------------
local function sub_check(self, f, l)
  if not (f <= l and 1 <= f and l <= self._n) then
    err("range", "out of range view: first="..f..", last="..l..", #="..#self)
  end
end
 
vecv_mt.sub = function(self, f, l)
  l = l or #self
  if RCHECK then 
    sub_check(self, f, l) 
  end
  return vecv_ct(self._p1 + f - 1, l - f + 1)
end
 
vecs_mt.sub = function(self, f, l)
  l = l or #self
  if RCHECK then 
    sub_check(self, f, l) 
  end
  return vecs_ct(self._p1 + f - 1, self._p2, l - f + 1)
end
 
local function stride_check(self, onein)
  chk(onein >= 1, "range", "onein=",onein," not >= 1")
end
 
vecv_mt.stride = function(self, onein)
  if RCHECK then 
    stride_check(self, onein)
  end
  local size = ceil(#self/onein) -- Always >= 1.
  return vecs_ct(self._p1, onein, size)
end
 
vecs_mt.stride = function(self, onein)
  if RCHECK then 
    stride_check(self, onein)
  end 
  local size = ceil(#self/onein) -- Always >= 1.
  return vecs_ct(self._p1, onein*self._p2, size)
end
 
--------------------------------------------------------------------------------
local function row_check(self, k)
  if not(1 <= k and k <= self._n) then 
    err("range", "out of range row: i="..k..", nrow="..self._n) 
  end
end
 
matv_mt.row = function(self, r)
  if RCHECK then 
    row_check(self, r)
  end
  return vecv_ct(self._p1 + self._p2*(r-1), self._m)
end
 
local function col_check(self, k)
  if not(1 <= k and k <= self._m) then 
    err("range", "out of range col: i="..k..", ncol="..self._m) 
  end
end
 
matv_mt.col = function(self, c)
  if RCHECK then 
    col_check(self, c)
  end
  return vecs_ct(self._p1 + c - 1, self._p2, self._n)
end
 
local function rows_check(self, f, l)
  if not (f <= l and 1 <= f and l <= self._n) then
    err("range",
      "out of range rows: first="..f..", last="..l..", nrow="..self._n)
  end
end
 
matv_mt.rows = function(self, f, l)
  l = l or self._n
  if RCHECK then 
    rows_check(self, f, l)
  end
  return matv_ct(self._p1 + (f - 1)*self._p2, self._p2, l - f + 1, self._m)
end
 
local function cols_check(self, f, l)
  if not (f <= l and 1 <= f and l <= self._m) then
    err("range",
      "out of range cols: first="..f..", last="..l..", ncol="..self._m)
  end
end
 
matv_mt.cols = function(self, f, l)
  l = l or self._m
  if RCHECK then 
    cols_check(self, f, l)
  end
  return matv_ct(self._p1 + f - 1, self._p2, self._n, l - f + 1)
end
 
local function square_check(self)
  if not (self._n == self._m) then
    err("range", "matrix not square: nrow="..self._n..", ncol="..self._m)
  end
end
 
local function diag_check(self, k)
  square_check(self)
  if not (1 - self._n <= k and k <= self._n - 1) then
    err("range", "out of range diagonal: i="..k..", n="..self._n)
  end
end
 
matv_mt.diag = function(self, k)
  k = k or 0
  if RCHECK then 
    diag_check(self, k)
  end
  local n = self._n
  if n >= 0 then
    return vecs_ct(self._p1 + k, n + 1, n - k)
  else
    local pk = -k
    return vecs_ct(self._p1 + pk*n, n + 1, n - pk)
  end
end
 
--------------------------------------------------------------------------------
local function copy_vec(self) 
  return vec(self) 
end
 
local function copy_mat(self) 
  return mat(self) 
end
 
local mstack = 1
local bstack, nstack
 
local function resizestack()
  bstack = cast(elptr_ct, C.realloc(bstack, elsize*mstack))
  if DEBUG and DEBUG.heap then print("buff", ptoint(bstack), mstack) end
  if bstack == nil then
    err("nomem", "cannot create a stack of mem size "..elsize*mstack)
  end
  nstack = mstack  
end
 
resizestack()
local pstack = bstack 
 
local function _stackcreate_vec(self, n)
  local p = pstack
  pstack = pstack + n
  mstack = max(mstack, pstack - bstack)
  if mstack <= nstack then -- Fast path.
    return vecv_ct(p, n)
  else
    if pstack - n == bstack then -- First el of stack, can resize stack.
      resizestack()
      p = bstack
      pstack = bstack + n
      return vecv_ct(p, n)
    else
      return vec(n)
    end
  end
end
 
local function _stackrelease_vec(self, n)
  pstack = pstack - n
end 
 
local function _stackcreate_mat(self, nr, nc)
  local p, n = pstack, nr*nc
  pstack = pstack + n
  mstack = max(mstack, pstack - bstack)
  if mstack <= nstack then -- Fast path.
    return matv_ct(p, nc, nr, nc)
  else
    if pstack - n == bstack then -- First el of stack, can resize stack.
      resizestack()
      p = bstack
      pstack = bstack + n
      return matv_ct(p, nc, nr, nc)
    else
      return mat(nr, nc)
    end
  end
end

local function _stackrelease_mat(self, nr, nc)
  pstack = pstack - nr*nc
end
 
local function _stackrelease_mat(self)
  pstack = pstack - self._n*self._m
end
 
local idnode_vecv = { -- Missing ct yet.
  res  = "v",
  tran = false,
  spec = "orig",
  data = { elptr_ct },
  env  = {},  
  expr = "$(v)",
  nidx = { function(i) return "self._p"..i.."[k-1]", 1 end },
  stac = { _stackcreate_vec, _stackrelease_vec },
}
 
local idnode_vecs = { -- Missing ct yet.
  res  = "v",
  tran = false,
  spec = "orig",
  data = { elptr_ct, int32_ct },
  env  = {},  
  expr = "$(v)",
  nidx = { function(i) 
    return "self._p"..i.."[self._p"..(i+1).."*(k-1)]", 2 
  end },
  stac = { _stackcreate_vec, _stackrelease_vec },
}
 
veco_mt = copytbl(vecv_mt)
local idnode_veco = copytbl(idnode_vecv)
 
for _,v in pairs{
  { vecv_mt, idnode_vecv },
  { vecs_mt, idnode_vecs },
  { veco_mt, idnode_veco },
} do
  local mt, id = v[1], v[2]
  mt._idnode = function()
    return id
  end
  setlazyops(mt, id)
  seteval(mt, id)
  setmethods(mt, id, methods_ntbe)
  setmethods(mt, id, methods_expr)
  setmethods(mt, id, methods_orig)
  setindex(mt, id)
  setnewindex(mt, id)
  mt.copy = copy_vec
  mt._stackcreate  = _stackcreate_vec
  mt._stackrelease = _stackrelease_vec
end
 
veco_mt.__gc = __gc
 
vecv_ct = metatype(algct(idnode_vecv), vecv_mt)
vecs_ct = metatype(algct(idnode_vecs), vecs_mt)
veco_ct = metatype(algct(idnode_veco), veco_mt)
 
local idnode_matv = { -- Missing ct yet, for mato as well.
  res  = "m",
  tran = false,
  spec = "orig",
  data = { elptr_ct, int32_ct },
  env  = { vecv_ct = vecv_ct, vecs_ct = vecs_ct },
  expr = "$(m)",
  nidx = matnidx,
  stac = { _stackcreate_mat, _stackrelease_mat },
}
 
mato_mt = copytbl(matv_mt)
local idnode_mato = copytbl(idnode_matv)
 
for _,v in pairs{
  { matv_mt, idnode_matv },
  { mato_mt, idnode_mato },
} do
  local mt, id = v[1], v[2]
  mt._idnode = function()
    return id
  end
  setlazyops(mt, id)
  seteval(mt, id)
  setmethods(mt, id, methods_ntbe)
  setmethods(mt, id, methods_expr)
  setmethods(mt, id, methods_orig)
  setindex(mt, id)
  mt.copy = copy_mat
  mt._stackcreate  = _stackcreate_mat
  mt._stackrelease = _stackrelease_mat
end
 
mato_mt.__gc = __gc
 
matv_ct = metatype(algct(idnode_matv), matv_mt)
mato_ct = metatype(algct(idnode_mato), mato_mt)
 
idnode_vecv.ct = vecv_ct
idnode_vecs.ct = vecs_ct
idnode_veco.ct = veco_ct
idnode_matv.ct = matv_ct
idnode_mato.ct = mato_ct
 
local function vec_alloc(n)
  chk(n >= 0, "error", "creating vector with #=",n)
  if n == 0 then
    return veco_ct(nil, 0)
  end
  local p = C.malloc(n*elsize)
  if p == nil then
    err("nomem", "cannot allocate memory for vector with #="..n)
  end
  if DEBUG and DEBUG.heap then print("avec", ptoint(p), n) end
  return veco_ct(p, n) 
end
 
local function vec_plain(n, c)
  local o = vec_alloc(n)
  local tc = type(c)
  if tc == "nil" then
    fill(o._p1, n*elsize)
  elseif tc == "number" or tc == "boolean" or istype(el_ct, c) then 
    o:fill(c)
  else
    o:gen(c)
  end
  return o
end
 
local function vec_aggregate(...)
  local a1 = ...
  local narg = select("#", ...)
  local n1 = #a1
  local n = n1
  for i=2,narg do
    local ai = select(i, ...)
    n = n + #ai
  end
  local o = vec_alloc(n)
  
  local f, l = 1, n1
  if f <= l then
    evalvec(o:sub(f, l), a1)
  end
  for i=2,narg do
    local ai = select(i, ...)
    f, l = l + 1, l + #ai
    if f <= l then
      evalvec(o:sub(f, l), ai)
    end
  end
  return o
end
 
vec = function(...)
  local n = ...
  if type(n) == "number" then
    return vec_plain(...)
  else
    return vec_aggregate(...)
  end
end
 
local function mat_alloc(nrow, ncol)
  chk(nrow >= 0, "range", "nrow=",nrow," not >=0")
  chk(ncol >= 0, "range", "ncol=",ncol," not >=0")
  if nrow == 0 or ncol == 0 then
    return mato_ct(nil, ncol, nrow, ncol)
  end
  local p = C.malloc(nrow*ncol*elsize)
  if p == nil then
    err("nomem", "cannot allocate memory for matrix with nrow="..nrow
      ..", ncol="..ncol)
  end
  if DEBUG and DEBUG.heap then print("amat", ptoint(p), nrow, ncol) end
  return mato_ct(p, ncol, nrow, ncol)
end
 
local function mat_plain(nrow, ncol, c)
  local o = mat_alloc(nrow, ncol)
  local tc = type(c)
  if tc == "nil" then
    fill(o._p1, nrow*ncol*elsize)
  elseif tc == "number" or tc == "boolean" or istype(el_ct, c) then 
    o:fill(c)
  else -- Function or callable. 
    o:gen(c)
  end
  return o
end
 
local function mat_dimensions(x)
  if type(x) == "table" then
    return #x, #x[1]
  else
    return x:nrow(), x:ncol()
  end
end
 
local function check_samencol(ncolx, ncoly)
  if not (ncolx == ncoly) then
    err("range", "x:ncol()="..ncolx.." ~= y:ncol()="..ncoly)
  end
end
 
local function mat_aggregate(...)
  local a1 = ...
  local narg = select("#", ...)
  local nrow1, ncol1 = mat_dimensions(a1)
  local nrow = nrow1
  for i=2,narg do
    local ai = select(i, ...)
    local nrowi, ncoli = mat_dimensions(ai)
    if RCHECK then
      check_samencol(ncol1, ncoli)
    end
    nrow = nrow + nrowi
  end
  local o = mat_alloc(nrow, ncol1)
  
  local f, l = 1, nrow1
  if f <= l then    
    evalmatnorcheck(o:rows(f, l), a1)
  end
  for i=2,narg do
    local ai = select(i, ...)
    local nrowi = mat_dimensions(ai)
    f, l = l + 1, l + nrowi
    if f <= l then
      evalmatnorcheck(o:rows(f, l), ai)
    end
  end
  return o
end
 
mat = function(...)
  local nrow = ...
  if type(nrow) == "number" then
    return mat_plain(...)
  else
    return mat_aggregate(...)
  end
end
 
--------------------------------------------------------------------------------
return {
  vec = vec,
  mat = mat,
  vec_ct = veco_ct,
  mat_ct = mato_ct,
}
 
end, "strong", tonumber)
 
local algdouble = algtypeof(typeof("double"))
 
local function algmax(x)
  return x:max()
end
local function algmin(x)
  return x:min()
end
local function algsum(x)
  return x:sum()
end
local function algavg(x)
  return x:avg()
end
local function algprod(x)
  return x:prod()
end
 
local algmath = {}
for k,v in pairs(math) do
  algmath[k] = unaop(v)
end
 
local function slicer(...)
  local r = {}
  local f, l = 1, 0
  for i=1,select("#", ...) do
    local el = select(i, ...)
    if type(el) == "table" then
      f, l = el[1], el[2]
    else
      f, l = l + 1, l + el
    end
    if f <= l then
      r[i] = "x:sub("..f..","..l..")"
    else
      r[i] = "nil"
    end
  end
  r = concat(r, ",")
  return compile("return function(x) return "..r.." end", "vecslicer")
end
 
return {
  isalg  = isalg,
  typeof = algtypeof,
  toelwf = unaop,
  math   = algmath,
  
  vec    = algdouble.vec,
  mat    = algdouble.mat,
  vec_ct = algdouble.vec_ct,
  mat_ct = algdouble.mat_ct,
  
  min    = algmin,
  max    = algmax,
  sum    = algsum,
  avg    = algavg,
  prod   = algprod,
  
  slicer = slicer,
}
