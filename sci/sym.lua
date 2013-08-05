
-- TODO: maxlen config.
local ffi  = require "ffi"
local xsys = require "xsys"
local math = require "sci.math"

local err, chk = xsys.handlers("sci.sym")
local split, trim = xsys.string.split, xsys.string.trim

local function isnum(a)
  return type(a) == "number"
end

-- Can I fold numerical parts of a and b when arguments to operator op?
local function isfoldable(op, a, b)
  local folda = isnum(a) or (a[0] == op and isnum(a[1]))
  local foldb = isnum(b) or (b[0] == op and isnum(b[1]))
  return folda and foldb
end

local arithop = { ["-"] = true, ["+"] = true, ["*"] = true, ["/"] = true,
                  ["^"] = true }
                  
local function numfirst(a, b) -- Swap a, b if b is number.
  if isnum(b) then
    return b, a
  else
    return a, b
  end
end

-- Number alway first, expressions order based on string length or if same
-- length on the lexicographical order.
local function symlt(a, b)
  if isnum(a) then
    return true
  elseif isnum(b) then
    return false
  else
    if #a.re < #b.re then
      return true
    else
      return a.re < b.re
    end
  end
end

-- Expression and number never equal, expressions equal iff same string.
local function symeq(a, b)
  if type(a) == "number" or type(b) == "number" then
    return false
  else
    return a.re == b.re
  end
end

local expr_mt, expr_ct

local function expr(op, ...) -- Composite expressions, i.e. not variables.
  local re
  if arithop[op] then
    local a, b = ...
    if not b then
      re = "("..op..tostring(a)..")" -- Unary op.
    else
      re = "("..tostring(a)..op..tostring(b)..")" -- Binary op.
    end
  else
    local arg = { ... }
    for i=1,#arg do
      arg[i] = tostring(arg[i])
    end
    re = op.."("..table.concat(arg, ",")..")" -- Functions.
  end
  return expr_ct({ re = re, [0] = op, ... })
end

local function var(s) -- Variables,
  local o = split(s, ",")
  for i=1,#o do
    local si = trim(o[i])
    o[i] = expr_ct({ si, re = si })
  end
  return unpack(o)
end

-- Simplify only simple cases for results: 0, +-1, +-a, +-b.
-- When constructing a new node via operator:
-- * Order so number is first (only commutative binop)
-- * Simplify
-- * Fold constants (only commutative binop)
-- * Return expr (ordered by symlt(a, b) for commutative binop, better hash)
-- Tree is never rewritten.

local function unm(a)
  if a[0] == "-" and #a == 1 then
    return a[1] -- -(-a) == a.
  end
    return expr("-", a)
end

local function add(a, b)
  a, b = numfirst(a, b)
  if a == 0 then
    return b -- 0 + b == b.
  end
  if isfoldable("+", a, b) then
    a = isnum(a) and { a, 0 } or a
    return (a[1] + b[1]) + (a[2] + b[2])
  end
  return symlt(a, b) and expr("+", a, b) or expr("+", b, a)
end

local function mul(a, b)
  a, b = numfirst(a, b)
  if a == 0 then
    return 0 -- 0 * b = 0.
  elseif a == 1 then
    return b -- 1 * b == b.
  elseif a == -1 then
    return -b -- -1 * b == -b.
  end
  if isfoldable("*", a, b) then
    a = isnum(a) and { a, 1 } or a
    return (a[1] * b[1]) * (a[2] * b[2])
  end
  return symlt(a, b) and expr("*", a, b) or expr("*", b, a)
end

local function sub(a, b)
  if a == 0 then
    return -b -- 0 - b == -b.
  elseif b == 0 then
    return a -- a - 0 == a.
  elseif symeq(a, b) then
    return 0 -- a - a == 0.
  end
    return expr("-", a, b)
end

local function div(a, b)
  if a == 0 then
    return 0 -- 0 / b == 0.
  elseif symeq(a, b) then
    return 1 -- b / b == 1.
  elseif isnum(b) then
    return (1/b) * a -- a / b == (1/b) * a.
  -- elseif b == 1 then
  -- return a
  -- elseif b == -1 then
  -- return -a
  end
  return expr("/", a, b)
end

local function pow(a, b)
  if a == 0 then
    return 0 -- 0 ^ b == 0.
  elseif a == 1 then
    return 1 -- 1 ^ b == 1.
  elseif b == 0 then
    return 1 -- a ^ 0 == 1.
  elseif b == 1 then
    return a -- a ^ 1 == a.
  end
  return expr("^", a, b)
end

expr_mt = {
  __unm = unm,
  __add = add,
  __mul = mul,
  __sub = sub,
  __div = div,
  __pow = pow,
  __tostring = function(self)
    return self.re
  end
}
expr_mt.__index = expr_mt

-- Check argument is a valid identifier and not a key in "sci.math" module.
local function checkvar(s)
  chk(not math[s], "parse", s," is already a math function name")
  local ok = pcall(xsys.compile, "local "..s)
  if not ok then
    err("parse", s.." is not a valid variable name")
  end
end

local expr_cache = setmetatable({}, { __mode = "v" })

-- Constructor for any expression: variables and composite expressions.
expr_ct = function(t)
  if expr_cache[t.re] then
    return expr_cache[t.re]
  else
    if not t[0] then -- If it's a variable.
      checkvar(t.re)
    end
    setmetatable(t, expr_mt)
    expr_cache[t.re] = t
    return t
  end
end

-- Need bounding parenthesis when argument to "*" op, for latex.
local function needspar(e)
  return type(e) ~= "number" and (e[0] == "+" or (e[0] == "-" and #e == 2))
end

local curly = { -- The function uses {} instad of () syntax, for latex.
  sqrt = true,
}

-- TODO: Add greek letters substitutions.
local replace = { -- Latex substitutions for "sci.math" module.
  phi  = "Phi",
  iphi = "Phi^{-1}",
}

local function tolatex(e)
  if type(e) == "number" then -- Number.
    return tostring(e)
  end
  if not e[0] then -- Variable.
    assert(#e == 1)
    return e[1]
  end
  -- Operators:
  local op = replace[e[0]] and replace[e[0]] or e[0]
  if op == "-" and #e == 1 then -- Unary op.
    return "-{"..tolatex(e[1]).."}"
  elseif op == "*" then -- Binary ops.
    assert(#e == 2)
    local lhs = needspar(e[1]) and "("..tolatex(e[1])..")"
                                or "{"..tolatex(e[1]).."}"
    local rhs = needspar(e[2]) and "("..tolatex(e[2])..")"
                                or "{"..tolatex(e[2]).."}"
    return lhs.." "..rhs
  elseif op == "/" then
    assert(#e == 2)
    return "\\frac{"..tolatex(e[1]).."}{"..tolatex(e[2]).."}"
  elseif op == "^" or op == "+" or op == "-" then
    assert(#e == 2)
    return "{"..tolatex(e[1]).."}"..op.."{"..tolatex(e[2]).."}"
  end
  -- Functions.
  local arg = {}
  for i=1,#e do
    arg[i] = tolatex(e[i])
  end
  arg = table.concat(arg, ",")
  if curly[op] then
  return "\\"..op.."{"..arg.."}"
  else
  return "\\"..op.."("..arg..")"
  end
end

local function tofunction(e, ...)
  local arg = { ... }
  xsys.table.apply(arg, tostring)
  arg = table.concat(arg, ",")
  return xsys.compile("return function("..arg..") return "
                    ..tostring(e).." end", "expr", math)
end

local finv = {
  log  = "exp",
  exp  = "log",
  sin  = "sin",
  cos  = "acos",
  tan  = "atan",
  asin = "sin",
  acos = "cos",
  atan = "tan",
  phi  = "iphi",
  iphi = "phi",
}

-- TODO: support more than 1 arg for non-numeric arguments.
local function fcoretoexpr(f, k, finv)
  return function(x)
    if isnum(x)
      then return f(x)
    else
      local isinv = finv and x[0] and x[0] == finv
      return isinv and x[1] or expr(k, x)
    end
  end
end

local M = {}
for k,v in pairs(math) do
  if type(v) == "function" then
    M[k] = fcoretoexpr(v, k, finv[k])
  else
    M[k] = v
  end
end

-- Core partial derivatives.
-- TODO: ceil, floor, abs, min, max, fmod, ldexp, frexp, deg, rad ,atan2, log10.
local partder 
partder = {
  ["-"] = function(e, i)
    if #e == 1 then
      return -1
    else
      return i == 1 and 1 or -1
    end
  end,
  ["+"] = function(e, i)
    return 1
  end,
  ["*"] = function(e, i)
    return i == 1 and e[2] or e[1]
  end,
  ["/"] = function(e, i)
    return i == 1 and 1/e[2] or -e[1]/(e[2]*e[2])
  end,
  ["^"] = function(e, i)
    return i == 1 and e[2]*e[1]^(e[2] - 1) or e[1]^e[2]*M.log(e[1])
  end,
  sqrt = function(e, i) return 1/(2*M.sqrt(e[1])) end,
  exp  = function(e, i) return M.exp(e[1]) end,
  log  = function(e, i) return 1/e[1] end,
  sin  = function(e, i) return M.cos(e[1]) end,
  asin = function(e, i) return 1/M.sqrt(1 - e[1]^2) end,
  sinh = function(e, i) return M.cosh(e[1]) end,
  cos  = function(e, i) return -M.sin(e[1]) end,
  acos = function(e, i) return -1/M.sqrt(1 - e[1]^2) end,
  cosh = function(e, i) return M.sinh(e[1]) end,
  tan  = function(e, i) return 1/M.cos(e[1])^2 end,
  atan = function(e, i) return 1/(e[1]^2 + 1) end,
  tanh = function(e, i) return 1/M.cosh(e[1])^2 end,
  pow  = function(e, i) return partder["^"](e, i) end,
  
  phi  = function(e, i) return 1/math.sqrt(2*math.pi)*M.exp(-e[1]^2/2) end,
  iphi = function(e, i) return 1/partder.phi(M.iphi(e[1])) end,
  
  step = function(e, i) return 0 end, 
  sign = function(e, i) return 0 end,
  abs  = function(e, i) return M.sign(e[1]) end,
}

local function diff(e, v)
  if isnum(e) then
    return 0
  elseif not e[0] then
    return e[1] == v[1] and 1 or 0
  else
    local o = 0
    for i=1,#e do
      o = o + partder[e[0]](e, i)*diff(e[i], v)
    end
    return o
  end
end

xsys.import(M, { 
  var        = var, 
  diff       = diff, 
  tofunction = tofunction,
  tolatex    = tolatex,
})

return M