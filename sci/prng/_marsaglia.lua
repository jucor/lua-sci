--------------------------------------------------------------------------------
-- George Marsaglia pseudo rngs module.
--
-- Copyright (C) 2011-2013 Stefano Peluchetti. All rights reserved.
--
-- Features, documention and more: http://www.scilua.org .
--
-- Credit: George Marsaglia Newsgroups posted code:
-- http://www.math.niu.edu/~rusin/known-math/99/RNG .
--
-- This file is part of the SciLua library, which is released under the MIT 
-- license: full text in file LICENSE.TXT in the library's root folder.
--------------------------------------------------------------------------------

-- These specific implementations have been tested against small, normal and big
-- crush batteries of TestU01, the following suspect p-value has been observed:
--
-- kiss99:
-- BIG crush: smarsa_MatrixRank test:
-- N = 10, n = 1000000, r = 0, s = 5, L = 30, k = 30
-- Test on the sum of all N observations: p-value of test : 7.6e-04 *****
-- Repeating the test yields p-values: 0.58, 0.21, 0.70, 0.08, 0.11 [OK]

local xsys = require "xsys"
local ffi  = require "ffi"
local bit  = require "bit"
local core = require "sci._rngcore"

local tobit, band, bxor, lshift, rshift =  xsys.from(bit, [[
      tobit, band, bxor, lshift, rshift ]])

-- TODO: improve and move to xsys.
local function sarg(...)
  return "("..table.concat({ ... }, ",")..")"
end

-- Guarantee range (0, 1) extremes excluded.
local function sample_double(self)
  local b = self:_bitsample()
  return (bxor(b, 0x80000000) + (0x80000000+1)) * (1/(2^32+1))
end

local kiss99_mt, kiss99_ct = {}
kiss99_mt.__index = kiss99_mt

function kiss99_mt:_bitsample()
  local r = self
  r._s1 = tobit(tobit(69069*r._s1) + 1234567)   
  local b = bxor(r._s2, lshift(r._s2, 17))
  b = bxor(b, rshift(b, 13))
  r._s2 = bxor(b, lshift(b, 5))   
  r._s3 = tobit(tobit(36969*band(r._s3, 0xffff)) + rshift(r._s3, 16))
  r._s4 = tobit(tobit(18000*band(r._s4, 0xffff)) + rshift(r._s4, 16))
  b = tobit(lshift(r._s3, 16) + r._s4)
  return tobit(r._s2 + bxor(r._s1, b))
end

kiss99_mt._sample = sample_double
kiss99_mt.sample = core.sample

function kiss99_mt:__tostring()
  return "sci.prng.kiss99_ct"
       ..sarg(self._s1 , self._s2 ,self._s3 , self._s4)
end

function kiss99_mt:copy()
  return kiss99_ct(self._s1, self._s2, self._s3, self._s4)
end

kiss99_ct = ffi.metatype("struct { int32_t _s1, _s2, _s3, _s4; }", kiss99_mt)

local function kiss99()
  -- Follow Marsaglia initialization.
  return kiss99_ct(tobit(12345), tobit(34221), tobit(12345), tobit(65435))
end

local lfib4_mt, lfib4_ct = {}
lfib4_mt.__index = lfib4_mt

function lfib4_mt:_bitsample()
  local r = self
  r._i = band(r._i + 1, 255)
  r._s[r._i] = tobit(tobit(r._s[r._i] + r._s[band(r._i+58, 255)]) 
    + tobit(r._s[band(r._i+119, 255)] + r._s[band(r._i+178, 255)]))
  return r._s[r._i]
end

lfib4_mt._sample = sample_double
lfib4_mt.sample = core.sample

function lfib4_mt:__tostring()
  local t = {}
  for i=1,256 do t[i] = self._s[i-1] end
  t = "{"..table.concat(t, ",").."}"
  return "sci.prng.lfib4_ct"
       ..sarg(t, self._i)
end

function lfib4_mt:copy()
  return lfib4_ct(self._s, self._i)
end

lfib4_ct = ffi.metatype("struct { int32_t _s[256]; int32_t _i; } ", lfib4_mt)

local function lfib4()
  -- Follow Marsaglia initialization.
  local obj = lfib4_ct() -- Zero filled => _i is 0.
  local r = kiss99()
  for i=0,255 do obj._s[i] = r:_bitsample() end
  return obj
end

return {
  kiss99    = kiss99,
  kiss99_ct = kiss99_ct,
  lfib4     = lfib4,
  lfib4_ct  = lfib4_ct,
}