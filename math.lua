--------------------------------------------------------------------------------
-- Special math functions module.
--
-- Copyright (C) 2011-2013 Stefano Peluchetti. All rights reserved.
--
-- Features, documention and more: http://www.scilua.org .
--
-- This file is part of the SciLua library, which is released under the MIT 
-- license: full text in file LICENSE.TXT in the library's root folder.
--------------------------------------------------------------------------------

local ffi  = require "ffi"
local xsys = require "xsys"
local bit  = require "bit"

local sqrt, exp, log, sin, floor, min, max, abs, ceil, floor = xsys.from(math, 
     "sqrt, exp, log, sin, floor, min, max, abs, ceil, floor")
local m_pi, m_e = math.pi, exp(1)

-- Utility functions -----------------------------------------------------------
-- TODO: Fix this one.
-- Round number so that it has ndigits after the zero.
local function round(num, ndigits)
  local tnum
  local rnum = num*10^ndigits
  if rnum < 0 then 
    tnum =  math.ceil(rnum < 0 and rnum - 0.5 or rnum + 0.5)
  else
    tnum = math.floor(rnum < 0 and rnum - 0.5 or rnum + 0.5)
  end
  return tnum/10^ndigits
end

local function step(x) -- 1 of x >= 0, 0 otherwise.
  return min(1, max(0, floor(x) + 1))
end

local function sign(x)
  return -1 + step(x)*2
end

local function isnan(x)
  return x ~= x
end

-- All of the below returns false if it's nan as expected.
local function isfinite(x)
  return abs(x) < math.huge
end

local function isinteger(x)
  return x == floor(x)
end

local function iseven(x)
  return x % 2 == 0
end

local function isodd(x)
  return x % 2 == 1
end

-- Phi function ----------------------------------------------------------------
-- From Marsaglia, "Evaluating the Normal Distribution"
-- http://www.jstatsoft.org/v11/a05/paper
-- around 15 digits of absolute precision.
local function phi(x)
  -- Ensure 0 <= phi(x) <= 1 :
  if x <= -8 then
    return 0
  elseif x >= 8 then
    return 1
  else
  
  local s, b, q = x, x, x^2
  for i=3,math.huge,2 do
    b = b*q/i
    local t = s
    s = t + b
    if s == t then break end
  end
  return 0.5 + s*exp(-0.5*q - 0.91893853320467274178)
  end
end

-- Iphi functions --------------------------------------------------------------

-- Inverse cdf for sampling based on Peter John Acklam research, see:
-- http://home.online.no/~pjacklam/notes/invnorm/ .
-- Maximum relative error of 1.15E-9 and machine accuracy with refinement.
-- In iphifast domain must be (0, 1) extremes excluded.
local iphifast, iphi

do 

  local a = ffi.new("double[7]", { 0,
  -3.969683028665376e+01,
  2.209460984245205e+02,
  -2.759285104469687e+02,
  1.383577518672690e+02,
  -3.066479806614716e+01,
  2.506628277459239e+00 })

  local b = ffi.new("double[6]", { 0,
  -5.447609879822406e+01,
  1.615858368580409e+02,
  -1.556989798598866e+02,
  6.680131188771972e+01,
  -1.328068155288572e+01 })

  local c = ffi.new("double[7]", { 0,
  -7.784894002430293e-03,
  -3.223964580411365e-01,
  -2.400758277161838e+00,
  -2.549732539343734e+00,
  4.374664141464968e+00,
  2.938163982698783e+00 })

  local d = ffi.new("double[5]", { 0,
  7.784695709041462e-03,
  3.224671290700398e-01,
  2.445134137142996e+00,
  3.754408661907416e+00 })

  -- PERF: just two branches, central with high prob.
  iphifast = function(p)
    --Rational approximation for central region:
    if abs(p - 0.5) < 0.47575 then -- 95.14% of cases if p - U(0, 1).
      local q = p - 0.5
      local r = q^2
      return (((((a[1]*r+a[2])*r+a[3])*r+a[4])*r+a[5])*r+a[6])*q /
             (((((b[1]*r+b[2])*r+b[3])*r+b[4])*r+b[5])*r+1)
    --Rational approximation for the two ends:
    else
      local iu = ceil(p - 0.97575)	    -- 1 if p > 0.97575 (upper).
      local z = (1 - iu)*p + iu*(1 - p) -- p if lower, (1 - p) if upper.
      local sign = 1 - 2*iu	            -- 1 if lower, -1	if upper.
      local q = sqrt(-2*log(z))
      return sign*(((((c[1]*q+c[2])*q+c[3])*q+c[4])*q+c[5])*q+c[6]) /
                   ((((d[1]*q+d[2])*q+d[3])*q+d[4])*q+1)
    end
  end
  
  iphi = function(p) 
    if p <= 0 then
      return -1/0
    elseif p >=1 then
      return 1/0
    else
      local x = iphifast(p)
      local e = phi(x) - p
      local u = e*sqrt(2*m_pi)*exp(x^2/2)
      return x - u/(1 + x*u/2)
    end
   end
  
end

-- Gamma function --------------------------------------------------------------
local gamma, logabsgamma

do

  -- r(10).
  local gamma_r10 = 10.900511

  -- dk[0], ..., dk[10].
  local gamma_dk = ffi.new("double[11]", 
    2.48574089138753565546e-5,
    1.05142378581721974210,
    -3.45687097222016235469,
    4.51227709466894823700,
    -2.98285225323576655721,
    1.05639711577126713077,
    -1.95428773191645869583e-1,
    1.70970543404441224307e-2,
    -5.71926117404305781283e-4,
    4.63399473359905636708e-6,
    -2.71994908488607703910e-9
  )

  local gamma_c = 2*sqrt(m_e/m_pi)

  -- Lanczos approximation, see:
  -- Pugh[2004]: AN ANALYSIS OF THE LANCZOS GAMMA APPROXIMATION
  -- http://bh0.physics.ubc.ca/People/matt/Doc/ThesesOthers/Phd/pugh.pdf
  -- pag 116 for optimal formula and coefficients. Theoretical accuracy of 
  -- 16 digits is likely in practice to be around 14.
  -- Domain: R except 0 and negative integers.
  gamma = function(z)
    -- Reflection formula to handle negative z plane.
    -- Better to branch at z < 0 as some probabilistic use cases only consider the
    -- case z >= 0.
    if z < 0 then 
      return m_pi/(sin(m_pi*z)*gamma(1 - z)) 
    end  
    local sum = gamma_dk[0]
    -- for i=1,10 do 
      -- sum = sum + gamma_dk[i]/(z + i - 1) 
    -- end
    sum = sum + gamma_dk[1]/(z + 0)
    sum = sum + gamma_dk[2]/(z + 1) 
    sum = sum + gamma_dk[3]/(z + 2) 
    sum = sum + gamma_dk[4]/(z + 3) 
    sum = sum + gamma_dk[5]/(z + 4) 
    sum = sum + gamma_dk[6]/(z + 5) 
    sum = sum + gamma_dk[7]/(z + 6) 
    sum = sum + gamma_dk[8]/(z + 7) 
    sum = sum + gamma_dk[9]/(z + 8) 
    sum = sum + gamma_dk[10]/(z + 9)  
    return gamma_c*((z  + gamma_r10 - 0.5)/m_e)^(z - 0.5)*sum
  end

  -- Returns log(abs(gamma(z))).
  -- Domain: R except 0 and negative integers.
  logabsgamma = function(z)
    -- Reflection formula to handle negative real plane. Only sin can be negative.
    -- Better to branch at z < 0 as some probabilistic use cases only consider the
    -- case z >= 0.
    if z < 0 then 
      return log(m_pi) - log(abs(sin(m_pi*z))) - logabsgamma(1 - z) 
    end  
    local sum = gamma_dk[0]
    -- for i=1,10 do 
      -- sum = sum + gamma_dk[i]/(z + i - 1) 
    -- end
    sum = sum + gamma_dk[1]/(z + 0)
    sum = sum + gamma_dk[2]/(z + 1) 
    sum = sum + gamma_dk[3]/(z + 2) 
    sum = sum + gamma_dk[4]/(z + 3) 
    sum = sum + gamma_dk[5]/(z + 4) 
    sum = sum + gamma_dk[6]/(z + 5) 
    sum = sum + gamma_dk[7]/(z + 6) 
    sum = sum + gamma_dk[8]/(z + 7) 
    sum = sum + gamma_dk[9]/(z + 8) 
    sum = sum + gamma_dk[10]/(z + 9) 
    -- For z >= 0 gamma function is positive, no abs() required.
    return log(gamma_c) + (z - 0.5)*log(z  + gamma_r10 - 0.5) 
      - (z - 0.5) + log(sum)
  end

end

-- Beta function ---------------------------------------------------------------
-- Domain: a > 0 and b > 0.
local function logbeta(a, b)
  if a <= 0 or b <= 0 then return 0/0 end
  return logabsgamma(a) + logabsgamma(b) - logabsgamma(a + b)
end

-- Domain: a > 0 and b > 0.
local function beta(a, b)
  return exp(logbeta(a, b))
end

--------------------------------------------------------------------------------

local M = {
  round       = round,
  step        = step,
  sign        = sign,
  isnan       = isnan,
  isfinite    = isfinite, 
  isinteger   = isinteger,
  iseven      = iseven,
  isodd       = isodd,
  phi         = phi,
  iphi        = iphi,
  _iphifast   = iphifast,
  gamma       = gamma,
  logabsgamma = logabsgamma,
  logbeta     = logbeta,
  beta        = beta,
}

xsys.import(M, math)

return M