--------------------------------------------------------------------------------
-- Normal statistical distribution.
--
-- Copyright (C) 2011-2013 Stefano Peluchetti. All rights reserved.
--
-- Features, documention and more: http://www.scilua.org .
--
-- This file is part of the SciLua library, which is released under the MIT 
-- license: full text in file LICENSE.TXT in the library's root folder.
--------------------------------------------------------------------------------

local xsys = require "xsys"
local ffi  = require "ffi"
local math = require "sci.math"

local M = {}

local err, chk = xsys.handlers("sci.dist")
local exp, log, sqrt, pi, sin, cos, iseven, abs, ceil = xsys.from(math,
     "exp, log, sqrt, pi, sin, cos, iseven, abs, ceil")
     
-- Inverse cdf for sampling based on Peter John Acklam research, see:
-- http://home.online.no/~pjacklam/notes/invnorm/ .
-- Maximum relative error of 1.15E-9, fine for generation of rv.
--
-- The following paper has some considerations on this topic:
-- http://epub.wu.ac.at/664/1/document.pdf .
--
-- Moreover, the following procedure has been employed as empirical validation 
-- of the sampling procedure: for a given prng the samples returned from a 
-- normal(0, 1) are converted back to uniform(0, 1) via the gsl cdf for the
-- normal(0, 1) which offers machine accuracy implementation. These numbers are
-- used as input to the small, normal, and big crush batteries from TestU01. 
-- All test passed aside from the followings suspect p-values. Also reported the
-- p-values obtained by repeating the suspect tests:
--
-- lfib4:
-- BIG: swalk_RandomWalkl test:
-- N = 1, n = 100000000, r = 0, s = 5, L0 = 50, L1 = 50
-- J: p-value of test : 6.8e-04 *****
-- Repeating the test yields p-values: 0.21, 0.51, 0.49, 0.07, 0.11 [OK]
--
-- mrg32k3a:
-- NORM: smarsa_MatrixRank test:
-- N = 1, n = 1000000, r = 0, s = 30, L = 60, k = 60
-- p-value of test : 9.4e-04 *****
-- Repeating the test yields p-values: 0.70, 0.24, 0.12, 0.40, 0.06 [OK]
--
-- The prng mrg32k3a has 2^53 accuracy and hence is of particular relevance
-- for the tails.
local icdf = math._iphifast
      
local norm_mt, norm_ct = {}
norm_mt.__index = norm_mt

function norm_mt:range()
  return -math.huge, math.huge
end

function norm_mt:pdf(x)
  local mu, sigma = self._mu, self._sigma
  return exp(-0.5*((x - mu)/sigma)^2) / (sqrt(2*pi)*sigma)
end

function norm_mt:logpdf(x)
  local mu, sigma = self._mu, self._sigma
  return -0.5*((x - mu)/sigma)^2 - 0.5*log(2*pi) - log(sigma)
end

function norm_mt:mean()
  return self._mu
end

function norm_mt:variance()
  return self._sigma^2
end

function norm_mt:absmoment(mm)
  if self._mu == 0 and self._sigma == 1 and mm == 1 then
    return sqrt(pi/2)
  else
    error("NYI")
  end
end

-- TODO: I think we can for sample(x) actually.
-- -- Box-muller cannot be used with our qrng API:
-- local function box_muller(self, u1, u2)
	-- -- Non-rejection sampler.
	-- local mu, sigma = self._mu, self._sigma
	-- local m  = sqrt(-2*log(u1))
	-- local r1 = m*cos(2*pi*u2) -- Gaussian(0,1).	
	-- local r2 = m*sin(2*pi*u2) -- Gaussian(0,1).
	-- return mu + sigma*r1, mu + sigma*r2
-- end

-- TODO: investigate ziggurat.
function norm_mt:sample(rng)
  return icdf(rng:sample())*self._sigma + self._mu
end

function norm_mt:copy()
  return norm_ct(self)
end

norm_ct = ffi.metatype("struct {double _mu; double _sigma;}", norm_mt)

M._normal_mt = norm_mt

function M.normal(mu, sigma)
  mu    = mu    or 0
  sigma = sigma or 1
  chk(sigma > 0, "constraint", "sigma must be positive, sigma=", sigma)
  return norm_ct(mu, sigma)
end

return M