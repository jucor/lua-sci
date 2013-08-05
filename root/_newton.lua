--------------------------------------------------------------------------------
-- Newton-type root finding module.
--
-- Copyright (C) 2011-2013 Stefano Peluchetti. All rights reserved.
--
-- Features, documention and more: http://www.scilua.org .
--
-- This file is part of the SciLua library, which is released under the MIT 
-- license: full text in file LICENSE.TXT in the library's root folder.
--------------------------------------------------------------------------------

local xsys = require "xsys"
local math = require "sci.math"

local err, chk = xsys.handlers("sci.root")

local function rebracket(x1, y1, xl, xu, yl, yu)
  if yl*y1 <= 0 then
    return xl, x1, yl, y1
  else
    return x1, xu, y1, yu
  end
end

local function newton(f, xl, xu, stop, f1)
  chk(xl < xu, "constraint", "xlower:",xl," not < xupper:",xu)
  local yl, yu = f(xl), f(xu)
  chk(yl*yu <= 0, "constraint", "root not bracketed by f(xlower):",yl,
    ", f(xupper):",yu)
  local x0 = xl + 0.5*(xu - xl) -- Avoid xm > xl or xm < xu.
  while true do
    local y0, f10 = f(x0), f1(x0)
    local x1 = x0 - y0/f10
    chk(x1 ~= x0, "error", "x1 == x0: f(x0)=",y0,", f1(x0)=",f10)
    chk(xl <= x1 and x1 <= xu, "error", "root estimate outside bracket, xl=",
      xl," xu=",xu," x1=",x1)
    local y1 = f(x1)
    if stop(x1, y1, xl, xu, yl, yu) then
      return x1, y1, xl, xu, yl, yu
    end
    xl, xu, yl, yu = rebracket(x1, y1, xl, xu, yl, yu)
    x0 = x1
  end
end

local function halley(f, xl, xu, stop, f1, f2)
  chk(xl < xu, "constraint", "xlower:",xl," not < xupper:",xu)
  local yl, yu = f(xl), f(xu)
  chk(yl*yu <= 0, "constraint", "root not bracketed by f(xlower):",yl,
    ", f(xupper):",yu)
  local x0 = xl + 0.5*(xu - xl) -- Avoid xm > xl or xm < xu.
  while true do
    local y0, f10, f20 = f(x0), f1(x0), f2(x0)
    local x1 = x0 - 2*y0*f10/(2*f10^2 - y0*f20)
    chk(x1 ~= x0, "error", "x1 == x0: f(x0)=",y0,", f1(x0)=",f10,", f2(x0)=",
      f20)
    chk(xl <= x1 and x1 <= xu, "error", "root estimate outside bracket, xl=",
      xl," xu=",xu," x1=",x1)
    local y1 = f(x1)
    if stop(x1, y1, xl, xu, yl, yu) then
      return x1, y1, xl, xu, yl, yu
    end
    xl, xu, yl, yu = rebracket(x1, y1, xl, xu, yl, yu)
    x0 = x1
  end
end

return { 
  newton = newton,
  halley = halley,
}