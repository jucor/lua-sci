--------------------------------------------------------------------------------
-- Rng core module.
--
-- Copyright (C) 2011-2013 Stefano Peluchetti. All rights reserved.
--
-- Features, documention and more: http://www.scilua.org .
--
-- This file is part of the SciLua library, which is released under the MIT 
-- license: full text in file LICENSE.TXT in the library's root folder.
--------------------------------------------------------------------------------

local rnggen = setmetatable({}, { 
  __mode  = "k",
  __index = function(self, k)
    local f = function() 
      return k:_sample()
    end
    self[k] = f
    return f
  end,
})

local function sample(self, x)
  if not x then
    return self:_sample()
  else
    x:gen(rnggen[self])
  end
end

return {
  sample = sample,
}