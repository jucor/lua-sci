package = 'sci'
version = 'beta-3'

source = {
    url = 'git+file://git@github.com:jucor/lua-sci.git',
    branch = '1.0-beta3'
}

description = {
    summary = 'A library for general purpose scientific computing, part of SciLua',
    homepage = 'http://scilua.org/'
}

dependencies = {'xsys'}
build = {
    type = 'none',
    install = {
        lua = {
            ['sci._expr'] = '_expr.lua',
            ['sci._rngcore'] = '_rngcore.lua',
            ['sci.alg.config'] = 'alg/config.lua',
            ['sci.alg'] = 'alg.lua',
            ['sci.dist._beta'] = 'dist/_beta.lua',
            ['sci.dist._exponential'] = 'dist/_exponential.lua',
            ['sci.dist._gamma'] = 'dist/_gamma.lua',
            ['sci.dist._lognormal'] = 'dist/_lognormal.lua',
            ['sci.dist._normal'] = 'dist/_normal.lua',
            ['sci.dist._shiftscale'] = 'dist/_shiftscale.lua',
            ['sci.dist._student'] = 'dist/_student.lua',
            ['sci.dist._uniform'] = 'dist/_uniform.lua',
            ['sci.dist'] = 'dist.lua',
            ['sci.fmax'] = 'fmax.lua',
            ['sci.fmin._diffevol'] = 'fmin/_diffevol.lua',
            ['sci.fmin'] = 'fmin.lua',
            ['sci.math'] = 'math.lua',
            ['sci.prng._marsaglia'] = 'prng/_marsaglia.lua',
            ['sci.prng._mrg'] = 'prng/_mrg.lua',
            ['sci.prng'] = 'prng.lua',
            ['sci.qrng._new-joe-kuo-6-21201'] = 'qrng/_new-joe-kuo-6-21201.lua',
            ['sci.qrng._sobol'] = 'qrng/_sobol.lua',
            ['sci.qrng'] = 'qrng.lua',
            ['sci.quad._dblexp'] = 'quad/_dblexp.lua',
            ['sci.quad._dblexp_precomputed'] = 'quad/_dblexp_precomputed.lua',
            ['sci.quad'] = 'quad.lua',
            ['sci.root._newton'] = 'root/_newton.lua',
            ['sci.root._ridders'] = 'root/_ridders.lua',
            ['sci.root'] = 'root.lua',
            ['sci.stat'] = 'stat.lua',
            ['sci.sym'] = 'sym.lua'
        }
    }
}
