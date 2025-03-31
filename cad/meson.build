project('cad', 'cpp',
  default_options: ['cpp_std=c++17',
    'warning_level=3',
    ])

gmp_dep = dependency('gmp')
flint_dep = dependency('flint')

executable('cad',
  'src/main.cpp', 'src/ctx.cpp', 'src/mpoly.cpp',
  dependencies: [gmp_dep, flint_dep],
  include_directories: include_directories('include')
)

