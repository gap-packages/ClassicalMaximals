[![CI](https://github.com/gap-packages/ClassicalMaximals/workflows/CI/badge.svg?branch=main)](https://github.com/gap-packages/ClassicalMaximals/actions?query=workflow%3ACI+branch%3Amain)
[![Code Coverage](https://codecov.io/github/gap-packages/ClassicalMaximals/coverage.svg?branch=main&token=)](https://codecov.io/gh/gap-packages/ClassicalMaximals)

# The GAP package ClassicalMaximals

Translation of magma `ClassicalMaximals` to GAP. For resources see
[this hack.md](https://hackmd.io/aOvJbbctTAKlFQl4kwf4Jg).

## Status

### Already implemented
- geometric subgroups in cases L, S, U, O (construction using [HR05] and [HR10] and filtering maximal ones according to [BHR13]), see below for exception
- tests using the RECOG package and the tables from [BHR13] section 8
	
### TODO
- additional subgroups, tests (and filtering?) for Omega(+, 8, q), see [HR10] section 11
- class C9/S according to [BHR13] (see 
[#41](https://github.com/gap-packages/ClassicalMaximals/pull/41))
- novelties and non-quasisimple groups (see 
[Magma's options](http://magma.maths.usyd.edu.au/magma/handbook/text/768#9097))
- optional: let user select form (e.g. Magma standard form)

## Contact

To report issues please use our
[issue tracker](https://github.com/gap-packages/ClassicalMaximals/issues).

## License

ClassicalMaximals is free software; you can redistribute and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or (at
your opinion) any later version. For more information see the `LICENSE` file.
