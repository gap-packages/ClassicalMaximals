[![CI](https://github.com/gap-packages/ClassicalMaximals/workflows/CI/badge.svg?branch=main)](https://github.com/gap-packages/ClassicalMaximals/actions?query=workflow%3ACI+branch%3Amain)
[![Code Coverage](https://codecov.io/github/gap-packages/ClassicalMaximals/coverage.svg?branch=main&token=)](https://codecov.io/gh/gap-packages/ClassicalMaximals)

# The GAP package ClassicalMaximals

Translation of magma `ClassicalMaximals` to GAP. For resources see
[this hack.md](https://hackmd.io/aOvJbbctTAKlFQl4kwf4Jg).

## Status

### Implementation status

#### Geometric maximal subgroups (Aschbacher Classes C1-C8)
- Complete for types L, U, S, O in all dimensions
- Supported options (via option records, undocumented):
    - `all` (see below)

#### Almost simple groups (Class S)
- Complete for types L, U, S, O in dimensions up to 12
- Supported options (via option records, undocumented):
    - `all`: Conjugacy classes under the full automorphism group of the simple classical group
    - `novelties`: Intersections of novelty maximal subgroups with the quasisimple group
    - `special`: Normalisers in SO(n,q)
    - `general`: Normalisers in GL(n,q), GU(n,q), or GO(n,q)
    - `normaliser`: Normalisers in the full conformal group (preserving form modulo scalars)
        - forms preserved up to scalars are not stored (awaiting full GAP support for conformal groups)
    - all these options complete for dimensions up to 12
    - ... but group sizes for `special`, `general`, `normaliser` are not precomputed and stored

#### Testing & verification
- Verification of stored bilinear/sesquilinear/quadratic forms
- Group size checks via the `recog` package
- Cross-checks against tables in [BHR13] and against Magma's `ClassicalMaximals`
  for the number of maximal subgroups

### Roadmap / TODO

#### Geometric maximal subgroups (Aschbacher Classes C1-C8)
- Implement `novelties`, `special`, `general`, `normaliser` for all geometric classes

#### Almost simple groups (Class S)
- Extend implementation beyond dimension 12 (for comparison: Magma covers dimensions up to 17)
- Precompute group sizes for `special`, `general`, `normaliser` options
- Streamline repetitive construction logic (especially in `ClassicalMaximals.gi`)

#### General features
- Adapt `ConjugateToStandardForm` to support forms preserved up to a scalar
  (depending on future updates in the `forms` package)

## Contact

To report issues please use our
[issue tracker](https://github.com/gap-packages/ClassicalMaximals/issues).

## License

ClassicalMaximals is free software; you can redistribute and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or (at
your opinion) any later version. For more information see the `LICENSE` file.

## Funding

The development of this GAP package is supported by the
German Research Foundation (DFG) within the
[Collaborative Research Center TRR 195](https://www.computeralgebra.de/sfb/).
