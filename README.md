[![CI](https://github.com/gap-packages/ClassicalMaximals/workflows/CI/badge.svg?branch=main)](https://github.com/gap-packages/ClassicalMaximals/actions?query=workflow%3ACI+branch%3Amain)
[![Code Coverage](https://codecov.io/github/gap-packages/ClassicalMaximals/coverage.svg?branch=main&token=)](https://codecov.io/gh/gap-packages/ClassicalMaximals)

# The GAP package ClassicalMaximals

Translation of magma `ClassicalMaximals` to GAP. For resources see
[this hack.md](https://hackmd.io/aOvJbbctTAKlFQl4kwf4Jg).

## Status

### Implementation status

#### Geometric maximal subgroups (Aschbacher Classes C1-C8)
- **Type L**: Complete for dimensions 2-12
- **Type U**: Complete for dimensions 3-12
- **Type S**: Complete for dimensions 4-12
- **Type O**: Complete for dimensions 5-12
    - **C2-C8**: Complete for dimensions 3-12
    - **C2 & C4**: Complete for all dimensions

#### Almost simple groups (Class S)
- Complete for types L, U, S, O in dimensions up to 12
- **Supported options** (currently as `ValueOption`s, undocumented):
    - `all`: Conjugacy classes under the full automorphism group of the simple classical group
    - `novelties`: Intersections of novelty maximal subgroups with the quasisimple group
    - `special`: Normalisers in SO(n,q)
    - `general`: Normalisers in GL(n,q), GU(n,q), or GO(n,q)
    - `normaliser`: Normalizers in the full conformal group (preserving form modulo scalars)
        - forms preserved up to scalars are not stored (awaiting full GAP support for conformal groups)
    - all these options complete for dimensions up to 12
    - ... but group sizes for `special`, `general`, `normaliser` are not precomputed and stored

#### Testing & verification
- Verification of stored bilinear/sesquilinear/quadratic forms
- Group size checks via the `recog` package
- Cross-checks against tables in [BHR13] for the number of maximal subgroups
    - Class S & orthogonal geometric subgroups: Tests also against Magma's `ClassicalMaximals`

### Roadmap / TODO

#### Geometric maximal subgroups (Aschbacher Classes C1-C8)
- Finalize **C1** for dimensions 3 and 4
  ([#155](https://github.com/gap-packages/ClassicalMaximals/issues/155))
- Generalize other Aschbacher classes to work for all dimensions
- Implement `all`, `novelties`, `special`, `general`, `normaliser` for all geometric classes

#### Almost simple groups (Class S)
- Extend implementation beyond dimension 12 (for comparison: Magma covers dimensions up to 17)
- Precompute group sizes for `special`, `general`, `normaliser` options
- Streamline repetitive construction logic (especially in `ClassicalMaximals.gi`)

#### General features
- **User-defined target forms**: Enable users to provide custom forms;
  subgroups will be returned conjugated to preserve these specific forms
  ([#7](https://github.com/gap-packages/ClassicalMaximals/issues/7),
  [#144](https://github.com/gap-packages/ClassicalMaximals/issues/144)).
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
