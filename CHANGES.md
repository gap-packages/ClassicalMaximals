This file describes changes in the ClassicalMaximals package.

## Unreleased

  - Classes C1-C8 now work in all dimensions, following the tables
    in [KL90]; previously, some cases were only handled up to
    dimension 12 (#176)
  - Fix missing and duplicate classes of Omega+(n, q) and
    Omega-(n, q): for even i < n/2, Omega-(n, q) lacked the C1
    stabilisers of nondegenerate i-spaces of minus type, e.g. the
    class of order 120960 in Omega-(8, 2); and where a type splits
    into several Omega-classes, some were listed twice and others
    not at all, e.g. for Omega+(6, 3) and for the C7 subgroups
    O-(4, q) wr S(2) of Omega+(16, q), q odd (#181, #187, #197)
  - Drop the non-maximal C9 subgroups L2(11) of Sp(12, 4) and L2(13)
    of Sp(12, 8), which lie in O-(12, q):
    `ClassicalMaximalsGeneric("S", 12, 4)` returned 19 classes
    instead of 17 (#180)
  - Some maximal subgroups of SU(n, q) had generators outside
    SU(n, q): the C1 stabilisers of totally isotropic subspaces for
    odd n and some even q (order 258048 instead of 32256 in
    SU(3, 8)), and the C5 subgroups of type GU(n, q0), which were
    SL(n, q0), e.g. in SU(3, 8) (#182, #183)
  - Some maximal subgroups of Omega+(n, q) and Omega-(n, q) had
    generators outside GAP's standard group: the C5 subgroups of
    type O-(n, q0), e.g. in Omega+(8, 9), and some C9 subgroups of
    Omega-(n, q), e.g. in Omega-(6, 11) (#184, #189)
  - Fix two subgroups of SU(n, q) whose generators and stored order
    disagreed: the C5 subgroups of type Sp(n, q) generated a
    subgroup of index 2 for some n and q = 3 mod 4, e.g. in
    SU(8, 3); and the stored order of the C9 subgroup SU(5, q) of
    SU(10, q) was 5 times too large if 5 divides q + 1, e.g. in
    SU(10, 4) (#198, #199)
  - Some results stored no invariant form: on GAP 4.15, classes
    obtained by conjugating another class, e.g. some C9 subgroups of
    Sp(4, 11); on GAP 4.16, the C5 subgroups of SU(n, q) of
    orthogonal and symplectic type (#201)
  - Fix errors in `ClassicalMaximalsGeneric` for some (type, n, q):
    `ClassicalMaximalsGeneric("L", 11, 169)` stopped with "Conway
    Polynomial ... will need to be computed and might be slow", and
    `ClassicalMaximalsGeneric("U", 4, 128)` with "List Element:
    <list>[1] must have an assigned value" (#179, #186)
  - The manual lists the misprints in [HR05] and [HR10] that the
    constructions work around (#200)
  - The tests now need the `ctbllib` package (#195)

## 1.1 (2026-05-26)

  - Add `recog` as a dependency
  - Avoid some accidental "hidden" dependencies on other packages
  - change `TestFile` in `PackageInfo.g` to use "quick" tests so
    we don't hit time limits in the package

## 1.0 (2026-05-17)

  - initial release
