This file describes changes in the ClassicalMaximals package.

## Unreleased

  - Classes C1-C8 now work in all dimensions, following the tables
    in [KL90]; previously, some cases were only handled up to
    dimension 12
  - Support the (undocumented) `all` option for classes C1-C8

## 1.1 (2026-05-26)

  - Add `recog` as a dependency
  - Avoid some accidental "hidden" dependencies on other packages
  - change `TestFile` in `PackageInfo.g` to use "quick" tests so
    we don't hit time limits in the package

## 1.0 (2026-05-17)

  - initial release
 