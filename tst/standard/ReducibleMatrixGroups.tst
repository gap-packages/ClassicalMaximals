gap> START_TEST("ReducibleMatrixGroups.tst");

#
gap> TestSLStabilizerOfSubspace := function(n, q, k)
>   local G;
>   Info(InfoClassicalMaximalsTests, 1, [n,q,k]);
>   G := SLStabilizerOfSubspace(n, q, k);
>   CheckIsSubsetSL(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSLStabilizerOfSubspace(4, 3, 2);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestSLStabilizerOfSubspace(3, 8, 2); # FIXME: `Error, !!!`, see https://github.com/gap-packages/recog/issues/12
#@fi
gap> TestSLStabilizerOfSubspace(2, 7, 1);

#
gap> TestSUStabilizerOfIsotropicSubspace := function(n, q, k)
>   local G;
>   G := SUStabilizerOfIsotropicSubspace(n, q, k);
>   CheckIsSubsetSU(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSUStabilizerOfIsotropicSubspace(4, 3, 2);
gap> TestSUStabilizerOfIsotropicSubspace(3, 5, 1);
gap> TestSUStabilizerOfIsotropicSubspace(3, 4, 1);
gap> TestSUStabilizerOfIsotropicSubspace(4, 3, 1);

#
gap> TestSUStabilizerOfNonDegenerateSubspace := function(n, q, k)
>   local G;
>   G := SUStabilizerOfNonDegenerateSubspace(n, q, k);
>   CheckIsSubsetSU(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSUStabilizerOfNonDegenerateSubspace(5, 3, 2);
gap> TestSUStabilizerOfNonDegenerateSubspace(6, 3, 2);
gap> TestSUStabilizerOfNonDegenerateSubspace(4, 5, 1);
gap> TestSUStabilizerOfNonDegenerateSubspace(5, 4, 1);

#
gap> TestSpStabilizerOfIsotropicSubspace := function(n, q, k)
>   local G;
>   G := SpStabilizerOfIsotropicSubspace(n, q, k);
>   CheckIsSubsetSp(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSpStabilizerOfIsotropicSubspace(4, 2, 1);
gap> TestSpStabilizerOfIsotropicSubspace(4, 9, 1);
gap> TestSpStabilizerOfIsotropicSubspace(6, 4, 1);
gap> TestSpStabilizerOfIsotropicSubspace(6, 7, 2);

# Test error handling
gap> SpStabilizerOfIsotropicSubspace(5, 2, 1);
Error, <d> must be even
gap> SpStabilizerOfIsotropicSubspace(4, 2, 3);
Error, <k> must be less than or equal to <d> / 2

#
gap> TestSpStabilizerOfNonDegenerateSubspace := function(n, q, k)
>   local G;
>   G := SpStabilizerOfNonDegenerateSubspace(n, q, k);
>   CheckIsSubsetSp(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSpStabilizerOfNonDegenerateSubspace(4, 2, 1);
gap> TestSpStabilizerOfNonDegenerateSubspace(4, 9, 1);
gap> TestSpStabilizerOfNonDegenerateSubspace(6, 4, 1);
gap> TestSpStabilizerOfNonDegenerateSubspace(6, 7, 2);

# Test error handling
gap> SpStabilizerOfNonDegenerateSubspace(5, 2, 1);
Error, <d> must be even
gap> SpStabilizerOfNonDegenerateSubspace(4, 2, 3);
Error, <k> must be less than <d> / 2

#
gap> TestOmegaStabilizerOfIsotropicSubspace := function(epsilon, d, q, k)
>   local G;
>   G := OmegaStabilizerOfIsotropicSubspace(epsilon, d, q, k);
>   Assert(0, IsSubsetOmega(epsilon, d, q, G));
>   Assert(0, CheckSize(G));
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOmegaStabilizerOfIsotropicSubspace(1, 6, 8, 2);
#@fi
gap> TestOmegaStabilizerOfIsotropicSubspace(1, 8, 5, 4);
gap> TestOmegaStabilizerOfIsotropicSubspace(0, 5, 7, 2);
gap> TestOmegaStabilizerOfIsotropicSubspace(1, 8, 5, 3);
gap> TestOmegaStabilizerOfIsotropicSubspace(-1, 8, 4, 2);
gap> TestOmegaStabilizerOfIsotropicSubspace(-1, 6, 5, 1);
gap> TestOmegaStabilizerOfIsotropicSubspace(0, 5, 3, 1);

# Test error handling
gap> OmegaStabilizerOfIsotropicSubspace(0, 6, 5, 1);
Error, <d> must be odd
gap> OmegaStabilizerOfIsotropicSubspace(1, 5, 5, 1);
Error, <d> must be even
gap> OmegaStabilizerOfIsotropicSubspace(2, 5, 5, 1);
Error, <epsilon> must be in [-1, 0, 1]
gap> OmegaStabilizerOfIsotropicSubspace(0, 5, 8, 1);
Error, <d> must be even if <q> is even
gap> OmegaStabilizerOfIsotropicSubspace(0, 5, 5, 3);
Error, <k> must be less than or equal to <m>
gap> TestOmegaStabilizerOfIsotropicSubspace(-1, 8, 5, 4);
Error, <k> must not be equal to <m> for <epsilon> = -1
gap> TestOmegaStabilizerOfIsotropicSubspace(-1, 4, 5, 1);
Error, <d> must be at least 5

#
gap> TestOmegaStabilizerOfNonDegenerateSubspace := function(epsilon, d, q, epsilon_0, k)
>   local G;
>   G := OmegaStabilizerOfNonDegenerateSubspace(epsilon, d, q, epsilon_0, k);
>   CheckIsSubsetOmega(epsilon, d, q, G);
>   CheckSize(G);
> end;;
gap> TestOmegaStabilizerOfNonDegenerateSubspace(0, 7, 5, 1, 3);
gap> TestOmegaStabilizerOfNonDegenerateSubspace(0, 7, 5, -1, 5);
gap> TestOmegaStabilizerOfNonDegenerateSubspace(1, 8, 5, -1, 2);
gap> TestOmegaStabilizerOfNonDegenerateSubspace(1, 6, 5, 0, 1);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOmegaStabilizerOfNonDegenerateSubspace(1, 6, 8, 1, 2); # `Error, !!!`, may be related to https://github.com/gap-packages/recog/issues/12
gap> TestOmegaStabilizerOfNonDegenerateSubspace(-1, 8, 5, -1, 4); # Error, List Element: <list>[3] must have an assigned value
#@fi
gap> TestOmegaStabilizerOfNonDegenerateSubspace(-1, 6, 7, 0, 1);
gap> TestOmegaStabilizerOfNonDegenerateSubspace(-1, 6, 8, 1, 2);

# Test error handling
gap> OmegaStabilizerOfNonDegenerateSubspace(2, 5, 5, 1, 2);
Error, <epsilon> must be in [-1, 0, 1]
gap> OmegaStabilizerOfNonDegenerateSubspace(1, 2, 3, 2, 1);
Error, <epsilon_0> must be in [-1, 0, 1]
gap> OmegaStabilizerOfNonDegenerateSubspace(0, 5, 4, 1, 2);
Error, <d> must be even if <q> is even
gap> OmegaStabilizerOfNonDegenerateSubspace(0, 4, 5, 1, 1);
Error, <d> must be odd
gap> OmegaStabilizerOfNonDegenerateSubspace(0, 5, 5, 0, 1);
Error, <epsilon_0> must be -1 or 1
gap> OmegaStabilizerOfNonDegenerateSubspace(0, 5, 5, 1, 2);
Error, <k> must be odd
gap> OmegaStabilizerOfNonDegenerateSubspace(0, 5, 5, 1, 7);
Error, <k> must be less than <d>
gap> OmegaStabilizerOfNonDegenerateSubspace(1, 5, 5, 0, 1);
Error, <d> must be even
gap> OmegaStabilizerOfNonDegenerateSubspace(1, 4, 4, 0, 1);
Error, <q> must be odd if <k> is odd
gap> OmegaStabilizerOfNonDegenerateSubspace(1, 6, 4, 0, 2);
Error, <k> must be odd if <epsilon_0> is 0
gap> OmegaStabilizerOfNonDegenerateSubspace(1, 4, 5, 1, 1);
Error, <k> must be even if <epsilon_0> is 1 or -1
gap> OmegaStabilizerOfNonDegenerateSubspace(1, 4, 5, 0, 3);
Error, <k> must be less than <d> / 2
gap> OmegaStabilizerOfNonDegenerateSubspace(-1, 5, 5, 0, 1);
Error, <d> must be even
gap> OmegaStabilizerOfNonDegenerateSubspace(-1, 4, 4, 0, 1);
Error, <q> must be odd if <k> is odd
gap> OmegaStabilizerOfNonDegenerateSubspace(-1, 6, 4, 0, 2);
Error, <k> must be odd if <epsilon_0> is 0
gap> OmegaStabilizerOfNonDegenerateSubspace(-1, 6, 5, 0, 3);
Error, <k> must not be equal to <d> / 2 if <epsilon_0> is 0
gap> OmegaStabilizerOfNonDegenerateSubspace(-1, 4, 5, 1, 1);
Error, <k> must be even if <epsilon_0> is 1 or -1
gap> OmegaStabilizerOfNonDegenerateSubspace(-1, 4, 5, 1, 4);
Error, <k> must be less than or equal to <d> / 2

#
gap> TestOmegaStabilizerOfNonSingularVector := function(epsilon, d, q)
>   local G;
>   G := OmegaStabilizerOfNonSingularVector(epsilon, d, q);
>   CheckIsSubsetOmega(epsilon, d, q, G);
>   CheckSize(G);
> end;;
gap> TestOmegaStabilizerOfNonSingularVector(1, 6, 4);
gap> TestOmegaStabilizerOfNonSingularVector(-1, 6, 4);
gap> TestOmegaStabilizerOfNonSingularVector(1, 8, 2);
gap> TestOmegaStabilizerOfNonSingularVector(-1, 8, 2);
gap> TestOmegaStabilizerOfNonSingularVector(1, 4, 8);
gap> TestOmegaStabilizerOfNonSingularVector(-1, 4, 8);

# Test error handling
gap> OmegaStabilizerOfNonSingularVector(0, 2, 4);
Error, <epsilon> must be 1 or -1
gap> OmegaStabilizerOfNonSingularVector(-1, 6, 3);
Error, <q> must be even
gap> OmegaStabilizerOfNonSingularVector(-1, 5, 4);
Error, <d> must be even
gap> OmegaStabilizerOfNonSingularVector(-1, 2, 4);
Error, <d> must be greater than 2

#
gap> STOP_TEST("ReducibleMatrixGroups.tst", 0);
