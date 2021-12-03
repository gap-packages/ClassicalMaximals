gap> START_TEST("ReducibleMatrixGroups.tst");

#
gap> TestSLStabilizerOfSubspace := function(args)
>   local n, q, k, G, hasSize;
>   Info(InfoClassicalMaximalsTests, 1, args);
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SLStabilizerOfSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SL(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestSLStabilizerOfSubspace([4, 3, 2]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestSLStabilizerOfSubspace([3, 8, 2]); # FIXME: `Error, !!!`, see https://github.com/gap-packages/recog/issues/12
#@fi
gap> TestSLStabilizerOfSubspace([2, 7, 1]);

#
gap> TestSUStabilizerOfIsotropicSubspace := function(args)
>   local n, q, k, G, hasSize;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SUStabilizerOfIsotropicSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SU(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   Assert(0, hasSize);
> end;;
gap> TestSUStabilizerOfIsotropicSubspace([4, 3, 2]);
gap> TestSUStabilizerOfIsotropicSubspace([3, 5, 1]);
gap> TestSUStabilizerOfIsotropicSubspace([3, 4, 1]);
gap> TestSUStabilizerOfIsotropicSubspace([4, 3, 1]);

#
gap> TestSUStabilizerOfNonDegenerateSubspace := function(args)
>   local n, q, k, G, hasSize;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SUStabilizerOfNonDegenerateSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SU(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   Assert(0, hasSize);
> end;;
gap> TestSUStabilizerOfNonDegenerateSubspace([5, 3, 2]);
gap> TestSUStabilizerOfNonDegenerateSubspace([6, 3, 2]);
gap> TestSUStabilizerOfNonDegenerateSubspace([4, 5, 1]);
gap> TestSUStabilizerOfNonDegenerateSubspace([5, 4, 1]);

#
gap> TestSpStabilizerOfIsotropicSubspace := function(args)
>   local n, q, k, G, hasSize;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SpStabilizerOfIsotropicSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Sp(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestSpStabilizerOfIsotropicSubspace([4, 2, 1]);
gap> TestSpStabilizerOfIsotropicSubspace([4, 9, 1]);
gap> TestSpStabilizerOfIsotropicSubspace([6, 4, 1]);
gap> TestSpStabilizerOfIsotropicSubspace([6, 7, 2]);

# Test error handling
gap> SpStabilizerOfIsotropicSubspace(5, 2, 1);
Error, <d> must be even
gap> SpStabilizerOfIsotropicSubspace(4, 2, 3);
Error, <k> must be less than <d> / 2

#
gap> TestSpStabilizerOfNonDegenerateSubspace := function(args)
>   local n, q, k, G, hasSize;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SpStabilizerOfNonDegenerateSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Sp(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestSpStabilizerOfNonDegenerateSubspace([4, 2, 1]);
gap> TestSpStabilizerOfNonDegenerateSubspace([4, 9, 1]);
gap> TestSpStabilizerOfNonDegenerateSubspace([6, 4, 1]);
gap> TestSpStabilizerOfNonDegenerateSubspace([6, 7, 2]);

# Test error handling
gap> SpStabilizerOfNonDegenerateSubspace(5, 2, 1);
Error, <d> must be even
gap> SpStabilizerOfNonDegenerateSubspace(4, 2, 3);
Error, <k> must be less than <d> / 2

#
gap> TestOmegaStabilizerOfNonSingularVector := function(args)
>   local epsilon, d, q, hasSize, G;
>   epsilon := args[1];
>   d := args[2];
>   q := args[3];
>   G := OmegaStabilizerOfNonSingularVector(epsilon, d, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Omega(epsilon, d, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestOmegaStabilizerOfNonSingularVector([1, 6, 4]);
gap> TestOmegaStabilizerOfNonSingularVector([-1, 6, 4]);
gap> TestOmegaStabilizerOfNonSingularVector([1, 8, 2]);
gap> TestOmegaStabilizerOfNonSingularVector([-1, 8, 2]);
gap> TestOmegaStabilizerOfNonSingularVector([1, 4, 8]);
gap> TestOmegaStabilizerOfNonSingularVector([-1, 4, 8]);

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
