gap> TestSLStabilizerOfSubspace := function(args)
>   local n, q, k, G, hasSize;
>   Info(InfoClassicalMaximalsTests, 1, args);
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SLStabilizerOfSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G)) and
>          DefaultFieldOfMatrixGroup(G) = GF(q) and
>          hasSize;
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS) 
gap> testsSLStabilizerOfSubspace := [[4, 3, 2], [3, 8, 2], [2, 7, 1]];;
#@else
gap> testsSLStabilizerOfSubspace := [[4, 3, 2], [2, 7, 1]];;
#@fi
gap> ForAll(testsSLStabilizerOfSubspace, TestSLStabilizerOfSubspace);
true
gap> TestSUStabilizerOfIsotropicSubspace := function(args)
>   local n, q, k, G, hasSize;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SUStabilizerOfIsotropicSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G)) and
>          DefaultFieldOfMatrixGroup(G) = GF(q ^ 2) and
>          hasSize;
> end;;
gap> testsSUStabilizerOfIsotropicSubspace := [[4, 3, 2], [3, 5, 1], [3, 4, 1], [4, 3, 1]];;
gap> ForAll(testsSUStabilizerOfIsotropicSubspace, TestSUStabilizerOfIsotropicSubspace);
true
gap> TestSUStabilizerOfNonDegenerateSubspace := function(args)
>   local n, q, k, G, hasSize;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SUStabilizerOfNonDegenerateSubspace(n, q, k);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G)) and
>          DefaultFieldOfMatrixGroup(G) = GF(q ^ 2) and
>          hasSize;
> end;;
gap> testsSUStabilizerOfNonDegenerateSubspace := [[5, 3, 2], [6, 3, 2], [4, 5, 1], [5, 4, 1]];;
gap> ForAll(testsSUStabilizerOfNonDegenerateSubspace, TestSUStabilizerOfNonDegenerateSubspace);
true
gap> TestSpStabilizerOfIsotropicSubspace := function(args)
>   local n, q, k, G;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SpStabilizerOfIsotropicSubspace(n, q, k);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(Sp(n, q), GeneratorsOfGroup(G)) and
>          DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
gap> testsSpStabilizerOfIsotropicSubspace := [];;
gap> ForAll(testsSpStabilizerOfIsotropicSubspace, TestSpStabilizerOfIsotropicSubspace);
true
gap> TestSpStabilizerOfNonDegenerateSubspace := function(args)
>   local n, q, k, G;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SpStabilizerOfNonDegenerateSubspace(n, q, k);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(Sp(n, q), GeneratorsOfGroup(G)) and
>          DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
gap> testsSpStabilizerOfNonDegenerateSubspace := [];;
gap> ForAll(testsSpStabilizerOfNonDegenerateSubspace, TestSpStabilizerOfNonDegenerateSubspace);
true
