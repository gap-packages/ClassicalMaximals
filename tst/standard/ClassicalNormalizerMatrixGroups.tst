gap> TestSymplecticNormalizerInSL := function(args)
>   local n, q, G;
>   n := args[1];
>   q := args[2];
>   G := SymplecticNormalizerInSL(n, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
gap> testsSymplecticNormalizerInSL := [[4, 3], [4, 5], [6, 4]];;
gap> ForAll(testsSymplecticNormalizerInSL, TestSymplecticNormalizerInSL);
true
gap> TestUnitaryNormalizerInSL := function(args)
>   local n, q, G;
>   n := args[1];
>   q := args[2];
>   G := UnitaryNormalizerInSL(n, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
gap> testsUnitaryNormalizerInSL := [[4, 9], [3, 9], [4, 4]];;
gap> ForAll(testsUnitaryNormalizerInSL, TestUnitaryNormalizerInSL);
true
gap> TestOrthogonalNormalizerInSL := function(args)
>   local epsilon, n, q, G;
>   epsilon := args[1];
>   n := args[2];
>   q := args[3];
>   G := OrthogonalNormalizerInSL(epsilon, n, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
gap> testsOrthogonalNormalizerInSL := [[0, 3, 5], [-1, 6, 5], [1, 6, 5], [-1, 4, 3], [1, 4, 3], 
>                                      [-1, 4, 5], [1, 4, 5], [-1, 6, 3]];;
gap> ForAll(testsOrthogonalNormalizerInSL, TestOrthogonalNormalizerInSL);
true
