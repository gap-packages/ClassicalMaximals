gap> TestSubfieldSL := function(args)
>   local n, p, e, f, G;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := SubfieldSL(n, p, e, f);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, p ^ e), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(p ^ e);
> end;;
gap> testsSubfieldSL := [[4, 2, 4, 2], [2, 3, 6, 2], [3, 7, 3, 1]];;
gap> ForAll(testsSubfieldSL, TestSubfieldSL);
true
gap> TestUnitarySubfieldSU := function(args)
>   local n, p, e, f, G;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := UnitarySubfieldSU(n, p, e, f);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, p ^ e), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(p ^ (2 * e));
> end;;
gap> testsUnitarySubfieldSU := [[2, 3, 6, 2], [3, 7, 3, 1], [3, 5, 3, 1]];;
gap> ForAll(testsUnitarySubfieldSU, TestUnitarySubfieldSU);
true
gap> TestSymplecticSubfieldSU := function(args)
>   local n, q;
>   n := args[1];
>   q := args[2];
>   G := SymplecticSubfieldSU(n, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2);
> end;;
gap> testsSymplecticSubfieldSU := [[4, 5], [2, 4], [4, 3]];;
gap> ForAll(testsSymplecticSubfieldSU, TestSymplecticSubfieldSU);
true
gap> TestOrthogonalSubfieldSU := function(args)
>   local epsilon, n, q, G;
>   epsilon := args[1];
>   n := args[2];
>   q := args[3];
>   G := OrthogonalSubfieldSU(epsilon, n, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsOrthogonalSubfieldSU := [[0, 3, 5], [0, 5, 3], [1, 2, 5], [1, 4, 3], [-1, 2, 3], [-1, 2, 5], [-1, 4, 3]];;
#@else
gap> testsOrthogonalSubfieldSU := [[0, 3, 5], [0, 5, 3], [-1, 2, 3], [-1, 2, 5], [-1, 4, 3]];;
#@fi
gap> ForAll(testsOrthogonalSubfieldSU, TestOrthogonalSubfieldSU);
true
