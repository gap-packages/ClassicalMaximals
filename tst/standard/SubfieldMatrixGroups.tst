gap> TestSubfieldSL := function(args)
>   local n, p, e, f, G, hasSize;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := SubfieldSL(n, p, e, f);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, p ^ e), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(p ^ e)
>          and hasSize;
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsSubfieldSL := [[4, 2, 4, 2], [2, 3, 6, 2], [3, 7, 3, 1]];;
#@else
gap> testsSubfieldSL := [[4, 2, 4, 2]];;
#@fi
gap> ForAll(testsSubfieldSL, TestSubfieldSL);
true
gap> TestUnitarySubfieldSU := function(args)
>   local n, p, e, f, G, hasSize;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := UnitarySubfieldSU(n, p, e, f);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, p ^ e), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(p ^ (2 * e))
>          and hasSize;
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS) 
gap> testsUnitarySubfieldSU := [[2, 3, 6, 2], [3, 7, 3, 1], [3, 5, 3, 1]];;
#@else
gap> testsUnitarySubfieldSU := [];;
#@fi
gap> ForAll(testsUnitarySubfieldSU, TestUnitarySubfieldSU);
true
gap> TestSymplecticSubfieldSU := function(args)
>   local n, q, G, hasSize;
>   n := args[1];
>   q := args[2];
>   G := SymplecticSubfieldSU(n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2)
>          and hasSize;
> end;;
gap> testsSymplecticSubfieldSU := [[4, 5], [2, 4], [4, 3]];;
gap> ForAll(testsSymplecticSubfieldSU, TestSymplecticSubfieldSU);
true
gap> TestOrthogonalSubfieldSU := function(args)
>   local epsilon, n, q, G, hasSize;
>   epsilon := args[1];
>   n := args[2];
>   q := args[3];
>   G := OrthogonalSubfieldSU(epsilon, n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2)
>          and hasSize;
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsOrthogonalSubfieldSU := [[0, 3, 5], [0, 5, 3], [1, 2, 5], [1, 4, 3], [-1, 2, 3], [-1, 2, 5], [-1, 4, 3]];;
#@else
gap> testsOrthogonalSubfieldSU := [[0, 3, 5], [0, 5, 3], [-1, 2, 3], [-1, 4, 3]];;
#@fi
gap> ForAll(testsOrthogonalSubfieldSU, TestOrthogonalSubfieldSU);
true
gap> TestSubfieldSp := function(args)
>   local n, p, e, f, G, hasSize;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := SubfieldSp(n, p, e, f);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(Sp(n, p ^ e), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(p ^ e)
>          and hasSize;
> end;;
gap> testsSubfieldSp := [[6, 2, 2, 1], [4, 3, 2, 1], [4, 3, 4, 2], [4, 7, 2, 1]];;
gap> ForAll(testsSubfieldSp, TestSubfieldSp);
true
gap> SubfieldSp(3, 2, 2, 1);
Error, <d> must be even.
gap> SubfieldSp(4, 2, 1, 2);
Error, <f> must be a divisor of <e>.
gap> SubfieldSp(4, 2, 4, 1);
Error, the quotient of <f> by <e> must be a prime.
