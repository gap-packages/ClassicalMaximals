gap> START_TEST("SubfieldMatrixGroups.tst");

#
gap> TestSubfieldSL := function(args)
>   local n, p, e, f, G, hasSize;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := SubfieldSL(n, p, e, f);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SL(n, p ^ e), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(p ^ e));
>   Assert(0, hasSize);
> end;;
gap> TestSubfieldSL([4, 2, 4, 2]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestSubfieldSL([2, 3, 6, 2]);
gap> TestSubfieldSL([3, 7, 3, 1]);
#@fi

# Test error handling
gap> SubfieldSL(1, 1, 1, 1);
Error, the quotient of <e> by <f> must be a prime
gap> SubfieldSL(1, 1, 4, 1);
Error, the quotient of <e> by <f> must be a prime
gap> SubfieldSL(1, 1, 1, 4);
Error, the quotient of <e> by <f> must be a prime

#
gap> TestUnitarySubfieldSU := function(args)
>   local n, p, e, f, G, hasSize;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := UnitarySubfieldSU(n, p, e, f);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SU(n, p ^ e), GeneratorsOfGroup(G)));
>   #Assert(0, DefaultFieldOfMatrixGroup(G) = GF(p ^ (2 * e))); # FIXME
>   Assert(0, hasSize);
> end;;
gap> TestUnitarySubfieldSU([2, 3, 6, 2]);
gap> TestUnitarySubfieldSU([3, 7, 3, 1]);
gap> TestUnitarySubfieldSU([3, 5, 3, 1]);

# Test error handling
gap> UnitarySubfieldSU(1, 1, 1, 1);
Error, the quotient of <e> by <f> must be an odd prime
gap> UnitarySubfieldSU(1, 1, 2, 1);
Error, the quotient of <e> by <f> must be an odd prime
gap> UnitarySubfieldSU(1, 1, 1, 2);
Error, the quotient of <e> by <f> must be an odd prime

#
gap> TestSymplecticSubfieldSU := function(args)
>   local n, q, G, hasSize;
>   n := args[1];
>   q := args[2];
>   G := SymplecticSubfieldSU(n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SU(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   Assert(0, hasSize);
> end;;
gap> TestSymplecticSubfieldSU([4, 5]);
gap> TestSymplecticSubfieldSU([2, 4]);
gap> TestSymplecticSubfieldSU([4, 3]);

# Test error handling
gap> SymplecticSubfieldSU(3, 3);
Error, <d> must be even

#
gap> TestOrthogonalSubfieldSU := function(epsilon, n, q)
>   local G, hasSize;
>   G := OrthogonalSubfieldSU(epsilon, n, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SU(n, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   Assert(0, hasSize);
> end;;
gap> TestOrthogonalSubfieldSU(0, 3, 5);
gap> TestOrthogonalSubfieldSU(0, 5, 3);
gap> TestOrthogonalSubfieldSU(1, 2, 5);
gap> TestOrthogonalSubfieldSU(1, 4, 3);
gap> TestOrthogonalSubfieldSU(-1, 2, 3);
gap> TestOrthogonalSubfieldSU(-1, 2, 5);
gap> TestOrthogonalSubfieldSU(-1, 4, 3);

#
gap> TestSubfieldSp := function(args)
>   local n, p, e, f, G, hasSize;
>   n := args[1];
>   p := args[2];
>   e := args[3];
>   f := args[4];
>   G := SubfieldSp(n, p, e, f);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Sp(n, p ^ e), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(p ^ e));
>   Assert(0, hasSize);
> end;;
gap> TestSubfieldSp([6, 2, 2, 1]);
gap> TestSubfieldSp([4, 3, 2, 1]);
gap> TestSubfieldSp([4, 3, 4, 2]);
gap> TestSubfieldSp([4, 7, 2, 1]);

# Test error handling
gap> SubfieldSp(3, 2, 2, 1);
Error, <d> must be even
gap> SubfieldSp(4, 2, 1, 2);
Error, <f> must be a divisor of <e>
gap> SubfieldSp(4, 2, 4, 1);
Error, the quotient of <f> by <e> must be a prime

#
gap> STOP_TEST("SubfieldMatrixGroups.tst", 0);
