gap> START_TEST("SubfieldMatrixGroups.tst");

#
gap> TestSubfieldSL := function(n, p, e, f)
>   local G;
>   G := SubfieldSL(n, p, e, f);
>   CheckIsSubsetSL(n, p ^ e, G);
>   CheckSize(G);
> end;;
gap> TestSubfieldSL(4, 2, 4, 2);
gap> TestSubfieldSL(2, 3, 6, 2);
gap> TestSubfieldSL(3, 7, 3, 1);

# Test error handling
gap> SubfieldSL(1, 1, 1, 1);
Error, the quotient of <e> by <f> must be a prime
gap> SubfieldSL(1, 1, 4, 1);
Error, the quotient of <e> by <f> must be a prime
gap> SubfieldSL(1, 1, 1, 4);
Error, the quotient of <e> by <f> must be a prime

#
gap> TestUnitarySubfieldSU := function(n, p, e, f)
>   local G;
>   G := UnitarySubfieldSU(n, p, e, f);
>   Assert(0, IsSubset(SU(n, p ^ e), GeneratorsOfGroup(G)));
>   #Assert(0, DefaultFieldOfMatrixGroup(G) = GF(p ^ (2 * e))); # FIXME
>   CheckSize(G);
> end;;
gap> TestUnitarySubfieldSU(2, 3, 6, 2);
gap> TestUnitarySubfieldSU(3, 7, 3, 1);
gap> TestUnitarySubfieldSU(3, 5, 3, 1);

# Test error handling
gap> UnitarySubfieldSU(1, 1, 1, 1);
Error, the quotient of <e> by <f> must be an odd prime
gap> UnitarySubfieldSU(1, 1, 2, 1);
Error, the quotient of <e> by <f> must be an odd prime
gap> UnitarySubfieldSU(1, 1, 1, 2);
Error, the quotient of <e> by <f> must be an odd prime

#
gap> TestSymplecticSubfieldSU := function(n, q)
>   local G;
>   G := SymplecticSubfieldSU(n, q);
>   CheckIsSubsetSU(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSymplecticSubfieldSU(4, 5);
gap> TestSymplecticSubfieldSU(2, 4);
gap> TestSymplecticSubfieldSU(4, 3);

# Test error handling
gap> SymplecticSubfieldSU(3, 3);
Error, <d> must be even

#
gap> TestOrthogonalSubfieldSU := function(epsilon, n, q)
>   local G;
>   G := OrthogonalSubfieldSU(epsilon, n, q);
>   CheckIsSubsetSU(n, q, G);
>   CheckSize(G);
> end;;
gap> TestOrthogonalSubfieldSU(0, 3, 5);
gap> TestOrthogonalSubfieldSU(0, 5, 3);
gap> TestOrthogonalSubfieldSU(1, 2, 5);
gap> TestOrthogonalSubfieldSU(1, 4, 3);
gap> TestOrthogonalSubfieldSU(-1, 2, 3);
gap> TestOrthogonalSubfieldSU(-1, 2, 5);
gap> TestOrthogonalSubfieldSU(-1, 4, 3);

#
gap> TestSubfieldSp := function(n, p, e, f)
>   local G;
>   G := SubfieldSp(n, p, e, f);
>   CheckIsSubsetSp(n, p ^ e, G);
>   CheckSize(G);
> end;;
gap> TestSubfieldSp(6, 2, 2, 1);
gap> TestSubfieldSp(4, 3, 2, 1);
gap> TestSubfieldSp(4, 3, 4, 2);
gap> TestSubfieldSp(4, 7, 2, 1);

# Test error handling
gap> SubfieldSp(3, 2, 2, 1);
Error, <d> must be even
gap> SubfieldSp(4, 2, 1, 2);
Error, <f> must be a divisor of <e>
gap> SubfieldSp(4, 2, 4, 1);
Error, the quotient of <e> by <f> must be a prime

#
gap> TestSubfieldOmega := function(epsilon, n, p, e, f, epsilon_0)
>   local G;
>   G := SubfieldOmega(epsilon, n, p, e, f, epsilon_0);
>   CheckIsSubsetOmega(epsilon, n, p ^ e, G);
>   CheckSize(G);
> end;;
gap> TestSubfieldOmega(0, 7, 3, 5, 1, 0);
gap> TestSubfieldOmega(0, 5, 3, 4, 2, 0);
gap> TestSubfieldOmega(0, 7, 5, 3, 1, 0);
gap> TestSubfieldOmega(0, 7, 7, 2, 1, 0);
gap> TestSubfieldOmega(-1, 8, 4, 5, 1, -1);
gap> TestSubfieldOmega(-1, 10, 3, 3, 1, -1);
gap> TestSubfieldOmega(1, 8, 4, 5, 1, 1);
gap> TestSubfieldOmega(1, 6, 5, 2, 1, 1);
gap> TestSubfieldOmega(1, 8, 3, 2, 1, 1);
gap> TestSubfieldOmega(1, 6, 8, 2, 1, -1);
gap> TestSubfieldOmega(1, 6, 3, 4, 2, -1);
gap> TestSubfieldOmega(1, 8, 3, 2, 1, -1);
gap> TestSubfieldOmega(1, 10, 3, 2, 1, -1);

# Test error handling
gap> SubfieldOmega(0, 8, 3, 2, 1, 0);
Error, <d> must be odd
gap> SubfieldOmega(1, 7, 3, 2, 1, 1);
Error, <d> must be even
gap> SubfieldOmega(2, 7, 3, 2, 1, 1);
Error, <epsilon> must be in [-1, 0, 1]
gap> SubfieldOmega(0, 7, 4, 2, 1, 0);
Error, <d> must be even if <q> is even
gap> SubfieldOmega(0, 7, 3, 3, 2, 0);
Error, <f> must be a divisor of <e>
gap> SubfieldOmega(0, 7, 3, 4, 1, 0);
Error, the quotient of <e> by <f> must be a prime
gap> SubfieldOmega(0, 7, 3, 2, 1, 2);
Error, <epsilon_0> must be in [-1, 0, 1]
gap> SubfieldOmega(-1, 8, 3, 2, 1, 1);
Error, <epsilon_0> ^ (<e> / <f>) must be equal to <epsilon>

#
gap> STOP_TEST("SubfieldMatrixGroups.tst", 0);
