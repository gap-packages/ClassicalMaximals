gap> START_TEST("Utils.tst");

#
gap> M := MatrixByEntries(GF(2), 2, 2, [[1, 2, 1], [2, 1, 1]]);;
gap> IsOne(M ^ 2);
true
gap> M := AntidiagonalMat(7, GF(9));;
gap> IsOne(M ^ 2);
true
gap> J := AntidiagonalMat(5, GF(7));;
gap> M := [ [ Z(7)^3, 0*Z(7), 0*Z(7), 0*Z(7), Z(7)^0 ], [ Z(7)^3, 0*Z(7), 0*Z(7), 0*Z(7), 0*Z(7) ], [ 0*Z(7), Z(7)^3, 0*Z(7), 0*Z(7), 0*Z(7) ], [ 0*Z(7), 0*Z(7), Z(7)^3, 0*Z(7), 0*Z(7) ], [ 0*Z(7), 0*Z(7), 0*Z(7), Z(7)^3, 0*Z(7) ] ];;
gap> RotateMat(M) = J * M * J;
true
gap> M := [[1, 2, 3], [4, 5, 6]];;
gap> RotateMat(M) = [[6, 5, 4 ], [3, 2, 1]];
true
gap> M := GL(7, 5 ^ 2).1;;
gap> N := ApplyFunctionToEntries(M, x -> x ^ 5);;
gap> M = ApplyFunctionToEntries(N, x -> x ^ 5);
true
gap> M := IdentityMat(4);;
gap> ReshapeMatrix(M, 2, 8);
[ [ 1, 0, 0, 0, 0, 1, 0, 0 ], [ 0, 0, 1, 0, 0, 0, 0, 1 ] ]
gap> M := IdentityMat(12, GF(7));;
gap> DimensionsMat(ReshapeMatrix(M, 48, 3));
[ 48, 3 ]
gap> M := GU(5, 7).1;;
gap> M = HermitianConjugate(HermitianConjugate(M, 7), 7);
true
gap> sol := SolveQuadraticCongruence(Z(7), 7);;
gap> sol.a ^ 2 + sol.b ^ 2 = Z(7);
true
gap> M := SquareSingleEntryMatrix(GF(9), 3, 1, 3);;
gap> IsZero(M ^ 2);
true
gap> QuoCeil(5, 3) = QuoCeil(6, 3);
true
gap> M := ReflectionMatrix(5, 9, AntidiagonalMat(5, GF(9)), "B", Z(9) ^ 0 * [1, 1, 1, 1, 1]);; 
gap> IsOne(M ^ 2);
true
gap> M := ReflectionMatrix(4, 4, AntidiagonalMat(Z(4) ^ 0 * [1, 1, 0, 0], GF(4)), "Q", Z(4) ^ 0 * [1, 1, 0, 1]);;
gap> IsOne(M ^ 2);
true
gap> x := SolveFrobeniusEquation("S", - Z(7) ^ 0, 7);;
gap> x + x ^ 7 = - Z(7) ^ 0;
true
gap> x := SolveFrobeniusEquation("P", - Z(7) ^ 0, 7);;
gap> x * x ^ 7 = - Z(7) ^ 0;
true

#
gap> TestFindGamma := function(q)
>   local gamma, R, x;
>   gamma := FindGamma(q);
>   R := PolynomialRing(GF(q), ["x"]);
>   x := Indeterminate(GF(q), "x");
>   Assert(0, IsIrreducibleRingElement(R, x ^ 2 + x + gamma));
> end;;
gap> TestFindGamma(8);
gap> TestFindGamma(2 ^ 7);
gap> TestFindGamma(2 ^ 13);

#
gap> TestSolveQuadraticEquation := function(args)
>   local F, a, b, c;
>   F := args[1];
>   a := args[2];
>   b := args[3];
>   c := args[4];
>   x := SolveQuadraticEquation(F, a, b, c);
>   Assert(0, IsZero(a * x ^ 2 + b * x + c));
> end;;
gap> TestSolveQuadraticEquation([GF(2), Z(2), 0 * Z(2), Z(2)]);
gap> TestSolveQuadraticEquation([GF(4), Z(4), Z(4) ^ 3, Z(4) ^ 2]);
gap> TestSolveQuadraticEquation([GF(2 ^ 19), Z(2 ^ 19) ^ 0, Z(2 ^ 19) ^ 113, Z(2 ^ 19) ^ (-1)]);

#
gap> TestFancySpinorNorm := function(args)
>   local epsilon, d, q, GroupOmega, GroupSO;
>   epsilon := args[1];
>   d := args[2];
>   q := args[3];
>   GroupOmega := Omega(epsilon, d, q);
>   GroupSO := SO(epsilon, d, q);
>   Assert(0, ForAll(GeneratorsOfGroup(GroupOmega), 
>                    gen -> FancySpinorNorm(InvariantBilinearForm(GroupOmega).matrix, GF(q), gen) = 1));
>   Assert(0, not ForAll(GeneratorsOfGroup(GroupSO), 
>                        gen -> FancySpinorNorm(InvariantBilinearForm(GroupSO).matrix, GF(q), gen) = -1));
> end;;
gap> TestFancySpinorNorm([0, 3, 7]);
gap> TestFancySpinorNorm([1, 4, 5]);
gap> TestFancySpinorNorm([1, 4, 8]);
gap> TestFancySpinorNorm([-1, 6, 4]);

#
gap> TestGeneratorsOfOrthogonalGroup := function(args)
>   local epsilon, n, q, F, zeta, gen, gens, rightDets, gramMatrix, rightForm;
>   epsilon := args[1];
>   n := args[2];
>   q := args[3];
>   F := GF(q);
>   zeta := PrimitiveElement(F);
>   gens := GeneratorsOfOrthogonalGroup(epsilon, n, q);
>   rightDets := true;
>   rightForm := true;
>   for gen in gens.generatorsOfSO do
>       if not IsOne(Determinant(gen)) then
>           rightDets := false;
>       fi;
>   od;
>   if not IsOne(- Determinant(gens.D)) then
>       rightDets := false;
>   fi;
>   if epsilon <> 0 then
>       if not Determinant(gens.E) = (epsilon * zeta) ^ (n / 2) then
>           rightDets := false;
>       fi;
>   fi;
>   if epsilon = 0 then
>       gramMatrix := IdentityMat(n, F);
>   elif epsilon = 1 then
>       gramMatrix := AntidiagonalMat(n, F);
>   elif epsilon = -1 then
>       if IsOddInt(n * (q - 1) / 4) then
>           gramMatrix := IdentityMat(n, F);
>       else
>           gramMatrix := IdentityMat(n, F);
>           gramMatrix[1, 1] := zeta;
>       fi;
>   fi;
>   for gen in Concatenation(gens.generatorsOfSO, [gens.D]) do
>       if not gen * gramMatrix * TransposedMat(gen) = gramMatrix then
>           rightForm := false;
>       fi;
>   od;
>   if epsilon = 0 then
>       if not gens.E * gramMatrix * TransposedMat(gens.E) = zeta ^ 2 * gramMatrix then
>           rightForm := false;
>       fi;
>   else
>       if not gens.E * gramMatrix * TransposedMat(gens.E) = zeta * gramMatrix then
>           rightForm := false;
>       fi;
>   fi;
>   return (rightDets and rightForm);
> end;;
gap> testsGeneratorsOfOrthogonalGroup := [[-1, 6, 7], [-1, 4, 9], [1, 4, 7], [0, 5, 5]];;
gap> ForAll(testsGeneratorsOfOrthogonalGroup, TestGeneratorsOfOrthogonalGroup);
true
gap> TestMatrixGroup := function(args)
>   local F, M, size, G, GWithSize;
>   F := args[1];
>   M := args[2];
>   size := args[3];
>   G := MatrixGroup(F, [M]);
>   GWithSize := MatrixGroupWithSize(F, [M], size);
>   return DefaultFieldOfMatrixGroup(G) = F
>          and DefaultFieldOfMatrixGroup(GWithSize) = F
>          and Size(GWithSize) = size;
> end;;
gap> testsMatrixGroup := [[GF(3 ^ 2), Z(3) * IdentityMat(2, GF(3)), 37],
>                         [GF(5 ^ 2), Z(5) * IdentityMat(2, GF(5)), 73]];;
gap> ForAll(testsMatrixGroup, TestMatrixGroup);
true

#
gap> for n in [2, 4 .. 10] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeSp(n, q) <> Size(Sp(n, q)) then Error("bad result for Sp(", n, ", ", q, ")"); fi; od; od;
gap> for n in [2, 4, 6] do for q in [2, 3, 4, 5, 7] do if SizePSp(n, q) <> Size(PSp(n, q)) then Error("bad result for PSp(", n, ", ", q, ")"); fi; od; od;
gap> for n in [2 .. 10] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeSU(n, q) <> Size(SU(n, q)) then Error("bad result for SU(", n, ", ", q, ")"); fi; od; od;
gap> for n in [2 .. 4] do for q in [2, 3, 4] do if SizePSU(n, q) <> Size(PSU(n, q)) then Error("bad result for PSU(", n, ", ", q, ")"); fi; od; od;
gap> for n in [2 .. 10] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeGU(n, q) <> Size(GU(n, q)) then Error("bad result for GU(", n, ", ", q, ")"); fi; od; od;
gap> for n in [3, 5 .. 9] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeGO(0, n, q) <> Size(GO(0, n, q)) then Error("bad result for GO(0, ", n, ", ", q, ")"); fi; od; od;
gap> for n in [2, 4 .. 10] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeGO(1, n, q) <> Size(GO(1, n, q)) then Error("bad result for GO(1, ", n, ", ", q, ")"); fi; od; od;
gap> for n in [2, 4 .. 10] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeGO(-1, n, q) <> Size(GO(-1, n, q)) then Error("bad result for GO(-1, ", n, ", ", q, ")"); fi; od; od;
gap> for n in [3, 5 .. 9] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeSO(0, n, q) <> Size(SO(0, n, q)) then Error("bad result for SO(0, ", n, ", ", q, ")"); fi; od; od;
gap> for n in [2, 4 .. 10] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeSO(1, n, q) <> Size(SO(1, n, q)) then Error("bad result for SO(1, ", n, ", ", q, ")"); fi; od; od;
gap> for n in [2, 4 .. 10] do for q in [2, 3, 4, 5, 7, 8, 9] do if SizeSO(-1, n, q) <> Size(SO(-1, n, q)) then Error("bad result for SO(1, ", n, ", ", q, ")"); fi; od; od;

#
gap> TestStandardGeneratorsOfOrthogonalGroup := function(epsilon, d, q)
>   local gens, generatorsOfOmega, S, G, D, standardForms, F, Q, field, one,
>   e, p, applyDToF, applyDToQ;
>   gens := StandardGeneratorsOfOrthogonalGroup(epsilon, d, q);
>   generatorsOfOmega := gens.generatorsOfOmega;
>   S := gens.S;
>   G := gens.G;
>   D := gens.D;
>   standardForms := StandardOrthogonalForm(epsilon, d, q);
>   F := standardForms.F;
>   Q := standardForms.Q;
>   field := GF(q);
>   one := One(field);
>   Assert(0, ForAll(generatorsOfOmega, g -> FancySpinorNorm(F, field, g) = 1));
>   Assert(0, S * F * TransposedMat(S) = F);
>   Assert(0, DiagonalOfMat(S * Q * TransposedMat(S)) = DiagonalOfMat(Q));
>   Assert(0, Determinant(S) = one);
>   Assert(0, FancySpinorNorm(F, field, S) = -1);
>   Assert(0, G * F * TransposedMat(G) = F);
>   Assert(0, DiagonalOfMat(G * Q * TransposedMat(G)) = DiagonalOfMat(Q));
>   Assert(0, Determinant(G) = -one);
>   e := DegreeOverPrimeField(field);
>   p := Root(q, e);
>   if IsEvenInt(q) or IsEvenInt(e) or p mod 8 = 1 or p mod 8 = 7 then
>       Assert(0, FancySpinorNorm(F, field, G) = 1);
>   else
>       Assert(0, FancySpinorNorm(F, field, G) = -1);
>   fi;
>   applyDToF := D * F * TransposedMat(D);
>   Assert(0, applyDToF * F[1, d] / applyDToF[1, d] = F);
>   applyDToQ := D * Q * TransposedMat(D);
>   Assert(0, DiagonalOfMat(applyDToQ * F[1, d] / applyDToF[1, d]) = DiagonalOfMat(Q)); 
> end;;
gap> TestStandardGeneratorsOfOrthogonalGroup(-1, 2, 7);
gap> TestStandardGeneratorsOfOrthogonalGroup(-1, 2, 5);
gap> TestStandardGeneratorsOfOrthogonalGroup(1, 6, 9);
gap> TestStandardGeneratorsOfOrthogonalGroup(-1, 6, 9);
gap> TestStandardGeneratorsOfOrthogonalGroup(0, 5, 11);
gap> TestStandardGeneratorsOfOrthogonalGroup(-1, 2, 8);
gap> TestStandardGeneratorsOfOrthogonalGroup(1, 6, 8);
gap> TestStandardGeneratorsOfOrthogonalGroup(-1, 6, 8);

#
gap> TestStandardGeneratorsOfLinearGroup := function(d, q)
>   local gens, field, one, zeta, entrySet, L1, L2, L3, S, G;
>   gens := StandardGeneratorsOfLinearGroup(d, q);
>   field := GF(q);
>   one := One(field);
>   zeta := PrimitiveElement(field);
>   entrySet := [Zero(field), one, -one, zeta, -zeta, zeta ^ (-1), -zeta ^ (-1)];
>   L1 := gens.L1;
>   L2 := gens.L2;
>   L3 := gens.L3;
>   S := MatrixGroup(field, [L1, L3]);
>   G := MatrixGroup(field, [L1, L2]);
>   CheckIsSubsetSL(d, q, S);
>   Assert(0, DimensionsMat(L2) = [d, d]);
>   Assert(0, DefaultFieldOfMatrix(L2) = field);
>   Assert(0, not Determinant(L2) in [0, 1]);
>   Assert(0, Size(S) = SizeSL(d, q));
>   Assert(0, Size(G) = SizeGL(d, q));
>   if IsOddInt(q) then
>       Assert(0, Size(Group(L1, L2^2)) = QuoInt(SizeGL(d, q), 2));
>   fi;
>   Assert(0, ForAll(L1, row -> IsSubset(entrySet, row)));
>   Assert(0, ForAll(L2, row -> IsSubset(entrySet, row)));
>   Assert(0, ForAll(L3, row -> IsSubset(entrySet, row)));
> end;;
gap> TestStandardGeneratorsOfLinearGroup(1, 2);
gap> TestStandardGeneratorsOfLinearGroup(1, 3);
gap> TestStandardGeneratorsOfLinearGroup(1, 4);
gap> TestStandardGeneratorsOfLinearGroup(1, 5);
gap> TestStandardGeneratorsOfLinearGroup(2, 2);
gap> TestStandardGeneratorsOfLinearGroup(2, 3);
gap> TestStandardGeneratorsOfLinearGroup(2, 4);
gap> TestStandardGeneratorsOfLinearGroup(2, 5);
gap> TestStandardGeneratorsOfLinearGroup(4, 2);
gap> TestStandardGeneratorsOfLinearGroup(4, 3);
gap> TestStandardGeneratorsOfLinearGroup(4, 4);
gap> TestStandardGeneratorsOfLinearGroup(4, 5);
gap> TestStandardGeneratorsOfLinearGroup(5, 2);
gap> TestStandardGeneratorsOfLinearGroup(5, 3);
gap> TestStandardGeneratorsOfLinearGroup(5, 4);
gap> TestStandardGeneratorsOfLinearGroup(5, 5);

# Test error handling
gap> StandardOrthogonalForm(2, 5, 5);
Error, <epsilon> must be one of -1, 0, 1
gap> StandardOrthogonalForm(0, 6, 5);
Error, <epsilon> must be one of -1 or 1 if <d> is even
gap> StandardOrthogonalForm(1, 5, 5);
Error, <epsilon> must be 0 if <d> is odd
gap> StandardOrthogonalForm(0, 5, 4);
Error, <d> must be even if <q> is even

#
gap> STOP_TEST("Utils.tst", 0);
