gap> START_TEST("Utils.tst");

#
gap> M := MatrixByEntries(GF(2), 2, 2, [[1, 2, 1], [2, 1, 1]]);;
gap> IsOne(M ^ 2);
true
gap> M := AntidiagonalMat(7, GF(9));;
gap> IsOne(M ^ 2);
true
gap> M := GL(7, 5 ^ 2).1;;
gap> N := ApplyFunctionToEntries(M, x -> x ^ 5);;
gap> M = ApplyFunctionToEntries(N, x -> x ^ 5);
true
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
gap> x := SolveFrobeniusEquation("S", - Z(7) ^ 0, 7);;
gap> x + x ^ 7 = - Z(7) ^ 0;
true
gap> x := SolveFrobeniusEquation("P", - Z(7) ^ 0, 7);;
gap> x * x ^ 7 = - Z(7) ^ 0;
true
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
gap> STOP_TEST("Utils.tst", 0);
