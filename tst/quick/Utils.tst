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
gap> M := ReflectionMatrix(5, 9, AntidiagonalMat(5, GF(9)), Z(9) ^ 0 * [1, 1, 1, 1, 1]);; 
gap> IsOne(M ^ 2);
true
gap> x := SolveFrobeniusEquation("S", - Z(7) ^ 0, 7);;
gap> x + x ^ 7 = - Z(7) ^ 0;
true
gap> x := SolveFrobeniusEquation("P", - Z(7) ^ 0, 7);;
gap> x * x ^ 7 = - Z(7) ^ 0;
true
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
