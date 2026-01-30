gap> START_TEST("Forms.tst");

#
gap> UnitaryForm(SU(4, 3), GF(3^2)) = InvariantSesquilinearForm(SU(4, 3)).matrix;
true
gap> G := Group([ [ [ Z(79^2)^4792, Z(79^2)^2120, Z(79^2)^3243, Z(79^2)^5635, Z(79^2)^651, Z(79^2)^4635, Z(79^2)^2274, Z(79^2)^952 ],
>   [ Z(79^2)^3905, Z(79^2)^3703, Z(79^2)^4458, Z(79^2)^2635, Z(79^2)^3474, Z(79^2)^4535, Z(79^2)^1707, Z(79^2)^2019 ],
>   [ Z(79^2)^4432, Z(79^2)^6170, Z(79^2)^492, Z(79^2)^3162, Z(79^2)^3774, Z(79^2)^4963, Z(79^2)^3448, Z(79^2)^652 ],
>   [ Z(79^2)^1947, Z(79^2)^1686, Z(79^2)^2500, Z(79^2)^677, Z(79^2)^161, Z(79^2)^251, Z(79^2)^753, Z(79^2)^687 ],
>   [ Z(79^2)^4352, Z(79^2)^2370, Z(79^2)^4247, Z(79^2)^2882, Z(79^2)^3921, Z(79^2)^1772, Z(79^2)^903, Z(79^2)^799 ],
>   [ Z(79^2)^3732, Z(79^2)^5413, Z(79^2)^2541, Z(79^2)^4969, Z(79^2)^3301, Z(79^2)^1152, Z(79^2)^2931, Z(79^2)^179 ],
>   [ Z(79^2)^4647, Z(79^2)^4047, Z(79^2)^1691, Z(79^2)^3377, Z(79^2)^873, Z(79^2)^1872, Z(79^2)^3560, Z(79^2)^3991 ],
>   [ Z(79^2)^6125, Z(79^2)^6030, Z(79^2)^1657, Z(79^2)^5122, Z(79^2)^6140, Z(79^2)^3681, Z(79^2)^2524, Z(79^2)^4362 ] ],
> [ [ Z(79^2)^2964, Z(79)^50, Z(79^2)^1428, Z(79^2)^4324, Z(79^2)^3844, Z(79^2)^5896, Z(79^2)^917, Z(79^2)^878 ],
>   [ Z(79^2)^3713, Z(79^2)^6036, Z(79^2)^5845, Z(79^2)^5597, Z(79^2)^2006, Z(79^2)^2678, Z(79^2)^2419, Z(79)^27 ],
>   [ Z(79^2)^1413, Z(79^2)^1535, Z(79^2)^4977, Z(79^2)^3608, Z(79^2)^923, Z(79^2)^5012, Z(79^2)^3830, Z(79^2)^1907 ],
>   [ Z(79^2)^3053, Z(79^2)^4393, Z(79^2)^4438, Z(79^2)^200, Z(79^2)^642, Z(79^2)^6058, Z(79^2)^4498, Z(79)^38 ],
>   [ Z(79^2)^1074, Z(79^2)^3370, Z(79^2)^6204, Z(79^2)^4860, Z(79^2)^245, Z(79^2)^2146, Z(79^2)^512, Z(79^2)^366 ],
>   [ Z(79^2)^4052, Z(79^2)^4032, Z(79^2)^5337, Z(79^2)^1838, Z(79^2)^2695, Z(79^2)^3927, Z(79^2)^1585, Z(79^2)^4590 ],
>   [ Z(79^2)^5990, Z(79^2)^5607, Z(79^2)^3478, Z(79)^59, Z(79^2)^2933, Z(79^2)^2393, Z(79^2)^4820, Z(79^2)^768 ],
>   [ Z(79^2)^1228, Z(79^2)^4621, Z(79^2)^1975, Z(79^2)^799, Z(79^2)^4455, Z(79^2)^2716, Z(79^2)^5986, Z(79^2)^4359 ] ] ]);;
gap> M := UnitaryForm(G, GF(79^2));;  # for this group, the unitary form was not reliably found
gap> Assert(0, ForAll(GeneratorsOfGroup(G), g -> g * M * HermitianConjugate(g, 79) = M));
gap> SymplecticForm(Sp(6, 7), GF(7)) = InvariantBilinearForm(Sp(6, 7)).matrix;
true
gap> SymmetricBilinearForm(SO(5, 9), GF(9)) = InvariantBilinearForm(SO(5, 9)).matrix;
true
gap> ConjugateToSesquilinearForm(SL(3, 4), "U", AntidiagonalMat(3, GF(4)), GF(4));
Error, No preserved unitary form found for <group>
gap> ConjugateToSesquilinearForm(SL(3, 5), "O-B", IdentityMat(3, GF(5)), GF(5));
Error, No preserved symmetric bilinear form found for <group>
gap> TestFormChangingFunctions := function(args)
>   local n, q, type, gramMatrix, standardGroup, conjugatedGroup, broadType,
>   standardGramMatrix, twiceConjugatedGroup, polarForm, standardPolarForm;
>   n := args[1];
>   q := args[2];
>   type := args[3];
>   gramMatrix := args[4];
>   if type = "U" then
>       standardGroup := SU(n, q); q:=q^2;
>   elif type = "S" then
>       standardGroup := Sp(n, q);
>   elif type = "O" then
>       standardGroup := Omega(n, q);
>   elif type = "O+" then
>       standardGroup := Omega(1, n, q);
>   elif type = "O-" then
>       standardGroup := Omega(-1, n, q);
>   fi;
>   if type in ["O", "O+", "O-"] then
>       if IsOddInt(q) then
>           broadType := "O-B";
>       else
>           broadType := "O-Q";
>       fi;
>   else
>       broadType := type;
>   fi;
>   conjugatedGroup := ConjugateToSesquilinearForm(standardGroup, broadType, gramMatrix, GF(q));
>   if not IsEmpty(GeneratorsOfGroup(conjugatedGroup)) then
>       conjugatedGroup := Group(GeneratorsOfGroup(conjugatedGroup));
>   else
>       conjugatedGroup := Group(One(conjugatedGroup));
>   fi;
>   if type = "U" then
>       standardGramMatrix := InvariantSesquilinearForm(standardGroup).matrix;
>   elif IsOddInt(q) then
>       standardGramMatrix := InvariantBilinearForm(standardGroup).matrix;
>   else
>       polarForm := gramMatrix + TransposedMat(gramMatrix);
>       standardGramMatrix := InvariantQuadraticForm(standardGroup).matrix;
>       standardPolarForm := InvariantBilinearForm(standardGroup).matrix;
>   fi;
>   twiceConjugatedGroup := ConjugateToStandardForm(conjugatedGroup, type, GF(q));
>   if type = "U" then
>       q := RootInt(q);
>       Assert(0, ForAll(GeneratorsOfGroup(conjugatedGroup), 
>                        g -> g * gramMatrix * HermitianConjugate(g, q) = gramMatrix));
>       Assert(0, ForAll(GeneratorsOfGroup(twiceConjugatedGroup), 
>                        g -> g * standardGramMatrix * HermitianConjugate(g, q) = standardGramMatrix));
>   elif IsOddInt(q) then
>       Assert(0, ForAll(GeneratorsOfGroup(conjugatedGroup),
>                        g -> g * gramMatrix * TransposedMat(g) = gramMatrix));
>       Assert(0, ForAll(GeneratorsOfGroup(twiceConjugatedGroup),
>                        g -> g * standardGramMatrix * TransposedMat(g) = standardGramMatrix));
>   else
>       Assert(0, ForAll(GeneratorsOfGroup(conjugatedGroup), 
>                        g -> (g * polarForm * TransposedMat(g) = polarForm 
>                              and DiagonalOfMat(g * gramMatrix * TransposedMat(g)) 
>                                  = DiagonalOfMat(gramMatrix))));
>       Assert(0, ForAll(GeneratorsOfGroup(twiceConjugatedGroup),
>                        g -> (g * standardPolarForm * TransposedMat(g) = standardPolarForm
>                              and DiagonalOfMat(g * standardGramMatrix * TransposedMat(g)) 
>                                  = DiagonalOfMat(standardGramMatrix))));
>   fi;
> end;;
gap> TestFormChangingFunctions([3, 7, "U", IdentityMat(3, GF(7))]);
gap> TestFormChangingFunctions([6, 3, "S", AntidiagonalMat(Z(3) ^ 0 * [1, -1, 1, -1, 1, -1], GF(3))]);
gap> TestFormChangingFunctions([5, 5, "O", IdentityMat(5, GF(5))]);
gap> TestFormChangingFunctions([4, 7, "O+", AntidiagonalMat(4, GF(7))]);
gap> TestFormChangingFunctions([4, 7, "O-", Z(7) ^ 0 * DiagonalMat([Z(7), 1, 1, 1])]);
gap> TestFormChangingFunctions([6, 7, "O-", IdentityMat(6, GF(7))]);
gap> TestFormChangingFunctions([1, 5, "O", IdentityMat(1, GF(5))]);
gap> TestFormChangingFunctions([1, 5, "O", Z(5) * IdentityMat(1, GF(5))]);
gap> TestFormChangingFunctions([2, 2, "O-", Z(2) ^ 0 * [[1, 1], [0, 1]]]);
gap> TestFormChangingFunctions([6, 4, "O+", AntidiagonalMat(Z(4) ^ 0 * [1, 1, 1, 0, 0, 0], GF(4))]);
gap> Q := QuadraticForm(Group(GeneratorsOfGroup(SO(5, 5))), GF(5));;
gap> Q / Q[5, 5] = InvariantQuadraticForm(SO(5, 5)).matrix;
true
gap> TestStandardOrthogonalForm := function(epsilon, d, q)
>   local standardForm;
>   standardForm := StandardOrthogonalForm(epsilon, d, q);
>   Assert(0, standardForm.F = standardForm.Q + TransposedMat(standardForm.Q));
> end;;
gap> TestStandardOrthogonalForm(0, 5, 7);
gap> TestStandardOrthogonalForm(1, 6, 9);
gap> TestStandardOrthogonalForm(-1, 6, 9);
gap> TestStandardOrthogonalForm(-1, 6, 4);

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
gap> STOP_TEST("Forms.tst", 0);
