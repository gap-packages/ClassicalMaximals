gap> UnitaryForm(SU(4, 3)) = InvariantSesquilinearForm(SU(4, 3)).matrix;
true
gap> SymplecticForm(Sp(6, 7)) = InvariantBilinearForm(Sp(6, 7)).matrix;
true
gap> SymmetricBilinearForm(SO(5, 9)) = InvariantBilinearForm(SO(5, 9)).matrix;
true
gap> ConjugateToSesquilinearForm(SL(3, 4), "U", AntidiagonalMat(3, GF(4)));
Error, No preserved unitary form found for <group>
gap> ConjugateToSesquilinearForm(SL(3, 5), "O", IdentityMat(3, GF(5)));
Error, No preserved symmetric bilinear form found for <group>
gap> TestFormChangingFunctions := function(args)
>   local n, q, type, gramMatrix, standardGroup, conjugatedGroup, broadType,
>   standardGramMatrix, twiceConjugatedGroup;
>   n := args[1];
>   q := args[2];
>   type := args[3];
>   gramMatrix := args[4];
>   if type = "U" then
>       standardGroup := SU(n, q);
>   elif type = "S" then
>       standardGroup := Sp(n, q);
>   elif type = "O" then
>       standardGroup := SO(n, q);
>   elif type = "O+" then
>       standardGroup := SO(1, n, q);
>   elif type = "O-" then
>       standardGroup := SO(-1, n, q);
>   fi;
>   if type in ["O", "O+", "O-"] then
>       broadType := "O";
>   else
>       broadType := type;
>   fi;
>   conjugatedGroup := ConjugateToSesquilinearForm(standardGroup, broadType, gramMatrix);
>   if not IsEmpty(GeneratorsOfGroup(conjugatedGroup)) then
>       conjugatedGroup := Group(GeneratorsOfGroup(conjugatedGroup));
>   else
>       conjugatedGroup := Group(One(conjugatedGroup));
>   fi;
>   if type = "U" then
>       standardGramMatrix := InvariantSesquilinearForm(standardGroup).matrix;
>   else
>       standardGramMatrix := InvariantBilinearForm(standardGroup).matrix;
>   fi;
>   twiceConjugatedGroup := ConjugateToStandardForm(conjugatedGroup, type);
>   if type = "U" then
>       return ForAll(GeneratorsOfGroup(conjugatedGroup), 
>                     g -> g * gramMatrix * HermitianConjugate(g, q) = gramMatrix)
>              and ForAll(GeneratorsOfGroup(twiceConjugatedGroup), 
>                         g -> g * standardGramMatrix * HermitianConjugate(g, q) = standardGramMatrix);
>   else
>       return ForAll(GeneratorsOfGroup(conjugatedGroup),
>                     g -> g * gramMatrix * TransposedMat(g) = gramMatrix)
>              and ForAll(GeneratorsOfGroup(twiceConjugatedGroup),
>                         g -> g * standardGramMatrix * TransposedMat(g) = standardGramMatrix);
>   fi;
> end;;
gap> testsFormChangingFunctions := [[3, 7, "U", IdentityMat(3, GF(7))],
>                                   [6, 3, "S", AntidiagonalMat(Z(3) ^ 0 * [1, -1, 1, -1, 1, -1], GF(3))],
>                                   [5, 5, "O", IdentityMat(5, GF(5))],
>                                   [4, 7, "O+", AntidiagonalMat(4, GF(7))],
>                                   [4, 7, "O-", Z(7) ^ 0 * DiagonalMat([Z(7), 1, 1, 1])],
>                                   [6, 7, "O-", IdentityMat(6, GF(7))],
>                                   [1, 5, "O", IdentityMat(1, GF(5))],
>                                   [1, 5, "O", Z(5) * IdentityMat(1, GF(5))]];;
gap> ForAll(testsFormChangingFunctions, TestFormChangingFunctions);
true
