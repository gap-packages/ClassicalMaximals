gap> TestExtraspecialNormalizerInSL := function(args)
>   local r, m, q, G;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   G := ExtraspecialNormalizerInSL(r, m, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
gap> testsExtraspecialNormalizerInSL := [[5, 1, 11], [3, 1, 7], [3, 2, 13], [2, 3, 5], [2, 2, 5], 
>                                        [2, 2, 9], [2, 1, 9], [2, 1, 5], [2, 1, 7]];;
gap> ForAll(testsExtraspecialNormalizerInSL, TestExtraspecialNormalizerInSL);
true
gap> TestExtraspecialNormalizerInSU := function(args)
>   local r, m, q, G;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   G := ExtraspecialNormalizerInSU(r, m, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsExtraspecialNormalizerInSU := [[5, 1, 4], [2, 3, 3], [2, 3, 7], [2, 2, 3], [2, 2, 7], 
>                                        [3, 2, 5], [3, 1, 8], [3, 1, 5]];;
#@else
gap> testsExtraspecialNormalizerInSU := [[2, 3, 3], [3, 2, 5], [3, 1, 8], [3, 1, 5]];;
#@fi
gap> ForAll(testsExtraspecialNormalizerInSU, TestExtraspecialNormalizerInSU);
true
gap> TestOddExtraspecialGroup := function(args)
>   local r, m, q, gens, G;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   gens := OddExtraspecialGroup(r, m, q);
>   G := Group(Concatenation(gens.listOfXi, gens.listOfYi));
>   RECOG.TestGroup(G, false, r ^ (2 * m + 1));
>   return true;
> end;;
gap> testsOddExtraspecialGroup := [[5, 1, 11], [3, 1, 7], [3, 2, 13]];;
gap> ForAll(testsOddExtraspecialGroup, TestOddExtraspecialGroup);
true
gap> TestOddExtraspecialNormalizerInGL := function(args)
>   local r, m, q, gensNormalizer, gensExtraspecial, extraspecialGroup,
>   normalizer;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   gensNormalizer := OddExtraspecialNormalizerInGL(r, m, q);
>   gensExtraspecial := OddExtraspecialGroup(r, m, q);
>   extraspecialGroup := Group(Concatenation(gensExtraspecial.listOfXi,
>                                            gensExtraspecial.listOfYi));
>   normalizer := Group(Concatenation(gensNormalizer.listOfXi,
>                                     gensNormalizer.listOfYi,
>                                     gensNormalizer.listOfUi,
>                                     gensNormalizer.listOfVi,
>                                     gensNormalizer.listOfWi,
>                                     [gensNormalizer.generatingScalar]));
>   return ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup);
> end;;
gap> testsOddExtraspecialNormalizerInGL := [[5, 1, 11], [3, 1, 7], [3, 2, 13]];;
gap> ForAll(testsOddExtraspecialNormalizerInGL, TestOddExtraspecialNormalizerInGL);
true
gap> TestSymplecticTypeNormalizerInGL := function(args)
>   local r, m, q, gensNormalizer, gensExtraspecial, extraspecialGroup,
>   normalizer, zeta, F;
>   r := 2;
>   m := args[1];
>   q := args[2];
>   F := GF(q);
>   zeta := PrimitiveElement(F);
>   gensNormalizer := SymplecticTypeNormalizerInGL(m, q);
>   gensExtraspecial := OddExtraspecialGroup(r, m, q);
>   extraspecialGroup := Group(Concatenation(gensExtraspecial.listOfXi,
>                                            gensExtraspecial.listOfYi,
>                                            [zeta ^ ((q - 1) / 4) * IdentityMat(r ^ m, F)]));
>   normalizer := Group(Concatenation(gensNormalizer.listOfXi,
>                                     gensNormalizer.listOfYi,
>                                     gensNormalizer.listOfUi,
>                                     gensNormalizer.listOfVi,
>                                     gensNormalizer.listOfWi,
>                                     [gensNormalizer.generatingScalar]));
>   return ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup);
> end;;
gap> testsSymplecticTypeNormalizerInGL := [[3, 5], [2, 5], [2, 9]];;
gap> ForAll(testsSymplecticTypeNormalizerInGL, TestSymplecticTypeNormalizerInGL);
true
gap> TestExtraspecial2MinusTypeNormalizerInGL := function(args)
>   local r, m, q, gensNormalizer, extraspecialGroup, normalizer, zeta, F;
>   r := 2;
>   m := args[1];
>   q := args[2];
>   F := GF(q);
>   zeta := PrimitiveElement(F);
>   gensNormalizer := Extraspecial2MinusTypeNormalizerInGL(m, q);
>   extraspecialGroup := Group(Concatenation(gensNormalizer.listOfXi,
>                                            gensNormalizer.listOfYi));
>   normalizer := Group(Concatenation(gensNormalizer.listOfXi,
>                                     gensNormalizer.listOfYi,
>                                     gensNormalizer.listOfUi,
>                                     gensNormalizer.listOfVi,
>                                     gensNormalizer.listOfWi,
>                                     [gensNormalizer.generatingScalar]));
>   return ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup);
> end;;
gap> testsExtraspecial2MinusTypeNormalizerInGL := [[1, 9], [1, 5], [1, 7], [2, 5]];;
gap> ForAll(testsExtraspecial2MinusTypeNormalizerInGL, TestExtraspecial2MinusTypeNormalizerInGL);
true
