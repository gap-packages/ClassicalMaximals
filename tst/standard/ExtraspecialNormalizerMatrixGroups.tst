gap> START_TEST("ExtraspecialNormalizerMatrixGroups.tst");

#
gap> TestExtraspecialNormalizerInSL := function(r, m, q)
>   local G;
>   G := ExtraspecialNormalizerInSL(r, m, q);
>   CheckIsSubsetSL(r ^ m, q, G);
>   CheckSize(G);
> end;;
gap> TestExtraspecialNormalizerInSL(5, 1, 11);
gap> TestExtraspecialNormalizerInSL(3, 1, 7);
gap> TestExtraspecialNormalizerInSL(3, 2, 13);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInSL(2, 3, 5); # FIXME: `Giving up, Schreier tree is not shallow.`
#@fi
gap> TestExtraspecialNormalizerInSL(2, 2, 5);
gap> TestExtraspecialNormalizerInSL(2, 2, 9);
gap> TestExtraspecialNormalizerInSL(2, 1, 9);
gap> TestExtraspecialNormalizerInSL(2, 1, 5);
gap> TestExtraspecialNormalizerInSL(2, 1, 7);

#
gap> TestExtraspecialNormalizerInSU := function(r, m, q)
>   local G;
>   G := ExtraspecialNormalizerInSU(r, m, q);
>   CheckIsSubsetSU(r ^ m, q, G);
>   CheckSize(G);
> end;;
gap> TestExtraspecialNormalizerInSU(5, 1, 4);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInSU(2, 3, 3); # FIXME: `Giving up, Schreier tree is not shallow.`
gap> TestExtraspecialNormalizerInSU(2, 3, 7); # FIXME: `Error, the recognition described by this recognition node has failed!`
#@fi
gap> TestExtraspecialNormalizerInSU(2, 2, 3);
gap> TestExtraspecialNormalizerInSU(2, 2, 7);
gap> TestExtraspecialNormalizerInSU(3, 2, 5);
gap> TestExtraspecialNormalizerInSU(3, 1, 8);
gap> TestExtraspecialNormalizerInSU(3, 1, 5);

#
gap> TestExtraspecialNormalizerInSp := function(m, q)
>   local G;
>   G := ExtraspecialNormalizerInSp(m, q);
>   CheckIsSubsetSp(2 ^ m, q, G);
>   CheckSize(G);
> end;;
gap> TestExtraspecialNormalizerInSp(2, 3);
gap> TestExtraspecialNormalizerInSp(2, 5);
gap> TestExtraspecialNormalizerInSp(2, 7);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInSp(3, 3); # FIXME: `Error, the recognition described by this recognition node has failed!`
gap> TestExtraspecialNormalizerInSp(3, 5); # FIXME: runs out of memory or `Error, This should never have happened (346), tell Max`
gap> TestExtraspecialNormalizerInSp(3, 7); # FIXME: `Error, the recognition described by this recognition node has failed!`
#@fi

#
gap> TestOddExtraspecialGroup := function(r, m, q)
>   local gens, G;
>   gens := OddExtraspecialGroup(r, m, q);
>   G := Group(Concatenation(gens.listOfXi, gens.listOfYi));
>   RECOG.TestGroup(G, false, r ^ (2 * m + 1));
> end;;
gap> TestOddExtraspecialGroup(5, 1, 11);
gap> TestOddExtraspecialGroup(3, 1, 7);
gap> TestOddExtraspecialGroup(3, 2, 13);

#
gap> TestOddExtraspecialNormalizerInGL := function(r, m, q)
>   local gensNormalizer, gensExtraspecial, extraspecialGroup, normalizer;
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
>   Assert(0, ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup));
> end;;
gap> TestOddExtraspecialNormalizerInGL(5, 1, 11);
gap> TestOddExtraspecialNormalizerInGL(3, 1, 7);
gap> TestOddExtraspecialNormalizerInGL(3, 2, 13);

#
gap> TestSymplecticTypeNormalizerInGL := function(m, q)
>   local r, gensNormalizer, gensExtraspecial, extraspecialGroup,
>   normalizer, zeta, F;
>   r := 2;
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
>   Assert(0, ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup));
> end;;
gap> TestSymplecticTypeNormalizerInGL(3, 5);
gap> TestSymplecticTypeNormalizerInGL(2, 5);
gap> TestSymplecticTypeNormalizerInGL(2, 9);

#
gap> TestExtraspecial2MinusTypeNormalizerInGL := function(m, q)
>   local r, gensNormalizer, extraspecialGroup, normalizer, zeta, F;
>   r := 2;
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
>   Assert(0, ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup));
> end;;
gap> TestExtraspecial2MinusTypeNormalizerInGL(1, 9);
gap> TestExtraspecial2MinusTypeNormalizerInGL(1, 5);
gap> TestExtraspecial2MinusTypeNormalizerInGL(1, 7);
gap> TestExtraspecial2MinusTypeNormalizerInGL(2, 5);

#
gap> TestExtraspecialNormalizerInOmega := function(m, q)
>   local G;
>   G := ExtraspecialNormalizerInOmega(m, q);
>   CheckIsSubsetOmega(1, 2 ^ m, q, G);
>   CheckSize(G);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInOmega(3, 3); # FIXME: 'Error, the recognition described by this recognition node has failed!' or 'Error, This should never have happened (346), tell Max.'
#@fi
gap> TestExtraspecialNormalizerInOmega(3, 5);
gap> TestExtraspecialNormalizerInOmega(3, 7);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInOmega(4, 3); # FIXME: 'Error, the recognition described by this recognition node has failed!'
#@fi
gap> TestExtraspecialNormalizerInOmega(4, 5);

# Test error handling
gap> ExtraspecialNormalizerInOmega(2, 5);
Error, 2 ^ <m> must be at least 8 in the orthogonal case
gap> ExtraspecialNormalizerInOmega(3, 4);
Error, <r> must be prime and a divisor of <q> - 1

#
gap> STOP_TEST("ExtraspecialNormalizerMatrixGroups.tst", 0);
