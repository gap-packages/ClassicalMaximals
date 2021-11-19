gap> START_TEST("ExtraspecialNormalizerMatrixGroups.tst");

#
gap> TestExtraspecialNormalizerInSL := function(args)
>   local r, m, q, G, hasSize;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   G := ExtraspecialNormalizerInSL(r, m, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestExtraspecialNormalizerInSL([5, 1, 11]);
gap> TestExtraspecialNormalizerInSL([3, 1, 7]);
gap> TestExtraspecialNormalizerInSL([3, 2, 13]);
gap> TestExtraspecialNormalizerInSL([2, 3, 5]);
gap> TestExtraspecialNormalizerInSL([2, 2, 5]);
gap> TestExtraspecialNormalizerInSL([2, 2, 9]);
gap> TestExtraspecialNormalizerInSL([2, 1, 9]);
gap> TestExtraspecialNormalizerInSL([2, 1, 5]);
gap> TestExtraspecialNormalizerInSL([2, 1, 7]);

#
gap> TestExtraspecialNormalizerInSU := function(args)
>   local r, m, q, G, hasSize;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   G := ExtraspecialNormalizerInSU(r, m, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   Assert(0, hasSize);
> end;;
gap> TestExtraspecialNormalizerInSU([5, 1, 4]);
gap> TestExtraspecialNormalizerInSU([2, 3, 3]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInSU([2, 3, 7]); # FIXME: `Giving up, Schreier tree is not shallow.`
gap> TestExtraspecialNormalizerInSU([2, 2, 3]); # FIXME: `Error, the recognition described by this recognition node has failed!`
#@fi
gap> TestExtraspecialNormalizerInSU([2, 2, 7]);
gap> TestExtraspecialNormalizerInSU([3, 2, 5]);
gap> TestExtraspecialNormalizerInSU([3, 1, 8]);
gap> TestExtraspecialNormalizerInSU([3, 1, 5]);

#
gap> TestExtraspecialNormalizerInSp := function(args)
>   local m, q, G, hasSize;
>   m := args[1];
>   q := args[2];
>   G := ExtraspecialNormalizerInSp(m, q);
>   hasSize := HasSize(G);
>   RECOG.TestGroup(G, false, Size(G));
>   Assert(0, IsSubset(Sp(2 ^ m, q), GeneratorsOfGroup(G)));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   Assert(0, hasSize);
> end;;
gap> TestExtraspecialNormalizerInSp([2, 3]);
gap> TestExtraspecialNormalizerInSp([2, 5]);
gap> TestExtraspecialNormalizerInSp([2, 7]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInSp([3, 3]); # FIXME: `Error, the recognition described by this recognition node has failed!`
#@fi
gap> TestExtraspecialNormalizerInSp([3, 5]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestExtraspecialNormalizerInSp([3, 7]); # FIXME: `Error, the recognition described by this recognition node has failed!`
#@fi

#
gap> TestOddExtraspecialGroup := function(args)
>   local r, m, q, gens, G;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   gens := OddExtraspecialGroup(r, m, q);
>   G := Group(Concatenation(gens.listOfXi, gens.listOfYi));
>   RECOG.TestGroup(G, false, r ^ (2 * m + 1));
> end;;
gap> TestOddExtraspecialGroup([5, 1, 11]);
gap> TestOddExtraspecialGroup([3, 1, 7]);
gap> TestOddExtraspecialGroup([3, 2, 13]);

#
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
>   Assert(0, ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup));
> end;;
gap> TestOddExtraspecialNormalizerInGL([5, 1, 11]);
gap> TestOddExtraspecialNormalizerInGL([3, 1, 7]);
gap> TestOddExtraspecialNormalizerInGL([3, 2, 13]);

#
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
>   Assert(0, ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup));
> end;;
gap> TestSymplecticTypeNormalizerInGL([3, 5]);
gap> TestSymplecticTypeNormalizerInGL([2, 5]);
gap> TestSymplecticTypeNormalizerInGL([2, 9]);

#
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
>   Assert(0, ForAll(GeneratorsOfGroup(normalizer), g -> extraspecialGroup ^ g = extraspecialGroup));
> end;;
gap> TestExtraspecial2MinusTypeNormalizerInGL([1, 9]);
gap> TestExtraspecial2MinusTypeNormalizerInGL([1, 5]);
gap> TestExtraspecial2MinusTypeNormalizerInGL([1, 7]);
gap> TestExtraspecial2MinusTypeNormalizerInGL([2, 5]);

#
gap> STOP_TEST("ExtraspecialNormalizerMatrixGroups.tst", 0);
