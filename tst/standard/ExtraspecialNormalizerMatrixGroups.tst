gap> r := 5;; m := 1;; q := 11;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 3;; m := 1;; q := 7;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 3;; m := 2;; q := 13;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 3;; q := 5;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 2;; q := 5;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 2;; q := 9;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 1;; q := 9;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 1;; q := 5;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 1;; q := 7;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> IsSubset(SL(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 5;; m := 1;; q := 4;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 3;; q := 3;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> r := 2;; m := 3;; q := 7;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> r := 2;; m := 2;; q := 3;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 2;; q := 7;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 3;; m := 2;; q := 5;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> r := 3;; m := 1;; q := 8;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 3;; m := 1;; q := 5;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> TestOddExtraspecialGroup := function(args)
>   local r, m, q, gens;
>   r := args[1];
>   m := args[2];
>   q := args[3];
>   gens := OddExtraspecialGroup(r, m, q);
>   return Size(Group(Concatenation(gens.listOfXi, gens.listOfYi))) = r ^ (2 * m + 1);
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
