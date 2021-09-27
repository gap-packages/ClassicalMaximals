gap> r := 5;; m := 1;; q := 11;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 3;; m := 1;; q := 7;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 3;; m := 2;; q := 13;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 3;; q := 5;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 2;; q := 5;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 2;; q := 9;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 1;; q := 9;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 1;; q := 5;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> r := 2;; m := 1;; q := 7;;
gap> G := ExtraspecialNormalizerInSL(r, m, q);;
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
gap> r := 3;; m := 2;; q := 5;;
gap> G := ExtraspecialNormalizerInSU(r, m, q);;
gap> IsSubset(SU(r ^ m, q), GeneratorsOfGroup(G));
true
