gap> n := 4;; q := 3;;
gap> G := SymplecticNormalizerInSL(n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 5;;
gap> G := SymplecticNormalizerInSL(n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 6;; q := 4;;
gap> G := SymplecticNormalizerInSL(n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 9;;
gap> G := UnitaryNormalizerInSL(n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 9;;
gap> G := UnitaryNormalizerInSL(n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 4;;
gap> G := UnitaryNormalizerInSL(n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := 0;; n := 3;; q := 5;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := -1;; n := 6;; q := 5;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := 1;; n := 6;; q := 5;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := -1;; n := 4;; q := 3;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := 1;; n := 4;; q := 3;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := -1;; n := 4;; q := 5;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := 1;; n := 4;; q := 5;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> epsilon := -1;; n := 6;; q := 3;;
gap> G := OrthogonalNormalizerInSL(epsilon, n, q);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
