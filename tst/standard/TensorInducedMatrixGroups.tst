gap> m := 3;; t := 2;; q := 5;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> IsSubset(SL(m ^ t, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 2;; t := 2;; q := 7;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> IsSubset(SL(m ^ t, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 2;; t := 2;; q := 5;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> IsSubset(SL(m ^ t, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 3;; t := 3;; q := 3;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> IsSubset(SL(m ^ t, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 2;; t := 2;; q := 7;;
gap> G := TensorInducedDecompositionStabilizerInSU(m, t, q);;
gap> IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 2;; t := 2;; q := 5;;
gap> G := TensorInducedDecompositionStabilizerInSU(m, t, q);;
gap> IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 3;; t := 2;; q := 3;;
gap> G := TensorInducedDecompositionStabilizerInSU(m, t, q);;
gap> IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 3;; t := 3;; q := 3;;
gap> G := TensorInducedDecompositionStabilizerInSU(m, t, q);;
gap> IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G));
true
gap> m := 3;; t := 2;; q := 5;;
gap> G := TensorInducedDecompositionStabilizerInSU(m, t, q);;
gap> IsSubset(SU(m ^ t, q), GeneratorsOfGroup(G));
true
