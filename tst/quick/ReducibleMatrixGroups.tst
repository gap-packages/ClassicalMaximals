gap> n := 4;; q := 3;; k := 2;;
gap> G := SLStabilizerOfSubspace(n, q, k);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 8;; k := 2;;
gap> G := SLStabilizerOfSubspace(n, q, k);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 2;; q := 7;; k := 1;;
gap> G := SLStabilizerOfSubspace(n, q, k);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 3;; k := 2;;
gap> G := SUStabilizerOfIsotropicSubspace(n, q, k);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 5;; k := 1;;
gap> G := SUStabilizerOfIsotropicSubspace(n, q, k);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 4;; k := 1;;
gap> G := SUStabilizerOfIsotropicSubspace(n, q, k);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 3;; k := 1;;
gap> G := SUStabilizerOfIsotropicSubspace(n, q, k);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
