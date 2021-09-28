gap> n := 2;; q := 3;; t := 2;;
gap> G := ImprimitivesMeetSL(n, q, t);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 8;; t := 2;;
gap> G := ImprimitivesMeetSL(n, q, t);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 6;; q := 5;; t := 3;;
gap> G := ImprimitivesMeetSL(n, q, t);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 6;; q := 2;;
gap> G := SUIsotropicImprimitives(n, q);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 3;;
gap> G := SUIsotropicImprimitives(n, q);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 2;; q := 5;;
gap> G := SUIsotropicImprimitives(n, q);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 6;; q := 3;; t := 3;;
gap> G := SUNonDegenerateImprimitives(n, q, t);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 9;; q := 2;; t := 3;;
gap> G := SUNonDegenerateImprimitives(n, q, t);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 5;; t := 3;;
gap> G := SUNonDegenerateImprimitives(n, q, t);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
