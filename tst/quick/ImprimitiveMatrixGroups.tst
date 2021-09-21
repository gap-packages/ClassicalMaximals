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
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 3;;
gap> G := SUIsotropicImprimitives(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 2;; q := 5;;
gap> G := SUIsotropicImprimitives(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
