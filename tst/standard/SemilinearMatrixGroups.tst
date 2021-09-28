gap> n := 4;; q := 3;; s := 2;;
gap> G := GammaLMeetSL(n, q, s);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 2;; q := 2;; s := 2;;
gap> G := GammaLMeetSL(n, q, s);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 6;; q := 5;; s := 3;;
gap> G := GammaLMeetSL(n, q, s);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 4;; s := 3;;
gap> G := GammaLMeetSL(n, q, s);;
gap> IsSubset(SL(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
