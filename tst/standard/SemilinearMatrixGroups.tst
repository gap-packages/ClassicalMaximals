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
gap> n := 3;; q := 5;; s := 3;;
gap> G := GammaLMeetSU(n, q, s);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 6;; q := 3;; s := 3;;
gap> G := GammaLMeetSU(n, q, s);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 7;; s := 3;;
gap> G := GammaLMeetSU(n, q, s);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> TestGammaLDimension1 := function(args)
>   local q, s, gens;
>   q := args[1];
>   s := args[2];
>   gens := GammaLDimension1(s, q);
>   return Order(gens.A) = (q ^ s - 1) and Order(gens.B) = s;
> end;;
gap> testsGammaLDimension1 := [[3, 2], [2, 2], [5, 3], [4, 3]];;
gap> ForAll(testsGammaLDimension1, TestGammaLDimension1);
true
