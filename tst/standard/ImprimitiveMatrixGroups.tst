gap> TestImprimitivesMeetSL := function(args)
>   local n, q, t, G;
>   n := args[1];
>   q := args[2];
>   t := args[3];
>   G := ImprimitivesMeetSL(n, q, t);
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G))
>          and Size(Group(GeneratorsOfGroup(G))) = Size(G);
> end;;
gap> testsImprimitivesMeetSL := [[2, 3, 2], [4, 8, 2], [6, 5, 3]];;
gap> ForAll(testsImprimitivesMeetSL, TestImprimitivesMeetSL);
true
gap> TestSUIsotropicImprimitives := function(args)
>   local n, q, G;
>   n := args[1];
>   q := args[2];
>   G := SUIsotropicImprimitives(n, q);
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and Size(Group(GeneratorsOfGroup(G))) = Size(G);
> end;;
gap> testsSUIsotropicImprimitives := [[6, 2], [4, 3], [2, 5]];;
gap> ForAll(testsSUIsotropicImprimitives, TestSUIsotropicImprimitives);
true
gap> TestSUNonDegenerateImprimitives := function(args)
>   local n, q, t, G;
>   n := args[1];
>   q := args[2];
>   t := args[3];
>   G := SUNonDegenerateImprimitives(n, q, t);
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and Size(Group(GeneratorsOfGroup(G))) = Size(G);
> end;;
gap> testsSUNonDegenerateImprimitives := [[6, 3, 3], [9, 2, 3], [3, 5, 3]];;
gap> ForAll(testsSUNonDegenerateImprimitives, TestSUNonDegenerateImprimitives);
true
