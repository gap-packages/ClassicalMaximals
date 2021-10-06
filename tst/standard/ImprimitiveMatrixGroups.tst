gap> TestImprimitivesMeetSL := function(args)
>   local n, q, t, G;
>   n := args[1];
>   q := args[2];
>   t := args[3];
>   G := ImprimitivesMeetSL(n, q, t);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsImprimitivesMeetSL := [[2, 3, 2], [4, 8, 2], [6, 5, 3]];;
#@else
gap> testsImprimitivesMeetSL := [[2, 3, 2], [6, 5, 3]];;
#@fi
gap> ForAll(testsImprimitivesMeetSL, TestImprimitivesMeetSL);
true
gap> TestSUIsotropicImprimitives := function(args)
>   local n, q, G;
>   n := args[1];
>   q := args[2];
>   G := SUIsotropicImprimitives(n, q);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> testsSUIsotropicImprimitives := [[6, 2], [4, 3], [2, 5]];;
#@else
gap> testsSUIsotropicImprimitives := [[6, 2]];;
#@fi
gap> ForAll(testsSUIsotropicImprimitives, TestSUIsotropicImprimitives);
true
gap> TestSUNonDegenerateImprimitives := function(args)
>   local n, q, t, G;
>   n := args[1];
>   q := args[2];
>   t := args[3];
>   G := SUNonDegenerateImprimitives(n, q, t);
>   RECOG.TestGroup(G, false, Size(G));
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G))
>          and DefaultFieldOfMatrixGroup(G) = GF(q ^ 2);
> end;;
gap> testsSUNonDegenerateImprimitives := [[6, 3, 3], [9, 2, 3], [3, 5, 3]];;
gap> ForAll(testsSUNonDegenerateImprimitives, TestSUNonDegenerateImprimitives);
true
