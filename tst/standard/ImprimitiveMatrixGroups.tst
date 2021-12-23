gap> START_TEST("ImprimitiveMatrixGroups.tst");

#
gap> TestImprimitivesMeetSL := function(n, q, t)
>   local G;
>   G := ImprimitivesMeetSL(n, q, t);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSL(n, q, G));
> end;;
gap> TestImprimitivesMeetSL(2, 3, 2);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestImprimitivesMeetSL(4, 8, 2); # FIXME: `Error, !!!`, see https://github.com/gap-packages/recog/issues/12
#@fi
gap> TestImprimitivesMeetSL(6, 5, 3);

#
gap> TestSUIsotropicImprimitives := function(n, q)
>   local G;
>   G := SUIsotropicImprimitives(n, q);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSU(n, q, G));
> end;;
gap> TestSUIsotropicImprimitives(6, 2);
gap> TestSUIsotropicImprimitives(4, 3);
gap> TestSUIsotropicImprimitives(2, 5);

#
gap> TestSUNonDegenerateImprimitives := function(n, q, t)
>   local G;
>   G := SUNonDegenerateImprimitives(n, q, t);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSU(n, q, G));
> end;;
gap> TestSUNonDegenerateImprimitives(6, 3, 3);
gap> TestSUNonDegenerateImprimitives(9, 2, 3);
gap> TestSUNonDegenerateImprimitives(3, 5, 3);

#
gap> TestSpIsotropicImprimitives := function(n, q)
>   local G;
>   G := SpIsotropicImprimitives(n, q);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSp(n, q, G));
> end;;
gap> TestSpIsotropicImprimitives(4, 3);
gap> TestSpIsotropicImprimitives(4, 7);
gap> TestSpIsotropicImprimitives(6, 5);
gap> TestSpIsotropicImprimitives(8, 3);

# Test error handling
gap> SpIsotropicImprimitives(3, 3);
Error, <d> must be even
gap> SpIsotropicImprimitives(4, 2);
Error, <q> must be odd

#
gap> TestSpNonDegenerateImprimitives := function(n, q, t)
>   local G;
>   G := SpNonDegenerateImprimitives(n, q, t);
>   Assert(0, CheckSize(G));
>   Assert(0, IsSubsetSp(n, q, G));
> end;;
gap> TestSpNonDegenerateImprimitives(4, 2, 2);
gap> TestSpNonDegenerateImprimitives(6, 5, 3);
gap> TestSpNonDegenerateImprimitives(10, 3, 5);
gap> TestSpNonDegenerateImprimitives(12, 3, 3);

# Test error handling
gap> SpNonDegenerateImprimitives(3, 3, 3);
Error, <d> must be even
gap> SpNonDegenerateImprimitives(4, 3, 3);
Error, <t> must divide <d>
gap> SpNonDegenerateImprimitives(6, 3, 2);
Error, <m> = <d> / <t> must be even

#
gap> STOP_TEST("ImprimitiveMatrixGroups.tst", 0);
