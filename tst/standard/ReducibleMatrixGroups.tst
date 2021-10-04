gap> TestSLStabilizerOfSubspace := function(args)
>   local n, q, k, G;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SLStabilizerOfSubspace(n, q, k);
>   return IsSubset(SL(n, q), GeneratorsOfGroup(G)) and
>          Size(Group(GeneratorsOfGroup(G))) = Size(G);
> end;;
gap> testsSLStabilizerOfSubspace := [[4, 3, 2], [3, 8, 2], [2, 7, 1]];;
gap> ForAll(testsSLStabilizerOfSubspace, TestSLStabilizerOfSubspace);
true
gap> TestSUStabilizerOfIsotropicSubspace := function(args)
>   local n, q, k, G;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SUStabilizerOfIsotropicSubspace(n, q, k);
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G)) and
>          Size(Group(GeneratorsOfGroup(G))) = Size(G);
> end;;
gap> testsSUStabilizerOfIsotropicSubspace := [[4, 3, 2], [3, 5, 1], [3, 4, 1], [4, 3, 1]];;
gap> ForAll(testsSUStabilizerOfIsotropicSubspace, TestSUStabilizerOfIsotropicSubspace);
true
gap> TestSUStabilizerOfNonDegenerateSubspace := function(args)
>   local n, q, k, G;
>   n := args[1];
>   q := args[2];
>   k := args[3];
>   G := SUStabilizerOfNonDegenerateSubspace(n, q, k);
>   return IsSubset(SU(n, q), GeneratorsOfGroup(G)) and
>          Size(Group(GeneratorsOfGroup(G))) = Size(G);
> end;;
gap> testsSUStabilizerOfNonDegenerateSubspace := [[5, 3, 2], [6, 3, 2], [4, 5, 1], [5, 4, 1]];;
gap> ForAll(testsSUStabilizerOfNonDegenerateSubspace, TestSUStabilizerOfNonDegenerateSubspace);
true
