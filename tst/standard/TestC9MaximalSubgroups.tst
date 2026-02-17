gap> TestC9SubgroupsSpecialLinearGroupGeneric := function(n, q)
>     local all, novelties, special, general, normaliser, result, G;
>     all := ValueOption("all");
>     if all = fail then all := true; fi;
>     novelties := ValueOption("novelties");
>     if novelties = fail then novelties := false; fi;
>     special := ValueOption("special");
>     if special = fail then special := false; fi;
>     general := ValueOption("general");
>     if general = fail then general := false; fi;
>     normaliser := ValueOption("normaliser");
>     if normaliser = fail then normaliser := false; fi;
>     result := C9SubgroupsSpecialLinearGroupGeneric(n, q :
>                                                    all := all,
>                                                    novelties := novelties,
>                                                    special := special,
>                                                    general := general,
>                                                    normaliser := normaliser);
>     for G in result do
>         CheckIsSubsetSL(n, q, G);
>         if not general then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric := function(n, q)
>     local all, novelties, special, general, normaliser, result, G;
>     all := ValueOption("all");
>     if all = fail then all := true; fi;
>     novelties := ValueOption("novelties");
>     if novelties = fail then novelties := false; fi;
>     special := ValueOption("special");
>     if special = fail then special := false; fi;
>     general := ValueOption("general");
>     if general = fail then general := false; fi;
>     normaliser := ValueOption("normaliser");
>     if normaliser = fail then normaliser := false; fi;
>     result := C9SubgroupsSpecialUnitaryGroupGeneric(n, q :
>                                                     all := all,
>                                                     novelties := novelties,
>                                                     special := special,
>                                                     general := general,
>                                                     normaliser := normaliser);
>     for G in result do
>         if not normaliser then
>             CheckIsSubsetSU(n, q, G);
>         else
>             CheckIsSubsetSL(n, q, G);
>         fi;
>         if not general and not normaliser then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsSymplecticGroupGeneric := function(n, q)
>     local all, novelties, special, general, normaliser, result, G;
>     all := ValueOption("all");
>     if all = fail then all := true; fi;
>     novelties := ValueOption("novelties");
>     if novelties = fail then novelties := false; fi;
>     special := ValueOption("special");
>     if special = fail then special := false; fi;
>     general := ValueOption("general");
>     if general = fail then general := false; fi;
>     normaliser := ValueOption("normaliser");
>     if normaliser = fail then normaliser := false; fi;
>     result := C9SubgroupsSymplecticGroupGeneric(n, q :
>                                                 all := all,
>                                                 novelties := novelties,
>                                                 special := special,
>                                                 general := general,
>                                                 normaliser := normaliser);
>     for G in result do
>         if not normaliser then
>             CheckIsSubsetSp(n, q, G);
>         else
>             CheckIsSubsetSL(n, q, G);
>         fi;
>         if not normaliser then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsOrthogonalGroupGeneric := function(epsilon, n, q)
>     local all, novelties, special, general, normaliser, result, G;
>     all := ValueOption("all");
>     if all = fail then all := true; fi;
>     novelties := ValueOption("novelties");
>     if novelties = fail then novelties := false; fi;
>     special := ValueOption("special");
>     if special = fail then special := false; fi;
>     general := ValueOption("general");
>     if general = fail then general := false; fi;
>     normaliser := ValueOption("normaliser");
>     if normaliser = fail then normaliser := false; fi;
>     result := C9SubgroupsOrthogonalGroupGeneric(epsilon, n, q :
>                                                 all := all,
>                                                 novelties := novelties,
>                                                 special := special,
>                                                 general := general,
>                                                 normaliser := normaliser);
>     for G in result do
>         if not normaliser then
>             CheckIsSubsetOmega(epsilon, n, q, G);
>         else
>             CheckIsSubsetSL(n, q ,G);
>         fi;
>         if not special and not general and not normaliser then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,4 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,11 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,7^2 : all:=false);  # Giving up, Schreier tree is not shallow.
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,11 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,11 : all:=false);  # Giving up, Schreier tree is not shallow.
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,19 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,7^2 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,11 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7 : novelties:=true);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,13 : all:=false);  # Giving up, Schreier tree is not shallow
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,2 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,3 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,31 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,7 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,3 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13 : novelties:=true, all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,7 : novelties:=true, all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13^2 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,5 : all:=false);  # Giving up, Schreier tree is not shallow.
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,3 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,7 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,19 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13^2 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,29 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,29 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,3^2 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,17^2 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,41 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,241 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,5 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,5 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,5 : all:=false);  # Have n points
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,7 : all:=false);  # Have n points
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,37 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,2 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,23 : novelties:=true, all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,9 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,53 : novelties:=true, all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,5 : all:=false);  # Giving up, Schreier tree is not shallow.
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,3 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,11 : all:=false);  # Have n points
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,37 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,2 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,13 : all:=false);
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,2 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,31 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13^2 : novelties:=true);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13^2 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13 : all:=false);  # Have n points (but recog #374 solved)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,31 : all:=false);  # Have n points
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,49 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,13 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,29 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,5 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,13 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,11 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,3 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,3^2 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,19 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,29 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,11 : novelties:=true, all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,17 : novelties:=true, all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,23 : novelties:=true, all:=false);  # Could not find hash function
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,17 : all:=false);  # Could not find hash function
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,2 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,23 : all:=false);  # Could not find hash function
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,83 : all:=false);  # Could not find hash function
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,11 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,11 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,19 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,59 : all:=false);  # Cound not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,71 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,31 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,79 : all:=false);  # Could not find hash function
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,2 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,13 : all:=false);  # Have n points
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,107 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,2 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(10,19 : novelties:=true, all:=false);  # Could not find hash function
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(10,3 : all:=false);  # Have n points
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(10,31 : all:=false);  # Could not find hash function
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(11,5 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(11,43 : all:=false);  # Could not find hash function
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,11 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,11 : all:=false);  # Have n points
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,5 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsSymplecticGroupGeneric(4,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(4,7 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(4,11 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(4,2^3 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,9 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,19 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,7 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,17 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,5^2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,11 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSymplecticGroupGeneric(6,3^2 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsSymplecticGroupGeneric(6,2^2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(8,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(8,5 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSymplecticGroupGeneric(8,11 : all:=false);  # Have n points
gap> TestC9SubgroupsSymplecticGroupGeneric(8,19 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(8,7^2 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsSymplecticGroupGeneric(8,2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,7 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,5^2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,23 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(12,11 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSymplecticGroupGeneric(12,11 : all:=false);  # Have n points
gap> TestC9SubgroupsSymplecticGroupGeneric(12,7^2 : all:=false);  # Have n points
gap> TestC9SubgroupsSymplecticGroupGeneric(12,41 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsSymplecticGroupGeneric(12,3^3 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSymplecticGroupGeneric(12,7 : all:=false);  # Have n points
gap> TestC9SubgroupsSymplecticGroupGeneric(12,3 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsSymplecticGroupGeneric(12,2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,3,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,3,11 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,3,7^2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,4,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,4,7 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,5,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,5,11 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,5,7 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,31 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,11 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,29 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,7 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,13 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,13 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,19 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,11 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,17 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,29 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,3 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,7,3 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,7,3 : all:=false);  # Giving up, Schreier tree is not shallow.
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,7,31 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5 : all:=false);
#I  2.O(7,q) < O^+(8,q) is not implemented yet.
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,2 : all:=false);
#I  2.O(7,q) < O^+(8,q) is not implemented yet.
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,3 : all:=false);
#I  2.O(7,q) < O^+(8,q) is not implemented yet.
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,2^3 : all:=false);  # Have n points
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5^3 : all:=false);  # Have n points
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5^2 : all:=false);  # Have n points
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,2^2 : all:=false);  # Giving up, Schreier tree is not shallow.
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,3^2 : all:=false); # Have n points
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,8,13 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,8,13 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,13 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,13 : all:=false);  # Have n points
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,3^3 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,3^2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,11 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,31 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,29 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,37 : novelties:=true, all:=false);  # Have n points
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,31 : all:=false);  # Have n points
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,37 : all:=false);  # Have n points
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,3 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,7 : novelties:=true, all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,19 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,2 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,13 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,19 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,2 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,7 : all:=false);  # SLCR.FindGoodElement
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,5 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,13 : all:=false); # SLCR.FindGoodElement, error without loop
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,17 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,23 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,19 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,29 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,41 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,3^2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,2^2 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,11^3 : all:=false);  # Could not find hash function
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,11 : all:=false);  # SLCR.FindGoodElement
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,2 : all:=false);  # SLCR.FindGoodElement, error without loop
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,7 : all:=false);
