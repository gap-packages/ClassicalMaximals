gap> START_TEST("C9MaximalSubgroups.tst");
gap> oldOrbInfoLevel:=InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0); # silence `Giving up, Schreier tree is not shallow.` warnings

#
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
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,7^2 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,11 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,19 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,7^2 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,11 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7 : novelties:=true);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,13 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,2 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,3 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,31 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,7 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,3 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13^2 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,3 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,7 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,19 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13^2 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,29 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,29 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,3^2 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,17^2 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,41 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,241 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,2 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,23 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,9 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,53 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,5 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,3 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,2 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,7 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,13 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,2 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,31 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13^2 : novelties:=true);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13^2 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,31 : all:=false);
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,49 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,13 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,29 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,5 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,13 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,11 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,3 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,3^2 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,19 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,29 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,11 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,17 : novelties:=true, all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,23 : novelties:=true, all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,17 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,2 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,23 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,7 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,83 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,11 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,19 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,59 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,71 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,31 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,79 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,2 : novelties:=true, all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,107 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,2 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(10,19 : novelties:=true, all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(10,31 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(11,5 : all:=false);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(11,43 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,11 : all:=false);
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,5 : all:=false);
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
gap> TestC9SubgroupsSymplecticGroupGeneric(6,3^2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(6,2^2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(8,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(8,5 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(8,11 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(8,2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,7 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,5^2 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(10,23 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(12,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(12,3^3 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(12,7 : all:=false);
gap> TestC9SubgroupsSymplecticGroupGeneric(12,3 : all:=false);
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
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,3 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,7,3 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,7,3 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,3 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,2^2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,8,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,13 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,3^2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,11 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,13 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,31 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,29 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,37 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,31 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,37 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,3 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,7 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,11 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,19 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,2 : novelties:=true, all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,13 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,19 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,7 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,5 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,7 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,13 : all:=false);
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
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,11^3 : all:=false);  # FIXME: `Error, Could not find hash function` (recog issue #123)
#@fi
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,11 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,2 : all:=false);
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,7 : all:=false);

#
gap> SetInfoLevel(InfoOrb, oldOrbInfoLevel);
gap> STOP_TEST("C9MaximalSubgroups.tst", 0);
