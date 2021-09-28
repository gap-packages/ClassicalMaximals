gap> n := 4;; p := 2;; e := 4;; f := 2;;
gap> G := SubfieldSL(n, p, e, f);;
gap> IsSubset(SL(n, p ^ e), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 2;; p := 3;; e := 6;; f := 2;;
gap> G := SubfieldSL(n, p, e, f);;
gap> IsSubset(SL(n, p ^ e), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; p := 7;; e := 3;; f := 1;;
gap> G := SubfieldSL(n, p, e, f);;
gap> IsSubset(SL(n, p ^ e), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 2;; p := 3;; e := 6;; f := 2;;
gap> G := UnitarySubfieldSU(n, p, e, f);;
gap> IsSubset(SU(n, p ^ e), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; p := 7;; e := 3;; f := 1;;
gap> G := UnitarySubfieldSU(n, p, e, f);;
gap> IsSubset(SU(n, p ^ e), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; p := 5;; e := 3;; f := 1;;
gap> G := UnitarySubfieldSU(n, p, e, f);;
gap> IsSubset(SU(n, p ^ e), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 5;;
gap> G := SymplecticSubfieldSU(n, q);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 2;; q := 4;;
gap> G := SymplecticSubfieldSU(n, q);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 3;;
gap> G := SymplecticSubfieldSU(n, q);;
gap> IsSubset(SU(n, q), GeneratorsOfGroup(G));
true
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
