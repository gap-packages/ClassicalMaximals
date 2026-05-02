gap> START_TEST("ClassicalMaximals.tst");
gap> oldClassicalMaximalsInfoLevel:=InfoLevel(InfoClassicalMaximals);;
gap> SetInfoLevel(InfoClassicalMaximals, 1);

# Test error handling
gap> ClassicalMaximalsGeneric("L", 2, 4, [0]);
Error, <classes> must be a subset of [1..9]
gap> ClassicalMaximalsGeneric("", 2, 4);
Error, Type must be in ['L', 'U', 'S', 'O-', 'O', 'O+']
gap> MaximalSubgroupClassRepsSpecialLinearGroup(2, 4, [0]);
Error, <classes> must be a subset of [1..9]
gap> MaximalSubgroupClassRepsSpecialLinearGroup(2, 2);
Error, SL(2, 2) and SL(2, 3) are soluble
gap> MaximalSubgroupClassRepsSpecialUnitaryGroup(3, 5, [0]);
Error, <classes> must be a subset of [1..9]
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> MaximalSubgroupClassRepsSpecialUnitaryGroup(2, 3);  # FIXME: Unstable output formatting (line breaks) in error message
Error, We assume <n> to be greater or equal to 3 in case 'U' since SU(2, q) and SL(2, q) are isomorphic
#@fi
gap> MaximalSubgroupClassRepsSpecialUnitaryGroup(3, 2);
Error, PSU(3, 2) is soluble
gap> MaximalSubgroupClassRepsSymplecticGroup(4, 3, [0]);
Error, <classes> must be a subset of [1..9]
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> MaximalSubgroupClassRepsSymplecticGroup(2, 3);  # FIXME: Unstable output formatting (line breaks) in error message
Error, We assume <n> to be greater or equal to 4 in case 'S' since Sp(2, q) and SL(2, q) are isomorphic
#@fi
gap> MaximalSubgroupClassRepsSymplecticGroup(4, 2);
Error, Sp(4, 2) is not quasisimple
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> MaximalSubgroupClassRepsOrthogonalGroup(1, 2, 3);  # FIXME: Unstable output formatting (line breaks) in error message
Error, We assume <n> to be greater or equal to 3 in cases 'O', 'O+' or 'O-'
#@fi
gap> MaximalSubgroupClassRepsOrthogonalGroup(-1, 4, 3, [0]);
Error, <classes> must be a subset of [1..9]
gap> MaximalSubgroupClassRepsOrthogonalGroup(0, 4, 3);
Error, Degree must be odd for type 'O'
gap> MaximalSubgroupClassRepsOrthogonalGroup(1, 3, 5);
Error, Degree must be even for types 'O+' or 'O-'
gap> MaximalSubgroupClassRepsOrthogonalGroup(0, 3, 2);
Error, O(3,2) and O(3,3) are soluble
gap> MaximalSubgroupClassRepsOrthogonalGroup(1, 4, 3);
Error, O^+(4,q) is not quasisimple

#
gap> Length(ClassicalMaximalsGeneric("L", 2, 4));
3
gap> Length(ClassicalMaximalsGeneric("L", 2, 5));
3
gap> Length(ClassicalMaximalsGeneric("L", 2, 7));
3
gap> Length(ClassicalMaximalsGeneric("L", 2, 8));
3
gap> Length(ClassicalMaximalsGeneric("L", 2, 9));
5
gap> Length(ClassicalMaximalsGeneric("L", 2, 11));
4
gap> Length(ClassicalMaximalsGeneric("L", 2, 13));
4
gap> Length(ClassicalMaximalsGeneric("L", 2, 16));
4
gap> Length(ClassicalMaximalsGeneric("L", 2, 17));
5
gap> Length(ClassicalMaximalsGeneric("L", 2, 19));
5
gap> Length(ClassicalMaximalsGeneric("L", 3, 2));
3
gap> Length(ClassicalMaximalsGeneric("L", 3, 3));
4
gap> Length(ClassicalMaximalsGeneric("L", 3, 4));
9
gap> Length(ClassicalMaximalsGeneric("L", 3, 5));
5
gap> Length(ClassicalMaximalsGeneric("L", 3, 7));
8
gap> Length(ClassicalMaximalsGeneric("L", 3, 8));
5
gap> Length(ClassicalMaximalsGeneric("L", 3, 9));
7
gap> Length(ClassicalMaximalsGeneric("L", 3, 11));
6
gap> Length(ClassicalMaximalsGeneric("L", 3, 13));
8
gap> Length(ClassicalMaximalsGeneric("L", 3, 16));
8
gap> Length(ClassicalMaximalsGeneric("L", 3, 17));
5
gap> Length(ClassicalMaximalsGeneric("L", 3, 19));
13
gap> Length(ClassicalMaximalsGeneric("L", 4, 2));
6
gap> Length(ClassicalMaximalsGeneric("L", 4, 3));
8
gap> Length(ClassicalMaximalsGeneric("L", 4, 4));
8
gap> Length(ClassicalMaximalsGeneric("L", 4, 5));
13
gap> Length(ClassicalMaximalsGeneric("L", 4, 7));
12
gap> Length(ClassicalMaximalsGeneric("L", 4, 8));
8
gap> Length(ClassicalMaximalsGeneric("L", 4, 9));
18
gap> Length(ClassicalMaximalsGeneric("L", 4, 11));
12
gap> Length(ClassicalMaximalsGeneric("L", 4, 13));
18
gap> Length(ClassicalMaximalsGeneric("L", 4, 16));
9
gap> Length(ClassicalMaximalsGeneric("L", 4, 17));
16
gap> Length(ClassicalMaximalsGeneric("L", 4, 19));
12
gap> Length(ClassicalMaximalsGeneric("L", 5, 2));
5
gap> Length(ClassicalMaximalsGeneric("L", 5, 3));
8
gap> Length(ClassicalMaximalsGeneric("L", 5, 4));
7
gap> Length(ClassicalMaximalsGeneric("L", 5, 5));
8
gap> Length(ClassicalMaximalsGeneric("L", 5, 7));
8
gap> Length(ClassicalMaximalsGeneric("L", 5, 8));
7
gap> Length(ClassicalMaximalsGeneric("L", 5, 9));
9
gap> Length(ClassicalMaximalsGeneric("L", 5, 11));
16
gap> Length(ClassicalMaximalsGeneric("L", 5, 13));
8
gap> Length(ClassicalMaximalsGeneric("L", 5, 16));
12
gap> Length(ClassicalMaximalsGeneric("L", 5, 17));
7
gap> Length(ClassicalMaximalsGeneric("L", 5, 19));
8
gap> Length(ClassicalMaximalsGeneric("L", 6, 2));
9
gap> Length(ClassicalMaximalsGeneric("L", 6, 3));
17
gap> Length(ClassicalMaximalsGeneric("L", 6, 4));
17
gap> Length(ClassicalMaximalsGeneric("L", 6, 5));
18
gap> Length(ClassicalMaximalsGeneric("L", 6, 7));
37
gap> Length(ClassicalMaximalsGeneric("L", 6, 8));
13
gap> Length(ClassicalMaximalsGeneric("L", 6, 9));
20
gap> Length(ClassicalMaximalsGeneric("L", 6, 11));
16
gap> Length(ClassicalMaximalsGeneric("L", 6, 13));
28
gap> Length(ClassicalMaximalsGeneric("L", 6, 16));
18
gap> Length(ClassicalMaximalsGeneric("L", 6, 17));
16
gap> Length(ClassicalMaximalsGeneric("L", 6, 19));
31
gap> Length(ClassicalMaximalsGeneric("L", 7, 2));
7
gap> Length(ClassicalMaximalsGeneric("L", 7, 3));
8
gap> Length(ClassicalMaximalsGeneric("L", 7, 4));
9
gap> Length(ClassicalMaximalsGeneric("L", 7, 5));
10
gap> Length(ClassicalMaximalsGeneric("L", 7, 7));
9
gap> Length(ClassicalMaximalsGeneric("L", 7, 8));
22
gap> Length(ClassicalMaximalsGeneric("L", 7, 9));
11
gap> Length(ClassicalMaximalsGeneric("L", 7, 11));
9
gap> Length(ClassicalMaximalsGeneric("L", 7, 13));
10
gap> Length(ClassicalMaximalsGeneric("L", 7, 16));
10
gap> Length(ClassicalMaximalsGeneric("L", 7, 17));
10
gap> Length(ClassicalMaximalsGeneric("L", 7, 19));
9
gap> Length(ClassicalMaximalsGeneric("L", 8, 2));
10
gap> Length(ClassicalMaximalsGeneric("L", 8, 3));
16
gap> Length(ClassicalMaximalsGeneric("L", 8, 4));
14
gap> Length(ClassicalMaximalsGeneric("L", 8, 5));
27
gap> Length(ClassicalMaximalsGeneric("L", 8, 7));
17
gap> Length(ClassicalMaximalsGeneric("L", 8, 8));
14
gap> Length(ClassicalMaximalsGeneric("L", 8, 9));
39
gap> Length(ClassicalMaximalsGeneric("L", 8, 11));
17
gap> Length(ClassicalMaximalsGeneric("L", 8, 13));
25
gap> Length(ClassicalMaximalsGeneric("L", 8, 16));
15
gap> Length(ClassicalMaximalsGeneric("L", 8, 17));
33
gap> Length(ClassicalMaximalsGeneric("L", 8, 19));
17
gap> Length(ClassicalMaximalsGeneric("L", 9, 2));
12
gap> Length(ClassicalMaximalsGeneric("L", 9, 3));
13
gap> Length(ClassicalMaximalsGeneric("L", 9, 4));
20
gap> Length(ClassicalMaximalsGeneric("L", 9, 5));
15
gap> Length(ClassicalMaximalsGeneric("L", 9, 7));
32
gap> Length(ClassicalMaximalsGeneric("L", 9, 8));
14
gap> Length(ClassicalMaximalsGeneric("L", 9, 9));
16
gap> Length(ClassicalMaximalsGeneric("L", 9, 11));
15
gap> Length(ClassicalMaximalsGeneric("L", 9, 13));
26
gap> Length(ClassicalMaximalsGeneric("L", 9, 16));
21
gap> Length(ClassicalMaximalsGeneric("L", 9, 17));
15
gap> Length(ClassicalMaximalsGeneric("L", 9, 19));
35
gap> Length(ClassicalMaximalsGeneric("L", 10, 2));
16
gap> Length(ClassicalMaximalsGeneric("L", 10, 3));
22
gap> Length(ClassicalMaximalsGeneric("L", 10, 4));
18
gap> Length(ClassicalMaximalsGeneric("L", 10, 5));
25
gap> Length(ClassicalMaximalsGeneric("L", 10, 7));
25
gap> Length(ClassicalMaximalsGeneric("L", 10, 8));
18
gap> Length(ClassicalMaximalsGeneric("L", 10, 9));
25
gap> Length(ClassicalMaximalsGeneric("L", 10, 11));
77
gap> Length(ClassicalMaximalsGeneric("L", 10, 13));
23
gap> Length(ClassicalMaximalsGeneric("L", 10, 16));
27
gap> Length(ClassicalMaximalsGeneric("L", 10, 17));
29
gap> Length(ClassicalMaximalsGeneric("L", 10, 19));
25
gap> Length(ClassicalMaximalsGeneric("L", 11, 2));
13
gap> Length(ClassicalMaximalsGeneric("L", 11, 3));
13
gap> Length(ClassicalMaximalsGeneric("L", 11, 4));
13
gap> Length(ClassicalMaximalsGeneric("L", 11, 5));
13
gap> Length(ClassicalMaximalsGeneric("L", 11, 7));
14
gap> Length(ClassicalMaximalsGeneric("L", 11, 8));
13
gap> Length(ClassicalMaximalsGeneric("L", 11, 9));
15
gap> Length(ClassicalMaximalsGeneric("L", 11, 11));
13
gap> Length(ClassicalMaximalsGeneric("L", 11, 13));
15
gap> Length(ClassicalMaximalsGeneric("L", 11, 16));
14
gap> Length(ClassicalMaximalsGeneric("L", 11, 17));
13
gap> Length(ClassicalMaximalsGeneric("L", 11, 19));
14
gap> Length(ClassicalMaximalsGeneric("L", 12, 2));
18
gap> Length(ClassicalMaximalsGeneric("L", 12, 3));
26
gap> Length(ClassicalMaximalsGeneric("L", 12, 4));
26
gap> Length(ClassicalMaximalsGeneric("L", 12, 5));
27
gap> Length(ClassicalMaximalsGeneric("L", 12, 7));
39
gap> Length(ClassicalMaximalsGeneric("L", 12, 8));
22
gap> Length(ClassicalMaximalsGeneric("L", 12, 9));
33
gap> Length(ClassicalMaximalsGeneric("L", 12, 11));
25
gap> Length(ClassicalMaximalsGeneric("L", 12, 13));
63
gap> Length(ClassicalMaximalsGeneric("L", 12, 16));
27
gap> Length(ClassicalMaximalsGeneric("L", 12, 17));
27
gap> Length(ClassicalMaximalsGeneric("L", 12, 19));
39

#
gap> Length(ClassicalMaximalsGeneric("U", 3, 3));
4
gap> Length(ClassicalMaximalsGeneric("U", 3, 4));
4
gap> Length(ClassicalMaximalsGeneric("U", 3, 5));
8
gap> Length(ClassicalMaximalsGeneric("U", 3, 7));
5
gap> Length(ClassicalMaximalsGeneric("U", 3, 8));
7
gap> Length(ClassicalMaximalsGeneric("U", 3, 9));
5
gap> Length(ClassicalMaximalsGeneric("U", 3, 11));
11
gap> Length(ClassicalMaximalsGeneric("U", 3, 13));
6
gap> Length(ClassicalMaximalsGeneric("U", 3, 16));
4
gap> Length(ClassicalMaximalsGeneric("U", 3, 17));
13
gap> Length(ClassicalMaximalsGeneric("U", 3, 19));
6
gap> Length(ClassicalMaximalsGeneric("U", 4, 2));
5
gap> Length(ClassicalMaximalsGeneric("U", 4, 3));
16
gap> Length(ClassicalMaximalsGeneric("U", 4, 4));
7
gap> Length(ClassicalMaximalsGeneric("U", 4, 5));
14
gap> Length(ClassicalMaximalsGeneric("U", 4, 7));
16
gap> Length(ClassicalMaximalsGeneric("U", 4, 8));
8
gap> Length(ClassicalMaximalsGeneric("U", 4, 9));
10
gap> Length(ClassicalMaximalsGeneric("U", 4, 11));
18
gap> Length(ClassicalMaximalsGeneric("U", 4, 13));
12
gap> Length(ClassicalMaximalsGeneric("U", 4, 16));
7
gap> Length(ClassicalMaximalsGeneric("U", 4, 17));
14
gap> Length(ClassicalMaximalsGeneric("U", 4, 19));
18
gap> Length(ClassicalMaximalsGeneric("U", 5, 2));
6
gap> Length(ClassicalMaximalsGeneric("U", 5, 3));
7
gap> Length(ClassicalMaximalsGeneric("U", 5, 4));
11
gap> Length(ClassicalMaximalsGeneric("U", 5, 5));
8
gap> Length(ClassicalMaximalsGeneric("U", 5, 7));
8
gap> Length(ClassicalMaximalsGeneric("U", 5, 8));
7
gap> Length(ClassicalMaximalsGeneric("U", 5, 9));
16
gap> Length(ClassicalMaximalsGeneric("U", 5, 11));
8
gap> Length(ClassicalMaximalsGeneric("U", 5, 13));
8
gap> Length(ClassicalMaximalsGeneric("U", 5, 16));
6
gap> Length(ClassicalMaximalsGeneric("U", 5, 17));
9
gap> Length(ClassicalMaximalsGeneric("U", 5, 19));
21
gap> Length(ClassicalMaximalsGeneric("U", 6, 2));
16
gap> Length(ClassicalMaximalsGeneric("U", 6, 3));
16
gap> Length(ClassicalMaximalsGeneric("U", 6, 4));
12
gap> Length(ClassicalMaximalsGeneric("U", 6, 5));
31
gap> Length(ClassicalMaximalsGeneric("U", 6, 7));
18
gap> Length(ClassicalMaximalsGeneric("U", 6, 8));
17
gap> Length(ClassicalMaximalsGeneric("U", 7, 2));
8
gap> Length(ClassicalMaximalsGeneric("U", 7, 3));
9
gap> Length(ClassicalMaximalsGeneric("U", 7, 8));
9
gap> Length(ClassicalMaximalsGeneric("U", 7, 13));
22
gap> Length(ClassicalMaximalsGeneric("U", 8, 2));
11
gap> Length(ClassicalMaximalsGeneric("U", 8, 3));
25
gap> Length(ClassicalMaximalsGeneric("U", 8, 4));
13
gap> Length(ClassicalMaximalsGeneric("U", 8, 5));
17
gap> Length(ClassicalMaximalsGeneric("U", 8, 8));
14
gap> Length(ClassicalMaximalsGeneric("U", 9, 2));
20
gap> Length(ClassicalMaximalsGeneric("U", 9, 3));
15
gap> Length(ClassicalMaximalsGeneric("U", 9, 4));
13
gap> Length(ClassicalMaximalsGeneric("U", 9, 5));
23
gap> Length(ClassicalMaximalsGeneric("U", 9, 8));
20
gap> Length(ClassicalMaximalsGeneric("U", 10, 2));
15
gap> Length(ClassicalMaximalsGeneric("U", 10, 3));
27
gap> Length(ClassicalMaximalsGeneric("U", 10, 17));
25
gap> Length(ClassicalMaximalsGeneric("U", 11, 2));
12
gap> Length(ClassicalMaximalsGeneric("U", 11, 3));
13
gap> Length(ClassicalMaximalsGeneric("U", 12, 2));
24
gap> Length(ClassicalMaximalsGeneric("U", 12, 3));
27

#
gap> Length(ClassicalMaximalsGeneric("S", 4, 3));
5
gap> Length(ClassicalMaximalsGeneric("S", 4, 4));
7
gap> Length(ClassicalMaximalsGeneric("S", 4, 5));
8
gap> Length(ClassicalMaximalsGeneric("S", 4, 7));
9
gap> Length(ClassicalMaximalsGeneric("S", 4, 8));
8
gap> Length(ClassicalMaximalsGeneric("S", 4, 9));
8
gap> Length(ClassicalMaximalsGeneric("S", 4, 11));
10
gap> Length(ClassicalMaximalsGeneric("S", 4, 13));
10
gap> Length(ClassicalMaximalsGeneric("S", 4, 16));
7
gap> Length(ClassicalMaximalsGeneric("S", 4, 17));
10
gap> Length(ClassicalMaximalsGeneric("S", 4, 19));
9
gap> Length(ClassicalMaximalsGeneric("S", 6, 2));
8
gap> Length(ClassicalMaximalsGeneric("S", 6, 3));
11
gap> Length(ClassicalMaximalsGeneric("S", 6, 4));
10
gap> Length(ClassicalMaximalsGeneric("S", 6, 5));
10
gap> Length(ClassicalMaximalsGeneric("S", 6, 7));
13
gap> Length(ClassicalMaximalsGeneric("S", 6, 8));
10
gap> Length(ClassicalMaximalsGeneric("S", 6, 9));
15
gap> Length(ClassicalMaximalsGeneric("S", 6, 11));
14
gap> Length(ClassicalMaximalsGeneric("S", 6, 13));
13
gap> Length(ClassicalMaximalsGeneric("S", 6, 16));
10
gap> Length(ClassicalMaximalsGeneric("S", 6, 17));
19
gap> Length(ClassicalMaximalsGeneric("S", 6, 19));
12
gap> Length(ClassicalMaximalsGeneric("S", 8, 2));
11
gap> Length(ClassicalMaximalsGeneric("S", 8, 3));
13
gap> Length(ClassicalMaximalsGeneric("S", 8, 4));
11
gap> Length(ClassicalMaximalsGeneric("S", 8, 5));
15
gap> Length(ClassicalMaximalsGeneric("S", 8, 7));
15
gap> Length(ClassicalMaximalsGeneric("S", 8, 8));
11
gap> Length(ClassicalMaximalsGeneric("S", 8, 9));
17
gap> Length(ClassicalMaximalsGeneric("S", 8, 11));
18
gap> Length(ClassicalMaximalsGeneric("S", 8, 13));
19
gap> Length(ClassicalMaximalsGeneric("S", 8, 16));
11
gap> Length(ClassicalMaximalsGeneric("S", 8, 17));
17
gap> Length(ClassicalMaximalsGeneric("S", 8, 19));
20
gap> Length(ClassicalMaximalsGeneric("S", 10, 2));
10
gap> Length(ClassicalMaximalsGeneric("S", 10, 3));
14
gap> Length(ClassicalMaximalsGeneric("S", 10, 4));
12
gap> Length(ClassicalMaximalsGeneric("S", 10, 5));
14
gap> Length(ClassicalMaximalsGeneric("S", 10, 7));
17
gap> Length(ClassicalMaximalsGeneric("S", 10, 8));
12
gap> Length(ClassicalMaximalsGeneric("S", 10, 9));
14
gap> Length(ClassicalMaximalsGeneric("S", 10, 11));
14
gap> Length(ClassicalMaximalsGeneric("S", 10, 13));
17
gap> Length(ClassicalMaximalsGeneric("S", 10, 16));
12
gap> Length(ClassicalMaximalsGeneric("S", 10, 17));
19
gap> Length(ClassicalMaximalsGeneric("S", 10, 19));
15
gap> Length(ClassicalMaximalsGeneric("S", 12, 2));
16
gap> Length(ClassicalMaximalsGeneric("S", 12, 3));
18
gap> Length(ClassicalMaximalsGeneric("S", 12, 4));
19
gap> Length(ClassicalMaximalsGeneric("S", 12, 5));
20
gap> Length(ClassicalMaximalsGeneric("S", 12, 7));
21
gap> Length(ClassicalMaximalsGeneric("S", 12, 8));
19
gap> Length(ClassicalMaximalsGeneric("S", 12, 9));
24
gap> Length(ClassicalMaximalsGeneric("S", 12, 11));
21
gap> Length(ClassicalMaximalsGeneric("S", 12, 13));
21
gap> Length(ClassicalMaximalsGeneric("S", 12, 16));
16
gap> Length(ClassicalMaximalsGeneric("S", 12, 17));
22
gap> Length(ClassicalMaximalsGeneric("S", 12, 19));
26

#
gap> Length(ClassicalMaximalsGeneric("O", 3, 5));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
2
gap> Length(ClassicalMaximalsGeneric("O", 3, 7));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
2
gap> Length(ClassicalMaximalsGeneric("O", 3, 9));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O", 3, 11));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
3
gap> Length(ClassicalMaximalsGeneric("O", 3, 13));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
3
gap> Length(ClassicalMaximalsGeneric("O", 3, 17));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O", 3, 19));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O-", 4, 2));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
2
gap> Length(ClassicalMaximalsGeneric("O-", 4, 3));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O-", 4, 4));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
3
gap> Length(ClassicalMaximalsGeneric("O-", 4, 5));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O-", 4, 7));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
6
gap> Length(ClassicalMaximalsGeneric("O-", 4, 8));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O-", 4, 9));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O-", 4, 11));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O-", 4, 13));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
6
gap> Length(ClassicalMaximalsGeneric("O-", 4, 16));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
3
gap> Length(ClassicalMaximalsGeneric("O-", 4, 17));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
6
gap> Length(ClassicalMaximalsGeneric("O-", 4, 19));
#I  List incomplete. Missing subgroup in C1 of isotropic type P_1
4
gap> Length(ClassicalMaximalsGeneric("O", 5, 3));
5
gap> Length(ClassicalMaximalsGeneric("O", 5, 5));
8
gap> Length(ClassicalMaximalsGeneric("O", 5, 7));
9
gap> Length(ClassicalMaximalsGeneric("O", 5, 9));
8
gap> Length(ClassicalMaximalsGeneric("O", 5, 11));
10
gap> Length(ClassicalMaximalsGeneric("O", 5, 13));
10
gap> Length(ClassicalMaximalsGeneric("O", 5, 17));
10
gap> Length(ClassicalMaximalsGeneric("O", 5, 19));
9
gap> Length(ClassicalMaximalsGeneric("O+", 6, 2));
6
gap> Length(ClassicalMaximalsGeneric("O+", 6, 3));
8
gap> Length(ClassicalMaximalsGeneric("O+", 6, 4));
8
gap> Length(ClassicalMaximalsGeneric("O+", 6, 5));
13
gap> Length(ClassicalMaximalsGeneric("O+", 6, 7));
12
gap> Length(ClassicalMaximalsGeneric("O+", 6, 8));
8
gap> Length(ClassicalMaximalsGeneric("O+", 6, 9));
18
gap> Length(ClassicalMaximalsGeneric("O+", 6, 11));
12
gap> Length(ClassicalMaximalsGeneric("O+", 6, 13));
18
gap> Length(ClassicalMaximalsGeneric("O+", 6, 16));
9
gap> Length(ClassicalMaximalsGeneric("O+", 6, 17));
16
gap> Length(ClassicalMaximalsGeneric("O+", 6, 19));
12
gap> Length(ClassicalMaximalsGeneric("O+", 6, 25));
18
gap> Length(ClassicalMaximalsGeneric("O-", 6, 2));
5
gap> Length(ClassicalMaximalsGeneric("O-", 6, 3));
16
gap> Length(ClassicalMaximalsGeneric("O-", 6, 4));
7
gap> Length(ClassicalMaximalsGeneric("O-", 6, 5));
14
gap> Length(ClassicalMaximalsGeneric("O-", 6, 7));
16
gap> Length(ClassicalMaximalsGeneric("O-", 6, 8));
8
gap> Length(ClassicalMaximalsGeneric("O-", 6, 9));
10
gap> Length(ClassicalMaximalsGeneric("O-", 6, 11));
18
gap> Length(ClassicalMaximalsGeneric("O-", 6, 13));
12
gap> Length(ClassicalMaximalsGeneric("O-", 6, 16));
7
gap> Length(ClassicalMaximalsGeneric("O-", 6, 17));
14
gap> Length(ClassicalMaximalsGeneric("O-", 6, 19));
18
gap> Length(ClassicalMaximalsGeneric("O", 7, 3));
15
gap> Length(ClassicalMaximalsGeneric("O", 7, 5));
14
gap> Length(ClassicalMaximalsGeneric("O", 7, 7));
15
gap> Length(ClassicalMaximalsGeneric("O", 7, 9));
13
gap> Length(ClassicalMaximalsGeneric("O", 7, 11));
14
gap> Length(ClassicalMaximalsGeneric("O", 7, 13));
14
gap> Length(ClassicalMaximalsGeneric("O", 7, 17));
15
gap> Length(ClassicalMaximalsGeneric("O", 7, 19));
14
gap> Length(ClassicalMaximalsGeneric("O+", 8, 2));
17
gap> Length(ClassicalMaximalsGeneric("O+", 8, 3));
27
gap> Length(ClassicalMaximalsGeneric("O+", 8, 4));
23
gap> Length(ClassicalMaximalsGeneric("O+", 8, 5));
55
gap> Length(ClassicalMaximalsGeneric("O+", 8, 7));
48
gap> Length(ClassicalMaximalsGeneric("O+", 8, 8));
23
gap> Length(ClassicalMaximalsGeneric("O+", 8, 9));
38
gap> Length(ClassicalMaximalsGeneric("O+", 8, 11));
36
gap> Length(ClassicalMaximalsGeneric("O+", 8, 13));
36
gap> Length(ClassicalMaximalsGeneric("O+", 8, 16));
24
gap> Length(ClassicalMaximalsGeneric("O+", 8, 17));
48
gap> Length(ClassicalMaximalsGeneric("O+", 8, 19));
36
gap> Length(ClassicalMaximalsGeneric("O-", 8, 2));
8
gap> Length(ClassicalMaximalsGeneric("O-", 8, 3));
10
gap> Length(ClassicalMaximalsGeneric("O-", 8, 4));
9
gap> Length(ClassicalMaximalsGeneric("O-", 8, 5));
13
gap> Length(ClassicalMaximalsGeneric("O-", 8, 7));
13
gap> Length(ClassicalMaximalsGeneric("O-", 8, 8));
10
gap> Length(ClassicalMaximalsGeneric("O-", 8, 9));
11
gap> Length(ClassicalMaximalsGeneric("O-", 8, 11));
13
gap> Length(ClassicalMaximalsGeneric("O-", 8, 13));
13
gap> Length(ClassicalMaximalsGeneric("O-", 8, 16));
9
gap> Length(ClassicalMaximalsGeneric("O-", 8, 17));
13
gap> Length(ClassicalMaximalsGeneric("O-", 8, 19));
13
gap> Length(ClassicalMaximalsGeneric("O", 9, 3));
14
gap> Length(ClassicalMaximalsGeneric("O", 9, 5));
17
gap> Length(ClassicalMaximalsGeneric("O", 9, 7));
19
gap> Length(ClassicalMaximalsGeneric("O", 9, 9));
20
gap> Length(ClassicalMaximalsGeneric("O", 9, 11));
21
gap> Length(ClassicalMaximalsGeneric("O", 9, 13));
24
gap> Length(ClassicalMaximalsGeneric("O", 9, 17));
21
gap> Length(ClassicalMaximalsGeneric("O", 9, 19));
23
gap> Length(ClassicalMaximalsGeneric("O+", 10, 2));
9
gap> Length(ClassicalMaximalsGeneric("O+", 10, 3));
16
gap> Length(ClassicalMaximalsGeneric("O+", 10, 4));
12
gap> Length(ClassicalMaximalsGeneric("O+", 10, 5));
31
gap> Length(ClassicalMaximalsGeneric("O+", 10, 7));
16
gap> Length(ClassicalMaximalsGeneric("O+", 10, 8));
12
gap> Length(ClassicalMaximalsGeneric("O+", 10, 9));
28
gap> Length(ClassicalMaximalsGeneric("O+", 10, 11));
16
gap> Length(ClassicalMaximalsGeneric("O+", 10, 13));
24
gap> Length(ClassicalMaximalsGeneric("O+", 10, 16));
13
gap> Length(ClassicalMaximalsGeneric("O+", 10, 17));
26
gap> Length(ClassicalMaximalsGeneric("O+", 10, 19));
16
gap> Length(ClassicalMaximalsGeneric("O-", 10, 2));
11
gap> Length(ClassicalMaximalsGeneric("O-", 10, 3));
22
gap> Length(ClassicalMaximalsGeneric("O-", 10, 4));
11
gap> Length(ClassicalMaximalsGeneric("O-", 10, 5));
16
gap> Length(ClassicalMaximalsGeneric("O-", 10, 7));
38
gap> Length(ClassicalMaximalsGeneric("O-", 10, 8));
12
gap> Length(ClassicalMaximalsGeneric("O-", 10, 9));
16
gap> Length(ClassicalMaximalsGeneric("O-", 10, 11));
24
gap> Length(ClassicalMaximalsGeneric("O-", 10, 13));
20
gap> Length(ClassicalMaximalsGeneric("O-", 10, 16));
11
gap> Length(ClassicalMaximalsGeneric("O-", 10, 17));
20
gap> Length(ClassicalMaximalsGeneric("O-", 10, 19));
32
gap> Length(ClassicalMaximalsGeneric("O", 11, 3));
15
gap> Length(ClassicalMaximalsGeneric("O", 11, 5));
18
gap> Length(ClassicalMaximalsGeneric("O", 11, 7));
18
gap> Length(ClassicalMaximalsGeneric("O", 11, 9));
17
gap> Length(ClassicalMaximalsGeneric("O", 11, 11));
17
gap> Length(ClassicalMaximalsGeneric("O", 11, 13));
20
gap> Length(ClassicalMaximalsGeneric("O", 11, 17));
19
gap> Length(ClassicalMaximalsGeneric("O", 11, 19));
19
gap> Length(ClassicalMaximalsGeneric("O+", 12, 2));
20
gap> Length(ClassicalMaximalsGeneric("O+", 12, 3));
33
gap> Length(ClassicalMaximalsGeneric("O+", 12, 4));
26
gap> Length(ClassicalMaximalsGeneric("O+", 12, 5));
33
gap> Length(ClassicalMaximalsGeneric("O+", 12, 7));
36
gap> Length(ClassicalMaximalsGeneric("O+", 12, 8));
26
gap> Length(ClassicalMaximalsGeneric("O+", 12, 9));
38
gap> Length(ClassicalMaximalsGeneric("O+", 12, 11));
34
gap> Length(ClassicalMaximalsGeneric("O+", 12, 13));
34
gap> Length(ClassicalMaximalsGeneric("O+", 12, 16));
27
gap> Length(ClassicalMaximalsGeneric("O+", 12, 17));
40
gap> Length(ClassicalMaximalsGeneric("O+", 12, 19));
42
gap> Length(ClassicalMaximalsGeneric("O-", 12, 2));
16
gap> Length(ClassicalMaximalsGeneric("O-", 12, 3));
18
gap> Length(ClassicalMaximalsGeneric("O-", 12, 4));
16
gap> Length(ClassicalMaximalsGeneric("O-", 12, 5));
22
gap> Length(ClassicalMaximalsGeneric("O-", 12, 7));
22
gap> Length(ClassicalMaximalsGeneric("O-", 12, 8));
18
gap> Length(ClassicalMaximalsGeneric("O-", 12, 9));
24
gap> Length(ClassicalMaximalsGeneric("O-", 12, 11));
26
gap> Length(ClassicalMaximalsGeneric("O-", 12, 13));
20
gap> Length(ClassicalMaximalsGeneric("O-", 12, 16));
14
gap> Length(ClassicalMaximalsGeneric("O-", 12, 17));
20
gap> Length(ClassicalMaximalsGeneric("O-", 12, 19));
22

#
gap> Length(ClassicalMaximalsGeneric("O", 15, 5));
27
gap> Length(ClassicalMaximalsGeneric("O-", 20, 3));
31
gap> Length(ClassicalMaximalsGeneric("O+", 48, 3, [4]));
30
gap> Length(ClassicalMaximalsGeneric("O+", 80, 3, [4]));
31

#
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(2,4));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(2,11));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(2,7^2));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(2,11 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(2,11 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,11));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,11 : general:=true));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,11 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,11 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,19));
3
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,19 : general:=true));
3
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,7^2));
3
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(3,19 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,11));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,11 : novelties:=true));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,11 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,7));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,7 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,7 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,13));
4
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(4,2));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,3 : novelties:=true));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,5));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,31));
10
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,31 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,7));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,7 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,3));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(5,3 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,13 : novelties:=true));
6
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,7 : novelties:=true));
12
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,7 : novelties:=true, all:=false));
3
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,13^2 : novelties:=true));
6
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,19 : novelties:=true));
6
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,19 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,5));
4
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,5 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,5 : general:=true));
4
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,3));
4
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,7));
17
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,7 : all:=false));
4
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,19));
11
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,19 : all:=false));
3
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(6,13^2));
14
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(7,5 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(7,5));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(7,5 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(7,29));
7
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(7,29 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,29));
4
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,3^2));
8
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,17^2));
16
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,17^2 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,41));
8
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,41 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,241));
16
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,5));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(8,5 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,5 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,5));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,5 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,5 : general:=true));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,7));
12
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,7 : all:=false));
4
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,37));
12
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(9,37 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,2 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,23 : novelties:=true));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,23 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,9 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,53 : novelties:=true));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,5));
7
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,5 : general:=true));
7
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,3));
5
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,11));
47
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,11 : all:=false));
8
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,37));
9
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(10,37 : all:=false));
5
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(11, 2 : novelties:=true));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(11,7));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(11,7 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(11,13));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(11,13 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(11,2));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,31 : novelties:=true));
6
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,31 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,13^2 : novelties:=true));
12
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,13^2 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,13));
24
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,13 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,31));
12
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,31 : all:=false));
2
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,49));
12
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,49 : all:=false));
1
gap> Length(C9SubgroupsSpecialLinearGroupGeneric(12,49 : general:=true));
12

#
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(3,5 : novelties:=true));
3
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(3,5 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(3,13));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(3,29));
3
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(3,29 : all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(3,5));
6
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(3,5 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,13 : novelties:=true));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,13 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,13));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,13 : all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,11));
4
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,11 : all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,3));
6
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,3 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(4,3^2));
0
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(5,5 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(5,7));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(5,19));
5
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(5,19 : all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(5,29));
10
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(5,29 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,11 : novelties:=true));
6
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,11 : novelties:=true, all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,17 : novelties:=true));
12
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,17 : novelties:=true, all:=false));
3
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,23 : novelties:=true));
12
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,23 : novelties:=true, all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,7));
4
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,7 : general:=true));
4
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,7 : normaliser:=true));
4
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,17));
23
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,17 : all:=false));
5
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,2));
6
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,2 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,23));
26
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(6,23 : all:=false));
5
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(7,7 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(7,7));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(7,7 : all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(7,83));
7
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(7,83 : all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,11 : novelties:=true));
0
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,11));
4
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,11 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,19));
4
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,59));
4
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,71));
8
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,31));  # error in magma
16
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(8,79));  # error in magma
16
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,2 : novelties:=true));
3
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,2 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,13));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,107));
21
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,107 : all:=false));
3
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,2));
6
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,2 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,2 : normaliser:=true));
6
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,2 : normaliser:=true, all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(9,2 : general:=true));
6
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,13 : novelties:=true));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,19 : novelties:=true));
10
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,19 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,3));
9
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,3 : all:=false));
5
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,31));
15
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,31 : all:=false));
8
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,5));
9
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,5 : general:=true));
9
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(10,5 : normaliser:=true));
9
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(11,5));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(11,5 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(11,43));
11
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(11,43 : all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(12,11 : novelties:=true));
12
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(12,11 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(12,11));
24
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(12,11 : all:=false));
2
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(12,5));
18
gap> Length(C9SubgroupsSpecialUnitaryGroupGeneric(12,5 : all:=false));
3

#
gap> Length(C9SubgroupsSymplecticGroupGeneric(4,7 : novelties:=true));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(4,7 : novelties:=true, normaliser:=true));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(4,7));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(4,11));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(4,11 : all:=false));
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(4,2^3));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(4,2^3 : normaliser:=true));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,11 : novelties:=true));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,9 : novelties:=true));
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,9 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,19 : novelties:=true));
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,7));
4
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,7 : all:=false));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,17));
10
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,17 : all:=false));
6
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,5^2));
4
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,5^2 : all:=false));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,11));
5
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,11 : all:=false));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,3^2));
4
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,3^2 : all:=false));  # error in magma
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,2));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,2 : normaliser:=true));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,2^2));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(6,2^2 : normaliser:=true));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,5 : novelties:=true));
0
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,5));
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,5 : normaliser:=true));
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,11));
5
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,11 : all:=false));
4
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,19));
7
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,19 : all:=false));
5
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,7^2));
4
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,7^2 : all:=false));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(8,2));
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(10,7 : novelties:=true));
0
gap> Length(C9SubgroupsSymplecticGroupGeneric(10,7));
5
gap> Length(C9SubgroupsSymplecticGroupGeneric(10,7 : all:=false));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(10,5^2));
5
gap> Length(C9SubgroupsSymplecticGroupGeneric(10,23));
10
gap> Length(C9SubgroupsSymplecticGroupGeneric(10,23 : all:=false));
6
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,11 : novelties:=true));
0
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,11));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,11 : all:=false));
2
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,7^2));
4
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,7^2 : all:=false));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,41));
12
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,41 : all:=false));
8
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,3^3));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,29));
12
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,7));
3
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,3));
1
gap> Length(C9SubgroupsSymplecticGroupGeneric(12,2));
2

#
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,3,11 : novelties:=true));
0
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,3,11));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,3,11 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,3,7^2));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,4,7 : novelties:=true));
0
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,4,7));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,4,7 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,5,7 : novelties:=true));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,5,5));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,5,11));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,5,11 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,5,7));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,5,7 : novelties:=true, normaliser:=true));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,5,7 : novelties:=true, general:=true));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,11 : novelties:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,13 : novelties:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,31 : novelties:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,31 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,29 : novelties:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,11));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,29));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,29 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,7));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,13));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,13 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,6,2));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,13));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,19));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,19 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,11));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,11 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,17));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,29));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,3));
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,6,3 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,7,3 : novelties:=true));
0
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,7,3));
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,7,3 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,7,5 : normaliser:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,7,5 : general:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,7,31));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5 : novelties:=true));
0
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5));
32
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5 : all:=false));
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5 : normaliser:=true));
32
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5 : general:=true));
32
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,7));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,7 : normaliser:=true));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,7 : general:=true));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,2));
5
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,2 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,2^3));
5
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,2^3 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,2^3 : general:=true));
5
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5^3));
16
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5^3 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5^2));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,5^2 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,3 : normaliser:=true));
8
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,3 : normaliser:=true, all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,4 : normaliser:=true));
5
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,3^2 : normaliser:=true));
8
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,8,3^2 : normaliser:=true, all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,13 : novelties:=true));
0
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,13));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,5));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,5 : normaliser:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,5 : general:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,7));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,7 : normaliser:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,7 : general:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,2));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,8,2 : general:=true));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,13 : novelties:=true));
0
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,13));
8
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,13 : all:=false));
5
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,3^3));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,3^2));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,3^2 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,11));
5
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,11 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,5));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,5 : general:=true));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,5 : normaliser:=true));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,7));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,7 : general:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,9,7 : normaliser:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,13 : novelties:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,13 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,31 : novelties:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,31 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,29 : novelties:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,37 : novelties:=true));
8
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,37 : novelties:=true, all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,31));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,31 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,37));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,37 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,3));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,10,3 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,7 : novelties:=true));
8
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,7 : novelties:=true, all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,11 : novelties:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,11 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,13 : novelties:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,19 : novelties:=true));
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,2 : novelties:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,13));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,13 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,19));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,2));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,7));
16
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,7 : all:=false));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,7 : special:=true, all:=false));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,7 : general:=true, all:=false));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,7 : normaliser:=true, all:=false));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,10,13));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,11,5));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,11,5 : all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,11,7));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,11,13));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(0,11,13 : all:=false));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,17 : novelties:=true));
8
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,17 : novelties:=true, all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,23 : novelties:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,23 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,13 : novelties:=true));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,13 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,19));
8
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,19 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,29));
24
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,29 : all:=false));
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,23));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(1,12,23 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,7 : novelties:=true));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,7 : novelties:=true, all:=false));
1
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,41));
12
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,41 : all:=false));
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,3^2));
4
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,2^2));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,11^3));  # slow
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,11));
6
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,11 : all:=false));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,2));
3
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,7));
2
gap> Length(C9SubgroupsOrthogonalGroupGeneric(-1,12,7 : all:=false));
1

#
gap> SetInfoLevel(InfoClassicalMaximals, oldClassicalMaximalsInfoLevel);
gap> STOP_TEST("ClassicalMaximals.tst", 0);
