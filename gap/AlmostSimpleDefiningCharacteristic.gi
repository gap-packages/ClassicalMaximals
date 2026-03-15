# Extension of GL(n,q) by graph isomorphisms - degree is twice as large.
InstallGlobalFunction("GLExtensionByGraphAutomorphism",
function(n, q)
    local G, gens, mat, G2;
    Assert(0, n >= 3);
    G := GL(n, q);
    gens := List(GeneratorsOfGroup(G), g -> DirectSumMat(g, TransposedMat(g^-1)));
    mat := NullMat(2*n, 2*n, GF(q));
    mat{[1..n]}{[n+1..2*n]} := One(G);
    mat{[n+1..2*n]}{[1..n]} := One(G);
    Add(gens, mat);
    G2 := Group(gens);
    # Assert(1, Size(G2) = 2 * Size(G));
    return G2;
end);

# Extension of GU(n,q) by frobenius isomorphism - degree is twice as large.
InstallGlobalFunction("GUExtensionByFrobeniusAutomorphism",
function(n, q)
    local G, gens, mat, G2;
    Assert(0, n >= 3);
    G := GU(n, q);
    gens := List(GeneratorsOfGroup(G), g -> DirectSumMat(g, EntrywisePowerMat(g, q)));
    mat := NullMat(2*n, 2*n, GF(q^2));
    mat{[1..n]}{[n+1..2*n]} := One(G);
    mat{[n+1..2*n]}{[1..n]} := One(G);
    Add(gens, mat);
    G2 := Group(gens);
    # Assert(1, Size(G2) = 2 * Size(G));
    return G2;
end);

# Given an absolutely irreducible matrix group G over the finite field F
# and its natural G-module, decide whether G has an equivalent representation over
# a subfield of F. If so, return the representation over the smallest possible
# field.
# TODO this function should most likely be revised (especially the use of
# SetFieldOfMatrixGroup) and carefully documented.
InstallGlobalFunction("CM_OverSmallerField",
function(M, G)
    local b, H;
    b := RECOG.BaseChangeForSmallestPossibleField(G, M);
    H := MatrixGroup(b.field, b.newgens);
    SetFieldOfMatrixGroup(H, b.field);
    return H;
end);

# Construction of L2q < O(d,q)
# Cf. Proposition 5.3.6 (ii) and (iii) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_OrthogSL2",
function(d, q)
    local special, general, normaliser, w, G, M, MM, T, A, S, forms, i;

    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # construct SL(2, q) in O(d, q) for d odd
    Assert(0, IsOddInt(d));
    Assert(0, IsOddInt(q));
    # construct GL(2, q) as SL(2, q) with extra generator
    w := PrimitiveElement(GF(q));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(2,q)),
                                         [DiagonalMat([w, One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    MM := M;
    for i in [3..d] do
        T := TensorProductGModule(M, MM);
        MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = i);
    od;
    A := Group(MTX.Generators(MM));
    S := w^(QuoInt(d - 1, 2)) * IdentityMat(d, GF(q));
    A := GroupByGenerators([A.1, A.2, A.3 * S^(-1)]);
    Assert(0, DeterminantMat(A.3) = One(GF(q)));
    A := ConjugateToStandardForm(A, "O", GF(q));
    if normaliser then
        G := GroupByGenerators([A.1, A.2, A.3, w * IdentityMat(d, GF(q))]);
    elif general then
        G := GroupByGenerators([A.1, A.2, A.3, (-1) * IdentityMat(d, GF(q))]);
    elif special or CM_InOmega(A.3, d, q, 0) then
        # A.3 in Omega(0, d, q) seems to happen for d = 1 or 7 mod 8.
        G := A;
    else
        G := GroupByGenerators([A.1, A.2]);
    fi;
    return ConjugateToStandardFormAutoType(G, GF(q));
end);

# Construction of 2.L2q < Sp(d,q)
# Cf. Proposition 5.3.6 (i) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_SymplecticSL2",
function(d, q)
    local normaliser, w, G, M, MM, T, A, S, DA, tmat, i;

    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # construct SL(2,q) in Sp(d,q) for d even
    Assert(0, IsEvenInt(d));
    Assert(0, IsOddInt(q));
    # construct GL(2,q) as SL(2,q) with extra generator
    w := PrimitiveElement(GF(q));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(2,q)),
                                         [DiagonalMat([w, One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    MM := M;
    for i in [3..d] do
        T := TensorProductGModule(M, MM);
        MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = i);
    od;
    A := Group(MTX.Generators(MM));
    S := w^(QuoInt(d - 2, 2)) * IdentityMat(d, GF(q));
    A := GroupByGenerators([A.1, A.2, A.3 * S^(-1)]);
    DA := GroupByGenerators([A.1, A.2]);
    # tmat := ConjugateToStandardForm(DA, "S", GF(q))!.baseChangeMatrix;
    # A := A^tmat;
    if normaliser then
        return A^ConjugateToStandardForm(DA, "S", GF(q))!.baseChangeMatrix;
    else
        return ConjugateToStandardForm(DA, "S", GF(q));
    fi;
end);

# Construction of SL(3,q) < SL(6,q)
# Cf. Proposition 5.4.5 (i) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l3qdim6",
function(q)
    local general, w, G, M, T, MM, A, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;

    Assert(0, IsOddInt(q));
    w := PrimitiveElement(GF(q));
    if general then
        G := GL(3,q);
    else
        G := SL(3,q);
    fi;
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    T := TensorProductGModule(M, M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 6);
    A := Group(MTX.Generators(MM));
    if not general then
        S := w^(QuoInt((q - 1), Gcd(6, (q - 1)))) * IdentityMat(6, GF(q));
    else
        S := w * IdentityMat(6, GF(q));
    fi;
    return GroupByGenerators(Concatenation(GeneratorsOfGroup(A), [S]));
end);

# Construction of SU(3,q) < SU(6,q)
# Cf. Proposition 5.4.5 (ii) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_u3qdim6",
function(q)
    local general, normaliser, w, G, M, T, MM, A, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    Assert(0, IsOddInt(q));
    if normaliser then general := true; fi;
    w := PrimitiveElement(GF(q^2));
    if general then
        G := GU(3, q);
    else
        G := SU(3, q);
    fi;
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    T := TensorProductGModule(M, M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 6);
    A := Group(MTX.Generators(MM));
    A := ConjugateToStandardForm(A, "U", GF(q^2));
    if not general then
        S := (w^(q - 1))^(QuoInt(q + 1, Gcd(6, q + 1))) * IdentityMat(6, GF(q^2));
    elif not normaliser then
        S := w^(q - 1) * IdentityMat(6, GF(q^2));
    else
        S := w * IdentityMat(6, GF(q^2));
    fi;
    return ConjugateToStandardFormAutoType(GroupByGenerators(Concatenation(GeneratorsOfGroup(A), [S])), GF(q^2));
end);

# Construction of SL(2,q^3).3 < Sp(8,q)
# Cf. Proposition 5.3.7 in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l2q3dim8",
function(q)
    local normaliser, w, G, M, M1, M2, T, u, H;

    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # SL(2,q^3).3 <= Sp(8,q)
    w := PrimitiveElement(GF(q^3));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(2, q^3)),
                                         [DiagonalMat([w, One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^3));
    M1 := ConjugateModule(M, q);
    M2 := ConjugateModule(M1, q);
    T := TensorProductGModule(M, TensorProductGModule(M1, M2));
    Assert(0, MTX.IsIrreducible(T));
    u := PermutationMat((2,3,5)(4,7,6), 8, GF(q^3));
    # induces field automorphism
    H := GroupByGenerators(Concatenation(MTX.Generators(T), [u]));
    G := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(H), GF(q^3)), H);
    Assert(0, Size(FieldOfMatrixGroup(G)) = q);
    G := ConjugateToStandardFormAutoType(G, GF(q));
    if normaliser then
        return G;
    fi;
    return ConjugateToStandardFormAutoType(GroupByGenerators([G.1, G.2, G.4]), GF(q));
end);

# Construction of L3q.3 < O^+(8,q) and L3q < O^-(8,q), respectively
# Cf. Proposition 5.4.16 in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l3qdim8",
function(q)
    local special, general, normaliser, w, G, M, T, C, M8, G8;

    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # SL(3,q)(.3) <= O+(8,q), q mod 3 = 1 or O-(8,q), q mod 3 = 2
    w := PrimitiveElement(GF(q));
    G := GLExtensionByGraphAutomorphism(3,q);
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    T := TensorProductGModule(M, M);
    C := List(MTX.CollectedFactors(T), c -> c[1]);
    M8 := First(C, c -> MTX.Dimension(c) = 8);
    G8 := Group(MTX.Generators(M8));
    G8 := ConjugateToStandardFormAutoType(G8, GF(q));
    if normaliser then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G8),
                                             [w * IdentityMat(8, GF(q))]));
    elif general and IsOddInt(q) then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G8),
                                             [(-1)*One(GF(q)) * IdentityMat(8, GF(q))]));
    elif (special or general) and IsEvenInt(q) then
        G := G8;
    elif special or q mod 3 = 1 then
        G := GroupByGenerators([G8.1, G8.2, (-1)*One(GF(q)) * IdentityMat(8, GF(q))]);
    else
        G := GroupByGenerators([G8.1, G8.2]);
    fi;
    return ConjugateToStandardFormAutoType(G, GF(q));
end);

# Construction of U3q.3 < O^+(8,q) and U3q < O^-(8,q), respectively
# Cf. Proposition 5.4.18 in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_u3qdim8",
function(q)
    local special, general, normaliser, w, G, M, T, C, M8, G8, G8q;

    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # SU(3,q)(.3) <= O+(8,q), q mod 3 = 2 or O-(8,q), q mod 3 = 1
    w := PrimitiveElement(GF(q));
    G := GUExtensionByFrobeniusAutomorphism(3,q);
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    T := TensorProductGModule(M, M);
    C := List(MTX.CollectedFactors(T), c -> c[1]);
    M8 := First(C, c -> MTX.Dimension(c) = 8);
    G8 := Group(MTX.Generators(M8));
    G8q := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(G8), GF(q^2)), G8);
    Assert(0, Size(FieldOfMatrixGroup(G8q)) = q);
    if q mod 3 = 2 then
        G8q := ConjugateToStandardForm(G8q, "O+", GF(q));
    else
        G8q := ConjugateToStandardForm(G8q, "O-", GF(q));
    fi;
    if normaliser then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G8q),
                                             [w * IdentityMat(8, GF(q))]));
    elif general and IsOddInt(q) then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G8q),
                                             [(-1)*One(GF(q)) * IdentityMat(8, GF(q))]));
    elif (special or general) and IsEvenInt(q) then
        G := G8q;
    elif special or q mod 3 = 2 then
        G := GroupByGenerators([G8q.1, G8q.2, (-1)*One(GF(q)) * IdentityMat(8, GF(q))]);
    else
        G := GroupByGenerators([G8q.1, G8q.2]);
    fi;
    return ConjugateToStandardFormAutoType(G, GF(q));
end);

# Construction of L2q^2.2 < O(9,q)
# Cf. Proposition 5.3.8 in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l2q2dim9",
function(q)
    local special, general, normaliser, w, z, G, M, M1, T, u, H, C, DG, tmat, form, tform, scal, rt, g3, g4, gg;

    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # L(2,q^2).2 <= O(9,q)
    w := PrimitiveElement(GF(q^2));
    z := w^(q + 1);
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(2,q^2)),
                                         [DiagonalMat([w, One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    M1 := ConjugateModule(M, q);
    T := TensorProductGModule(M, M1);
    Assert(0, MTX.IsIrreducible(T));
    u := PermutationMat((2,3), 4, GF(q^2));
    # induces field automorphism
    H := GroupByGenerators(Concatenation(MTX.Generators(T), [u]));
    G := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(H), GF(q^2)), H);
    Assert(0, Size(FieldOfMatrixGroup(G)) = q);
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    T := TensorProductGModule(M, M);
    C := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 9);
    G := Group(MTX.Generators(C));
    DG := GroupByGenerators([G.1, G.2]);
    tmat := ConjugateToStandardForm(DG, "O", GF(q))!.baseChangeMatrix;
    G := G^tmat;
    # adjust G.3 to fix form and G.4 to have determinant 1
    form := CM_SymmetricBilinearForm(GroupByGenerators([G.1, G.2]), GF(q));
    tform := G.3 * form * TransposedMat(G.3);
    scal := form[1,9] / tform[1,9];
    rt := RootFFE(GF(q), scal, 2);
    Assert(0, rt <> fail);
    g3 := G.3 * (rt * IdentityMat(9, GF(q)));
    if not IsOne(DeterminantMat(g3)) then
        g3 := - g3;
    fi;
    if IsOne(DeterminantMat(G.4)) then
        g4 := G.4;
    else
        g4 := - G.4;
    fi;
    G := GroupByGenerators([G.1, G.2, g3, g4]);
    if normaliser then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                             [z * IdentityMat(9, GF(q))]));
    elif general then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                             [(-1)*One(GF(q)) * IdentityMat(9, GF(q))]));
    elif not special then
        if CM_InOmega(g3, 9, q, 0) then
            gg := g3;
        elif CM_InOmega(g4, 9, q, 0) then
            gg := g4;
        else
            gg := g3 * g4;
        fi;
        G := GroupByGenerators([G.1, G.2, gg]);
    fi;
    return ConjugateToStandardFormAutoType(G, GF(q));
end);

# Construction of (3.)L3q^2(.3).2 < SL(9,q)
# Cf. Proposition 5.4.20 in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l3q2dim9l",
function(q)
    local general, w, z, G, M, M1, T, u, H, g4;

    general := ValueOption("general");
    if general = fail then general := false; fi;

    # (3.)L(3,q^2)(.3).2 <= L(9,q)
    w := PrimitiveElement(GF(q^2));
    z := w^(q + 1);
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(3,q^2)),
                                         [DiagonalMat([w, One(w), One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    M1 := ConjugateModule(M, q);
    T := TensorProductGModule(M, M1);
    Assert(0, MTX.IsIrreducible(T));
    u := PermutationMat((2,4)(3,7)(6,8), 9, GF(q^2));
    # induces field automorphism
    H := GroupByGenerators(Concatenation(MTX.Generators(T), [u]));
    G := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(H), GF(q^2)), H);
    Assert(0, Size(FieldOfMatrixGroup(G)) = q);
    # adjust G.4 to have determinant 1
    if IsOne(DeterminantMat(G.4)) then
        g4 := G.4;
    else
        g4 := - G.4;
    fi;
    G := GroupByGenerators([G.1, G.2, G.3, g4]);
    if general then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                               [z * IdentityMat(9, GF(q))]));
    else
        # get power of G.3 with determinant 1
        return GroupByGenerators([G.1, G.2, G.3^Order(DeterminantMat(G.3)), G.4]);
    fi;
end);

# Construction of (3.)L3q^2(.3).2 < SU(9,q)
# Cf. Proposition 5.4.21 in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l3q2dim9u",
function(q)
    local general, normaliser, w, z, G, M, M1, T, u, tmat, g4;

    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # (3.)L(3,q^2)(.3).2 <= L(9,q)
    w := PrimitiveElement(GF(q^2));
    z := w^(q - 1);
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(3,q^2)),
                                         [DiagonalMat([w, One(w), One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    M1 := ConjugateModule(M, q);
    T := TensorProductGModule(DualGModule(M), M1);
    Assert(0, MTX.IsIrreducible(T));
    u := PermutationMat((2,4)(3,7)(6,8), 9, GF(q^2));
    # induces field automorphism
    G := GroupByGenerators(Concatenation(MTX.Generators(T), [u]));
    tmat := ConjugateToStandardFormAutoType(GroupByGenerators([G.1, G.2]), GF(q^2))!.baseChangeMatrix;
    G := GroupByGenerators(List(GeneratorsOfGroup(G), g -> g ^ tmat));
    # Adjust G.4 to have determinant 1
    if IsOne(DeterminantMat(G.4)) then
        g4 := G.4;
    else
        g4 := - G.4;
    fi;
    G := GroupByGenerators([G.1, G.2, G.3, g4]);
    if normaliser then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                             [w * IdentityMat(9, GF(q^2))]));
    elif general then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                             [z * IdentityMat(9, GF(q^2))]));
    else
        # get power of G.3 with determinant 1
        G := GroupByGenerators([G.1, G.2, G.3^Order(DeterminantMat(G.3)), G.4]);
    fi;
    return ConjugateToStandardFormAutoType(G, GF(q^2));
end);

# Construction of L3q.(q-1,3) < SL(10,q)
# Cf. Proposition 5.4.6 (i) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l3qdim10",
function(q)
    local general, w, G, M, T, MM, o, tp, g3, rt, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;

    Assert(0, PrimePowersInt(q)[1] >= 5);
    w := PrimitiveElement(GF(q));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(3,q)),
                                         [DiagonalMat([w, One(w), One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    T := TensorProductGModule(TensorProductGModule(M, M), M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 10);
    G := Group(MTX.Generators(MM));
    if general then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                               [w * IdentityMat(10, GF(q))]));
    fi;
    # get intersection with SL
    o := Order(DeterminantMat(G.3));
    tp := 3^Valuation(o, 3);
    g3 := G.3^(QuoInt(o, tp));
    rt := RootFFE(GF(q), DeterminantMat(g3), 10);
    Assert(0, rt <> fail);
    g3 := g3 * (rt^(-1) * IdentityMat(10, GF(q)));
    S := w^(QuoInt(q - 1, Gcd(10, q - 1))) * IdentityMat(10, GF(q));
    return GroupByGenerators([G.1, G.2, g3, S]);
end);

# Construction of U3q.(q+1,3) < SU(10,q)
# Cf. Proposition 5.4.6 (ii) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_u3qdim10",
function(q)
    local general, normaliser, w, G, M, T, MM, A, o, tp, g3, rt, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    Assert(0, PrimePowersInt(q)[1] >= 5);
    if normaliser then general := true; fi;
    w := PrimitiveElement(GF(q^2));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SU(3,q)),
                                         [GUMinusSU(3,q)]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    T := TensorProductGModule(TensorProductGModule(M, M), M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 10);
    A := Group(MTX.Generators(MM));
    G := ConjugateToStandardForm(A, "U", GF(q^2));
    if normaliser then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                               [w * IdentityMat(10, GF(q^2))]));
    fi;
    if general then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                             [w^(q - 1) * IdentityMat(10, GF(q^2))]));
        return ConjugateToStandardForm(G, "U", GF(q^2));
    fi;
    # get intersection with SU
    o := Order(DeterminantMat(G.3));
    tp := 3^Valuation(o, 3);
    g3 := G.3^(QuoInt(o, tp));
    rt := RootFFE(GF(q^2), DeterminantMat(g3), 10 * (q - 1));
    Assert(0, rt <> fail);
    g3 := g3 * (rt^-(q - 1) * IdentityMat(10, GF(q^2)));
    S := (w^(q - 1))^(QuoInt(q + 1, Gcd(10, q + 1))) * IdentityMat(10, GF(q^2));
    return ConjugateToStandardForm(GroupByGenerators([G.1, G.2, g3, S]), "U", GF(q^2));
end);

# Construction of ((q-1,4)/2).L4q.((q-1,4)/2) < SL(10,q)
# Cf. Proposition 5.4.7 (i) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l4qdim10",
function(q)
    local general, w, G, M, T, MM, o, tp, g3, rt, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;

    Assert(0, PrimePowersInt(q)[1] >= 3);
    w := PrimitiveElement(GF(q));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(4,q)),
                                         [DiagonalMat([w, One(w), One(w), One(w)])]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    T := TensorProductGModule(M, M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 10);
    G := Group(MTX.Generators(MM));
    if general then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                               [w * IdentityMat(10, GF(q))]));
    fi;
    # get intersection with SL
    o := Order(DeterminantMat(G.3));
    tp := 2^Valuation(o, 2);
    g3 := G.3^(QuoInt(2 * o, tp));
    rt := RootFFE(GF(q), DeterminantMat(g3), 10);
    Assert(0, rt <> fail);
    g3 := g3 * (rt^(-1) * IdentityMat(10, GF(q)));
    S := w^(QuoInt(q - 1, Gcd(10, q - 1))) * IdentityMat(10, GF(q));
    return GroupByGenerators([G.1, G.2, g3, S]);
end);

# Construction of ((q+1,4)/2).U4q.((q+1,4)/2) < SU(10,q)
# Cf. Proposition 5.4.7 (ii) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_u4qdim10",
function(q)
    local general, normaliser, w, G, M, T, MM, A, o, tp, g3, rt, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    Assert(0, PrimePowersInt(q)[1] >= 3);
    if normaliser then general := true; fi;
    w := PrimitiveElement(GF(q^2));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(SU(4,q)),
                                         [GUMinusSU(4,q)]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    T := TensorProductGModule(M, M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 10);
    A := Group(MTX.Generators(MM));
    G := ConjugateToStandardForm(A, "U", GF(q^2));
    if normaliser then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                               [w * IdentityMat(10, GF(q^2))]));
    fi;
    if general then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                             [w^(q - 1) * IdentityMat(10, GF(q^2))]));
        return ConjugateToStandardForm(G, "U", GF(q^2));
    fi;
    # get intersection with SU
    o := Order(DeterminantMat(G.3));
    tp := 2^Valuation(o, 2);
    g3 := G.3^(QuoInt(2 * o, tp));
    rt := RootFFE(GF(q^2), DeterminantMat(g3), 10 * (q - 1));
    Assert(0, rt <> fail);
    g3 := g3 * (rt^-(q - 1) * IdentityMat(10, GF(q^2)));
    S := (w^(q - 1))^(QuoInt(q + 1, Gcd(10, q + 1))) * IdentityMat(10, GF(q^2));
    return ConjugateToStandardForm(GroupByGenerators([G.1, G.2, g3, S]), "U", GF(q^2));
end);

# Construction of SL(5,q) < SL(10,q)
# Cf. Proposition 5.4.8 (i) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_l5qdim10",
function(q)
    local general, w, G, M, T, MM, A, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;

    w := PrimitiveElement(GF(q));
    if general then
        G := GL(5,q);
    else
        G := SL(5,q);
    fi;
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    T := TensorProductGModule(M, M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 10);
    A := Group(MTX.Generators(MM));
    if not general then
        S := w^(QuoInt(q - 1, Gcd(10, q - 1))) * IdentityMat(10, GF(q));
    else
        S := w * IdentityMat(10, GF(q));
    fi;
    return GroupByGenerators(Concatenation(GeneratorsOfGroup(A), [S]));
end);

# Construction of SU(5,q) < SU(10,q)
# Cf. Proposition 5.4.8 (ii) in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_u5qdim10",
function(q)
    local general, normaliser, w, G, M, T, MM, A, S;

    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    if normaliser then general := true; fi;
    w := PrimitiveElement(GF(q^2));
    if general then
        G := GU(5,q);
    else
        G := SU(5,q);
    fi;
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    T := TensorProductGModule(M, M);
    MM := First(MTX.CompositionFactors(T), c -> MTX.Dimension(c) = 10);
    A := Group(MTX.Generators(MM));
    A := ConjugateToStandardForm(A, "U", GF(q^2));
    if not general then
        S := (w^(q - 1))^(QuoInt(q + 1, Gcd(10, q + 1))) * IdentityMat(10, GF(q^2));
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(A), [S]));
        return ConjugateToStandardForm(G, "U", GF(q^2));
    fi;
    if not normaliser then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(A),
                                               [w^(q - 1) * IdentityMat(10, GF(q^2))]));
    else
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(A),
                                             [w * IdentityMat(10, GF(q^2))]));
    fi;
    return ConjugateToStandardFormAutoType(G, GF(q^2));
end);

# Construction of S4q < O^+(10,q) and S4q < O^-(4,q), respectively
# Cf. Proposition 5.5.2 in [BHR13]
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_sp4qdim10",
function(q)
    local special, general, normaliser, w, G, M, T, C, M10, tmat, form, tform, scal, rt, g3, sign;

    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # Sp4q <= O^+(10,q) (q = 1 mod 4) of O^-(10,q) (q = 3 mod 4)
    Assert(0, IsOddInt(q));
    w := PrimitiveElement(GF(q));
    G := GroupByGenerators(Concatenation(GeneratorsOfGroup(Sp(4,q)),
                                         [NormSpMinusSp(4,q)]));
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q));
    T := TensorProductGModule(M, M);
    C := List(MTX.CollectedFactors(T), c -> c[1]);
    M10 := First(C, c -> MTX.Dimension(c) = 10);
    G := Group(MTX.Generators(M10));
    tmat := ConjugateToStandardFormAutoType(Group([G.1, G.2]), GF(q))!.baseChangeMatrix;
    G := G^tmat;
    form := CM_SymmetricBilinearForm(Group([G.1, G.2]), GF(q));
    tform := G.3 * form * TransposedMat(G.3);
    scal := form[1,10] / tform[1,10];
    rt := RootFFE(GF(q), scal, 2);
    Assert(0, rt <> fail);
    g3 := G.3 * (rt * IdentityMat(10, GF(q)));
    G := GroupByGenerators([G.1, G.2, g3]);
    if q mod 4 = 1 then
        sign := 1;
    else
        sign := -1;
    fi;
    Assert(0, IsOne(DeterminantMat(g3)) and not CM_InOmega(g3, 10, q, sign));
    if normaliser then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                               [w * IdentityMat(10, GF(q))]));
    elif special or general then
        G := GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                               [(-1)*One(GF(q)) * IdentityMat(10, GF(q))]));
    else
        G := GroupByGenerators([G.1, G.2, (-1)*One(GF(q)) * IdentityMat(10, GF(q))]);
    fi;
    return ConjugateToStandardFormAutoType(G, GF(q));
end);

# Construction of Spin_8^-(q) - by John Bray
# Two visible submodules generated by V.i, i in {1,4,6,7,10,11,13,16} and {2,3,5,8,9,12,14,15}.
# x23o only required when q=3.
# x1, x7, x8 to the same named elements in Spin_8^+(q) construction.
# x4 vaguely correponds to element named x4 in Spin_8^+(q) construction, but has order q+1 instead of q-1.
# x23 corresponds to x2*x3^-1 in Spin_8^+(q) construction, and x23o is also in <x2,x3>.
# x26 and x46 correspond to the elements x2^x6 and x4^x6 in Spin_8^+(q) construction.
InstallGlobalFunction("CM_Spin8Minus",
function(q)
    local F, o, b, bb, c, cc, a, aa, G, x8;
    F := GF(q^2);
    o := One(F);
    b := PrimitiveElement(F);
    bb := 1 / b;
    c := b^(q - 1);
    cc := 1 / c;
    a := b^(q + 1);
    aa := 1 / a;
    G := Group([[
    [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0]] * o
    ,[
    [1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]] * o
    ,[
    [1,0,0,-c^q,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,1,c,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,1,0,0,-c^q,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,1,c,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,1,0,0,-c^q,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,1,c,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-c^q],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,1,c,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]] * o
    ,[
    [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]] * o
    ,[
    [c,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,c^-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,c,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,c^-1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,c,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,c^-1,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,c,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,c^-1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,c,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,c^-1,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,c,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,c^-1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,c,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,c^-1,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,c,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c^-1]] * o
    ,[
    [a,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,a,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,a^-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,a^-1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,a,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,a,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,a^-1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,a^-1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,a,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,a,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,a^-1,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,a^-1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,a,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,a,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,a^-1,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,a^-1]] * o
    ,[
    [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]] * o
    ]);
    x8:=[
    [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0]] * o;
    return rec(G := G, x8 := x8);
end);

# 2.O(7,q) as C9-subgroup of O^+(8,q)
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_TwoO7",
function(q)
    local G, M, C, H;
    G := CM_Spin8Minus(q).G;
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    C := First(MTX.CompositionFactors(M));
    G := Group(MTX.Generators(C));
    if q = 2 then
        H := GroupByGenerators([G.1 * G.5, G.3, G.4, G.7]);
    else
        H := GroupByGenerators([G.1 * G.5, G.3, G.4, G.6, G.7]);
    fi;
    H := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(H), GF(q^2)), H);
    Assert(0, Size(FieldOfMatrixGroup(H)) = q);
    return ConjugateToStandardForm(H, "O+", GF(q));
end);

# 2.O^-(8,q) as C9-subgroup of O^+(8,q^2)
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_TwoOminus8",
function(q)
    local G, M, C;
    G := CM_Spin8Minus(q).G;
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    C := First(MTX.CompositionFactors(M));
    G := Group(MTX.Generators(C));
    return ConjugateToStandardForm(G, "O+", GF(q^2));
end);

# ExtendToBasis(Q, V) - quick and dirty, requires checking
# Given a list Q of linearly independent vectors in the vector space V,
# return a list of length Dimension(V) whose first entries are Q and which
# extends Q to a basis of V.
# Throws an error if Q contains vectors not in V, is linearly dependent,
# or has length greater than Dimension(V).
InstallGlobalFunction("CM_ExtendToBasis",
function(Q, V)
    local r, d, B, S, b;
    Assert(0, IsList(Q));
    Assert(0, IsVectorSpace(V));
    r := Length(Q);
    d := Dimension(V);
    Assert(0, r <= d);
    Assert(0, ForAll(Q, q -> q in V));
    Assert(0, Dimension(Subspace(V, Q)) = r);
    B := BasisVectors(Basis(V));
    S := ShallowCopy(Q);
    for b in B do
        if Length(S) = d then
            break;
        fi;
        if RankMat(Concatenation(S, [b])) = Length(S) + 1 then
            Add(S, b);
        fi;
    od;
    return S;
end);

# return map from Magma rep of O^-(8,q) to 2.O^-(8,q) over GF(q^2), q odd.
# may be wrong by scalar factor -1, but correct on elements of odd order.
InstallGlobalFunction("CM_O8qMapToCover",
function(q)
    local G, M, C, G1, G2, ng, T, AT, form, formi, ATtoG1, MT, M8, M56, imM8, imM56,
          trans64, G8, G8g, inds, SG8, M8g, M8b, M8btoM8, TT, CT, M28, imM28, V, extbas,
          trans28, trans28i, M28g, G56, SG56, SM56g, SM56, gh1, M56b, trans56, trans56i,
          M56bg, M56btoM56, SG8toG1;
    Assert(0, IsOddInt(q));
    G := CM_Spin8Minus(q).G;
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    C := List(MTX.CollectedFactors(M), c -> c[1]);
    G1 := Group(MTX.Generators(C[1])); # domain of returned map
    G2 := Group(MTX.Generators(C[2]));
    ng := Length(GeneratorsOfGroup(G));
    # form tensor product of two 8-dimensional modules
    T := GModuleByMats(List([1..ng], i -> KroneckerProduct(GeneratorsOfGroup(G1)[i],
                                                           GeneratorsOfGroup(G2)[i])),
                       GF(q^2));
    AT := Group(MTX.Generators(T));
    # first construct map from AT to G1
    form := CM_SymmetricBilinearForm(G1, GF(q^2));
    Assert(0, form <> fail);
    formi := form^(-1);
    ATtoG1 := function(m)
        local x, formx, mum, mu;
        x := RECOG.HomTensorFactor(rec(blocksize := 8, field := GF(q^2)), m);
        Assert(0, x <> fail);
        # x should fix form mod scalars
        formx := x * form * TransposedMat(x);
        mum := formx * formi^(-1);
        mu := mum[1,1];
        Assert(0, mum = mu * IdentityMat(8, GF(q^2)));
        x := RootFFE(GF(q^2), mu^-1, 2) * x;
        # Order is missing for IsPlistMatrixRep
        # see https://github.com/gap-system/gap/issues/6270
        if IsOddInt(Order(Unpack(m))) and IsEvenInt(Order(x)) then
            x := x * ((-1)*One(GF(q^2)) * IdentityMat(8));
        fi;
        return x;
    end;

    MT := List(MTX.BasesMinimalSubmodules(T), sub -> MTX.InducedActionSubmodule(T, sub));
    M8 := First(MT, c -> MTX.Dimension(c) = 8);
    M56 := First(MT, c -> MTX.Dimension(c) = 56);
    imM8 := First(MTX.Homomorphisms(M8, T));
    imM56 := First(MTX.Homomorphisms(M56, T));
    trans64 := Matrix(GF(q^2), Concatenation(List([1..8], i -> imM8[i]*One(GF(q^2))),
                                             List([1..56], i -> imM56[i]*One(GF(q^2)))));

    # Need horrible hack to deal with case when some action generators
    # of M8 are trivial or equal.
    G8 := Group(MTX.Generators(M8));
    G8g := GeneratorsOfGroup(G8);
    inds := List([1..ng], function(i)
        local ag;
        ag := MTX.Generators(M8)[i];
        if ag = IdentityMat(MTX.Dimension(M8), MTX.Field(M8)) then
            return 0;
        else
            return Position(G8g, ag);
        fi;
    end);
    SG8 := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(G8), GF(q^2)), G8);
    Assert(0, Size(FieldOfMatrixGroup(SG8)) = q);
    SG8 := ConjugateToStandardForm(SG8, "O-", GF(q));  # should not be standard copy of O^-(8,q)
    M8g := List([1..ng], function(i)
        if inds[i] = 0 then
            return IdentityMat(8, GF(q^2));
        else
            return GeneratorsOfGroup(SG8)[inds[i]];
        fi;
    end);
    M8b := GModuleByMats(M8g, GF(q^2));
    Assert(0, MTX.IsIrreducible(M8b) and MTX.IsIrreducible(M8));
    M8btoM8 := MTX.IsomorphismIrred(M8b, M8);
    Assert(0, M8btoM8 <> fail);
    # more efficient to go back to working over GF(q)
    M8g := List([1..ng], function(i)
        if inds[i] = 0 then
            return IdentityMat(8, GF(q));
        else
            return GeneratorsOfGroup(SG8)[inds[i]];
        fi;
    end);

    # Our next aim is to construct the homomorphism SG8 -> SG56
    # We construct SG56 from SG8 in following.
    TT := GModuleByMats(List([1..ng], i -> KroneckerProduct(M8g[i], M8g[i])), GF(q));
    CT := List(MTX.CollectedFactors(TT), c -> c[1]);
    M28 := First(CT, c -> MTX.Dimension(c) = 28);
    M28 := First(List(SMTX.MinimalSubGModules(M28, TT),
                      sub -> MTX.InducedActionSubmodule(TT, sub)));
    imM28 := First(MTX.Homomorphisms(M28, TT));
    V := GF(q)^64;
    extbas := CM_ExtendToBasis(imM28, V);
    trans28 := ExtractSubMatrix(extbas, [1..28], [1..64]);
    trans28i := ExtractSubMatrix(extbas^-1, [1..64], [1..28]);
    # Get from element g in SG8 to element in action group of M28 by
    # g -> trans28 * KroneckerProduct(g,g) * trans28i
    # and extracting
    M28g := MTX.Generators(M28);
    TT := GModuleByMats(List([1..ng], i -> KroneckerProduct(M8g[i], M28g[i])), GF(q));
    # get 56-dimensional module M56 over GF(q)
    G56 := Group(MTX.Generators(M56));
    SG56 := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(G56), GF(q^2)), G56);
    Assert(0, Size(FieldOfMatrixGroup(SG56)) = q);
    SM56g := List([1..ng], function(i)
        if inds[i] = 0 then
            return IdentityMat(56, GF(q));
        else
            return GeneratorsOfGroup(SG56)[inds[i]];
        fi;
    end);

    SM56 := GModuleByMats(SM56g, GF(q));
    gh1 := First(MTX.Homomorphisms(SM56, TT));
    gh1 := MTX.Homomorphism(SM56, TT, gh1);
    M56b := Image(gh1);
    M56b := MTX.InducedActionSubmodule(TT, MTX.SubmoduleGModule(TT, Basis(M56b)));

    #CT := List(MTX.CollectedFactors(TT), c -> c[1]);
    #M56b := First(CT, c -> MTX.Dimension(c) = 56);
    #M56b := First(List(SMTX.MinimalSubGModules(M56b, TT),
    #                   sub -> MTX.InducedActionSubmodule(TT, sub)));
    imM56 := First(MTX.Homomorphisms(M56b, TT));
    V := GF(q)^224;
    extbas := CM_ExtendToBasis(imM56, V);
    trans56 := ExtractSubMatrix(extbas, [1..56], [1..224]);
    trans56i := ExtractSubMatrix(extbas^-1, [1..224], [1..56]);
    # Get from element g in G8 mapping to gg in action group of M28
    # to action group of M56 by
    # g -> trans56 * KroneckerProduct(g,gg) * trans56i;

    # now need to get M56b back over to GF(q^2)
    M56bg := MTX.Generators(M56b);
    M56b := GModuleByMats(M56bg, GF(q^2));
    Assert(0, MTX.IsIrreducible(M56b) and MTX.IsIrreducible(M56));
    M56btoM56 := MTX.IsomorphismIrred(M56b, M56);
    Assert(0, M56btoM56 <> fail);

    # Now we are ready to define the required map!
    SG8toG1 := function(g)  # g in SG8 = Omega^-(8,q)
        local gg, ggg, m64;
        gg := trans28 * KroneckerProduct(g, g) * trans28i;
        ggg := trans56 * KroneckerProduct(g, gg) * trans56i;
        g := g * One(GF(q^2));  # ?
        ggg := ggg * One(GF(q^2));  # ?
        m64 := Matrix(GF(q^2), DirectSumMat(M8btoM8^-1 * g * M8btoM8, M56btoM56^-1 * ggg * M56btoM56));
        m64 := Matrix(GF(q^2), trans64^-1 * m64 * trans64);
        return ATtoG1(m64);
    end;
    return SG8toG1;
end);

# 2.O(7,q).2 as C9-subgroup of normaliser in GL(8,q) of O^+(8,q)
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_TwoO72",
function(q)
    local H, phi, Hgens;
    H := OmegaStabilizerOfNonDegenerateSubspace(-1, 8, q, 0, 1);
    phi := CM_O8qMapToCover(q);
    Hgens := List([1..Length(GeneratorsOfGroup(H))], i -> phi(GeneratorsOfGroup(H)[i]));
    H := GroupByGenerators(Hgens);
    # G *modulo scalars* has equivalent representation over GF(q)
    # TODO Understand whether/why the following scalars are the right ones
    H := GroupByGenerators([H.1, H.2, Z(q^2)^((q+1)/2) * H.3]);
    H := CM_OverSmallerField(GModuleByMats(GeneratorsOfGroup(H), GF(q^2)), H);
    Assert(0, Size(FieldOfMatrixGroup(H)) = q);
    # TODO Conjugate H s.t. it preserves our standard form *up to a scalar*.
    # Ideally, the function ConjugateToStandardForm should be extended to include this
    # functionality.
    # The forms package does not reliably detect the preserved form.
    # oldForm := PreservedSesquilinearForms(H)[1];
    # newForm := BilinearFormByMatrix(InvariantBilinearForm(Omega(1, 8, q)).matrix, GF(q));
    # baseChangeMatrix := BaseChangeToCanonical(oldForm)^-1 * BaseChangeToCanonical(newForm);
    # H := MatrixGroup(GF(q), List(GeneratorsOfGroup(H), g -> g ^ baseChangeMatrix));
    return GroupByGenerators(Concatenation(GeneratorsOfGroup(H),
                                           [PrimitiveElement(GF(q)) * IdentityMat(8, GF(q))]));
end);

# 2.O^-(8,q).2 as C9-subgroup of normaliser in GL(8,q^2) of O^+(8,q^2)
InstallGlobalFunction("AlmostSimpleDefiningCharacteristic_TwoOminus82",
function(q)
    local G, go, z, AandB, a, b, mats, g, stdform, mat, ngo, f, H, Hg, Hgc, phi,
          Hgi, Hgci, M, Mi, x, Hgc2, Hgc2i, M2i;
    G := Omega(-1, 8, q);
    go := GOMinusSO(-1, 8, q);
    # Construct an element ngo of Normaliser(GL(8,q),GO^-(8,q)) - GO^-(8,q)
    # with determinant Z(q)^4 as in Magma's NormGOMinusGO(8,q,-1).
    # It induces the standard diagonal automorphism described in
    # [BHR], 1.7.1 Standard outer automorphisms.
    z := PrimitiveElement(GF(q));
    AandB := SolveQuadraticCongruence(z, q);
    a := AandB.a; b := AandB.b;
    mats := List([1..3], i -> [[a, -b], [b, a]]);
    Add(mats, One(GF(q)) * [[0, -1], [z, 0]]);
    g := DirectSumMat(mats);
    stdform := IdentityMat(8, GF(q)); stdform[8,8] := z;
    mat := ConjugateToSesquilinearForm(G, "O-B", stdform, GF(q))!.baseChangeMatrix;
    ngo := mat * g * mat^-1;
    # need generating set of odd order elements
    repeat
        g := PseudoRandom(G);
        f := PrimePowersInt(Order(g));
        f := List([1..Length(f)/2], i -> [f[2*i-1], f[2*i]]);
    until Size(f) > 1 or (Size(f) = 1 and f[1,1] <> 2);
    if f[1,1] = 2 then
        g := g^(2^f[1,2]);
    fi;
    H := GroupByGenerators([g, g^PseudoRandom(G)]);
    while not IsAbsolutelyIrreducible(H) do
        H := GroupByGenerators(Concatenation(GeneratorsOfGroup(H), [g^PseudoRandom(G)]));
    od;
    while false do  # TODO while not RecogniseClassical(H)
        H := GroupByGenerators(Concatenation(GeneratorsOfGroup(H), [g^PseudoRandom(G)]));
    od;
    Hg := GeneratorsOfGroup(H);
    Hgc := List(Hg, h -> h^ngo);

    # now map over to 2.O^-(8,q) in GO^+(8,q^2)
    phi := CM_O8qMapToCover(q);
    Hgi := List(Hg, h -> phi(h));
    Hgci := List(Hgc, h -> phi(h));
    G := GroupByGenerators(Hgi);
    M := GModuleByMats(GeneratorsOfGroup(G), GF(q^2));
    Mi := GModuleByMats(Hgci, GF(q^2));
    x := MTX.IsomorphismModules(M, Mi);
    if x = fail then
        # "try other one"
        Hgc2 := List(Hg, h -> h^(ngo * go));
        Hgc2i := List(Hgc2, h -> phi(h));
        M2i := GModuleByMats(Hgc2i, GF(q^2));
        x := MTX.IsomorphismModules(M, M2i);
        Assert(0, x <> fail);
    fi;
    G := GroupByGenerators(Concatenation(Hgi, [x]));
    # TODO Conjugate G s.t. it preserves our standard form *up to a scalar*.
    # Ideally, the function ConjugateToStandardForm should be extended to include this
    # functionality.
    # The forms package does not reliably detect the preserved form.
    # oldForm := PreservedSesquilinearForms(G)[1];
    # newForm := BilinearFormByMatrix(InvariantBilinearForm(Omega(1, 8, q^2)).matrix, GF(q^2));
    # baseChangeMatrix := BaseChangeToCanonical(oldForm)^-1 * BaseChangeToCanonical(newForm);
    # G := MatrixGroup(GF(q^2), List(GeneratorsOfGroup(G), g -> g ^ baseChangeMatrix));
    return GroupByGenerators(Concatenation(GeneratorsOfGroup(G),
                                           [PrimitiveElement(GF(q^2)) * IdentityMat(8, GF(q^2))]));
end);
