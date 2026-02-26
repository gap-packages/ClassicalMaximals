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
    # adjust G,4 to have determinant 1
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
