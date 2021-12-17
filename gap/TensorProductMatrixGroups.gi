# Construction as in Proposition 7.1 of [HR05]
BindGlobal("TensorProductStabilizerInSL",
function(d1, d2, q)
    local F, d, c, k, g, zeta, C, Id1, Id2, gens, SLd1Gens, SLd2Gens,
    diagonalGenerator1, diagonalGenerator2, solution, size;
    if not d1 > 1 or not d1 < d2 then
        ErrorNoReturn("<d1> must be strictly between 1 and <d2>");
    fi;

    F := GF(q);
    d := d1 * d2;
    k := Gcd(d, q - 1);
    g := Gcd(d1, d2, q - 1);
    c := QuoInt(Gcd(d1, q - 1) * Gcd(d2, q - 1) * g, k);
    zeta := PrimitiveElement(F);
    C := zeta^(QuoInt((q - 1), k)) * IdentityMat(d, F); # generates the center of SL(d, q)
    Id1 := One(SL(d1 ,q));
    Id2 := One(SL(d2 ,q));

    gens := [C];
    SLd1Gens := GeneratorsOfGroup(SL(d1, q));
    SLd2Gens := GeneratorsOfGroup(SL(d2, q));
    Add(gens,KroneckerProduct(SLd1Gens[1], Id2)); # corresponds to S in [HR05]
    Add(gens,KroneckerProduct(SLd1Gens[2], Id2)); # corresponds to T in [HR05]
    Add(gens,KroneckerProduct(Id1, SLd2Gens[1])); # corresponds to U in [HR05]
    Add(gens,KroneckerProduct(Id1, SLd2Gens[2])); # corresponds to V in [HR05]

    if not c = 1 then
        diagonalGenerator1 := GLMinusSL(d1, q); # diagonal matrix [zeta, 1, ..., 1]
        diagonalGenerator2 := GLMinusSL(d2, q);
        # Solving the modular congruence d2 * x + d1 * y = 0 mod (q - 1) by
        # solving the matrix equation (d2, d1, q - 1) * (x, y, t) = 0 over the
        # integers.
        for solution in NullspaceIntMat([[d2], [d1], [q - 1]]) do
            Add(gens, 
                KroneckerProduct(diagonalGenerator1 ^ solution[1],
                                 diagonalGenerator2 ^ solution[2]));
        od;
    fi;

    # Size according to Table 2.7 in [BHR13]
    size := SizeSL(d1, q) * SizeSL(d2, q) * g;
    return MatrixGroupWithSize(F, gens, size);
end);

# Construction as in Proposition 7.3 of [HR05]
# We use the identity matrix as our hermitian form.
BindGlobal("TensorProductStabilizerInSU",
function(d1, d2, q)
    local d, F, zeta, generators, SUd1FormIdentityMat, SUd2FormIdentityMat, C,
    c, eta, diagonalMat1, diagonalMat2, solution, result, size;
    if not d1 < d2 or not d1 > 1 then
        ErrorNoReturn("<d1> must be strictly between 1 and <d2>");
    fi;

    d := d1 * d2;
    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    generators := [];

    # generate the central product SU(d1, q) o SU(d2, q)
    SUd1FormIdentityMat := ConjugateToSesquilinearForm(SU(d1, q), "U", IdentityMat(d1, F));
    SUd2FormIdentityMat := ConjugateToSesquilinearForm(SU(d2, q), "U", IdentityMat(d2, F));

    generators := List(GeneratorsOfGroup(SUd1FormIdentityMat), 
                       g -> KroneckerProduct(g, IdentityMat(d2, F)));
    Append(generators, List(GeneratorsOfGroup(SUd2FormIdentityMat),
                            g -> KroneckerProduct(IdentityMat(d1, F), g)));

    # add a generating scalar
    C := zeta ^ QuoInt(q ^ 2 - 1, Gcd(q + 1, d)) * IdentityMat(d, F);
    Add(generators, C);

    c := Gcd(d1, q + 1) * Gcd(d2, q + 1) * Gcd(d1, d2, q + 1) / Gcd(d, q + 1);
    if not c = 1 then
        eta := zeta ^ (q - 1);
        diagonalMat1 := DiagonalMat(Concatenation([eta], List([2..d1], i -> zeta ^ 0)));
        diagonalMat2 := DiagonalMat(Concatenation([eta], List([2..d2], i -> zeta ^ 0)));
        # we additionally want to take the generators 
        # diagonalMat1 ^ x * diagonalMat2 ^ y, where * is to be understood as a
        # Kronecker product. For these generators to have determinant 1, we
        # need d2 * x + d1 * y = 0 mod q + 1, which we solve by solving the
        # matrix equation (d2, d1, q + 1) * (x, y, t) = 0 over the integers.
        for solution in NullspaceIntMat([[d2], [d1], [q + 1]]) do
            Add(generators,
                KroneckerProduct(diagonalMat1 ^ solution[1],
                                 diagonalMat2 ^ solution[2]));
        od;
    fi;

    # Size according to Table 2.7 in [BHR13]
    size := SizeSU(d1, q) * SizeSU(d2, q) * Gcd(q + 1, d1, d2);
    result := MatrixGroupWithSize(F, generators, size);
    # change back fixed form into standard GAP form Antidiag(1, ..., 1)
    SetInvariantSesquilinearForm(result, rec(matrix := IdentityMat(d, F)));
    return ConjugateToStandardForm(result, "U");
end);

# Construction as in Proposition 7.2 of [HR05]
BindGlobal("TensorProductStabilizerInSp",
function(epsilon, d1, d2, q)
    local field, I_d1, I_d2, gens, size, Spgen, orthogonalGens, SOgen, Z_1, Z, E, result;

    if IsOddInt(d1) then
        ErrorNoReturn("<d1> must be even");
    fi;

    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be odd");
    fi;

    if d2 < 3 then
        ErrorNoReturn("<d2> must be at least 3");
    fi;

    if IsOddInt(d2) then
        if epsilon <> 0 then
            ErrorNoReturn("<epsilon> must be 0 since <d2> is odd");
        fi;
    else
        if not epsilon in [-1, 1] then
            ErrorNoReturn("<epsilon> must be +1 or -1 since <d2> is even");
        fi;
    fi;

    field := GF(q);
    I_d1 := IdentityMat(d1, field);
    I_d2 := IdentityMat(d2, field);
    gens := [];

    # Size according to Table 2.7 in [BHR13], a factor of 2
    # will be added in case d2 is even.
    size := QuoInt(SizeSp(d1, q) * SizeGO(epsilon, d2, q), 2);

    for Spgen in GeneratorsOfGroup(Sp(d1, q)) do
        Add(gens, KroneckerProduct(Spgen, I_d2));
    od;

    orthogonalGens := GeneratorsOfOrthogonalGroup(epsilon, d2, q);

    for SOgen in orthogonalGens.generatorsOfSO do
        Add(gens, KroneckerProduct(I_d1, SOgen));
    od;

    # This might be redundant in case d2 is odd, since
    # then the matrix orthogonalGens.D is -I_d2 and
    # the Kronecker product -I_d should be contained
    # in the group generated by X and Y already.
    Add(gens, KroneckerProduct(I_d1, orthogonalGens.D));

    if IsEvenInt(d2) then
        Z_1 := NormSpMinusSp(d1, q);
        Z := KroneckerProduct(Z_1, I_d2);
        E := KroneckerProduct(I_d1, orthogonalGens.E);
        Add(gens, Inverse(Z) * E);
        size := 2 * size;
    fi;

    result := MatrixGroupWithSize(field, gens, size);
    return ConjugateToStandardForm(result, "S");
end);
