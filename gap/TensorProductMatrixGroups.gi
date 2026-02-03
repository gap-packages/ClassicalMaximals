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
    SUd1FormIdentityMat := ConjugateToSesquilinearForm(SU(d1, q), "U", IdentityMat(d1, F), F);
    SUd2FormIdentityMat := ConjugateToSesquilinearForm(SU(d2, q), "U", IdentityMat(d2, F), F);

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
    SetInvariantSesquilinearForm(result, rec(matrix := IdentityMat(d, F), baseDomain := F));
    return ConjugateToStandardForm(result, "U", F);
end);

# Construction as in Proposition 7.2 of [HR05]
BindGlobal("TensorProductStabilizerInSp",
function(epsilon, d1, d2, q)
    local field, one, I_d1, I_d2, gens, size, Spgen, orthogonalGens, SOgen, Z_1, Z,
    E, standardSymplecticForm, standardBilinearForm, formMatrix, result;

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
    one := One(field);
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

    # Calculate the form preserved by the constructed group
    standardSymplecticForm := AntidiagonalHalfOneMat(d1, field);
    if epsilon = 0 then
        standardBilinearForm := IdentityMat(d2, field);
    elif epsilon = 1 then
        standardBilinearForm := AntidiagonalMat(d2, field);
    elif epsilon = -1 then
        standardBilinearForm := IdentityMat(d2, field);
        if IsEvenInt(d2 * (q - 1) / 4) then
            standardBilinearForm[1, 1] := PrimitiveElement(field);
        fi;
    fi;
    
    formMatrix := LiftFormsToTensorProduct([standardSymplecticForm, standardBilinearForm], field);
    result := MatrixGroupWithSize(field, gens, size);
    SetInvariantBilinearForm(result, rec(matrix := formMatrix, baseDomain := field));
    return ConjugateToStandardForm(result, "S", field);
end);

# Construction as in Proposition 7.3 of [HR10]
BindGlobal("OrthogonalTensorProductStabilizerInOmega",
function(epsilon, epsilon_1, epsilon_2, d1, d2, q)
    local d, field, zeta, gens, size, F1, F2, F, orthogonalGens_1, orthogonalGens_2,
    squareDiscriminant_1, squareDiscriminant_2, G_1, G_2, one, xi, alpha, beta,
    A, B, E_1, E_2, D, gen, result;

    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be odd");
    fi;

    if epsilon_1 = epsilon_2 and d1 = d2 then
        ErrorNoReturn("[<epsilon_1>, <d1>] must not be equal to [<epsilon_2>, <d2>]");
    fi;

    if d1 < 3 or d2 < 3 then
        ErrorNoReturn("<d1> and <d2> must be at least 3");
    fi;

    if epsilon_1 = 0 then
        if IsEvenInt(d1) then
            ErrorNoReturn("<d1> must be odd");
        fi;
    elif epsilon_1 in [-1, 1] then
        if IsOddInt(d1) then
            ErrorNoReturn("<d1> must be even");
        fi;
    else
        ErrorNoReturn("<epsilon_1> must be in [-1, 0, 1]");
    fi;

    if epsilon_2 = 0 then
        if IsEvenInt(d2) then
            ErrorNoReturn("<d2> must be odd");
        fi;
    elif epsilon_2 in [-1, 1] then
        if IsOddInt(d2) then
            ErrorNoReturn("<d2> must be even");
        fi;
    else
        ErrorNoReturn("<epsilon_2> must be in [-1, 0, 1]");
    fi;

    d := d1 * d2;

    if epsilon = 0 then
        if IsEvenInt(d) then
            ErrorNoReturn("<d> must be odd");
        fi;
    elif epsilon in [-1, 1] then
        if IsOddInt(d) then
            ErrorNoReturn("<d> must be even");
        fi;
    else
        ErrorNoReturn("<epsilon> must be in [-1, 0, 1]");
    fi;

    # This condition is implicitely assumed in [HR10] and [KL90]
    if epsilon_1 = 0 and epsilon_2 <> 0 then
        ErrorNoReturn("<epsilon2> must be 0 if <epsilon_1> is 0]");
    fi;

    # In this case we use symmetry to restrict the epsilons,
    # the papers also implicitly do this
    if epsilon = 1 and epsilon_1 = -1 and epsilon_2 = 1 then
        ErrorNoReturn("by symmetry, we disallow this case");
    fi;

    # In this case we use symmetry to restrict the dimensions,
    # the papers also implicitly do this
    if (epsilon = 0 or (epsilon = 1 and epsilon_1 = epsilon_2)) and d1 >= d2 then
        ErrorNoReturn("by symmetry, we assume d1 < d2 in this case");
    fi;

    if (epsilon = -1) <> (epsilon_1 = -1 and epsilon_2 = 0) then
        ErrorNoReturn("<epsilon> = -1 must be equivalent to <epsilon_1> = -1 and <epsilon_2> = 0");
    fi;

    field := GF(q);
    zeta := PrimitiveElement(field);
    gens := [];

    # Size according to Table 2.7 in [BHR13], another factor
    # will be added in case d1 and d2 are even.
    size := 2 * SizeOmega(epsilon_1, d1, q) * SizeOmega(epsilon_2, d2, q);

    if epsilon = 0 then

        F1 := AntidiagonalMat(d1, field);
        F2 := AntidiagonalMat(d2, field);
        F := KroneckerProduct(F1, F2);

        orthogonalGens_1 := StandardGeneratorsOfOrthogonalGroup(0, d1, q);
        orthogonalGens_2 := StandardGeneratorsOfOrthogonalGroup(0, d2, q);

        Add(gens, KroneckerProduct(orthogonalGens_1.S, orthogonalGens_2.S));

    elif IsEvenInt(d1) and epsilon_2 = 0 then

        squareDiscriminant_1 := epsilon_1 = (-1) ^ QuoInt((q - 1) * d1, 4);

        F1 := IdentityMat(d1, field);
        if not squareDiscriminant_1 then
            F1[1, 1] := zeta;
        fi;
        F2 := IdentityMat(d2, field);
        F := KroneckerProduct(F1, F2);

        orthogonalGens_1 := AlternativeGeneratorsOfOrthogonalGroup(d1, q, squareDiscriminant_1);
        orthogonalGens_2 := AlternativeGeneratorsOfOrthogonalGroup(d2, q, true);

        Add(gens, KroneckerProduct(IdentityMat(d1, field), orthogonalGens_2.S));

    else
        # In this case we have epsilon = 1 and d1, d2 even

        squareDiscriminant_1 := epsilon_1 = (-1) ^ QuoInt((q - 1) * d1, 4);
        squareDiscriminant_2 := epsilon_2 = (-1) ^ QuoInt((q - 1) * d2, 4);

        orthogonalGens_1 := AlternativeGeneratorsOfOrthogonalGroup(d1, q, squareDiscriminant_1);
        orthogonalGens_2 := AlternativeGeneratorsOfOrthogonalGroup(d2, q, squareDiscriminant_2);

        Add(gens, KroneckerProduct(orthogonalGens_1.S, IdentityMat(d2, field)));
        Add(gens, KroneckerProduct(IdentityMat(d1, field), orthogonalGens_2.S));

        G_1 := KroneckerProduct(orthogonalGens_1.G, IdentityMat(d2, field));
        G_2 := KroneckerProduct(IdentityMat(d1, field), orthogonalGens_2.G);

        # The following is dark magic from Proposition 7.1 in [HR10], with
        # the idea being that alpha ^ 2 + beta ^ 2 = zeta.
        one := One(field);
        xi := PrimitiveElement(GF(q ^ 2));
        alpha := xi ^ QuoInt(q + 1, 2) * (xi - xi ^ q) / (xi + xi ^ q);
        beta := 2 * zeta / (xi + xi ^ q);
        A := [[alpha, beta], [beta, -alpha]];
        B := AntidiagonalMat([zeta, one], field);
        E_1 := KroneckerProduct(IdentityMat(d1 / 2, field), A);
        E_2 := KroneckerProduct(IdentityMat(d2 / 2, field), A);

        F1 := IdentityMat(d1, field);
        if not squareDiscriminant_1 then
            F1[1, 1] := zeta;
            E_1{[1, 2]}{[1, 2]} := B;
        fi;
        F2 := IdentityMat(d2, field);
        if not squareDiscriminant_2 then
            F2[1, 1] := zeta;
            E_2{[1, 2]}{[1, 2]} := B;
        fi;

        F := KroneckerProduct(F1, F2);
        D := KroneckerProduct(E_1, E_2 ^ (-1));

        if (epsilon_1 = -1 and epsilon_2 = -1) or
           (epsilon_1 = 1 and epsilon_2 = 1 and squareDiscriminant_1 <> squareDiscriminant_2) or
           (epsilon_1 = 1 and epsilon_2 = 1 and squareDiscriminant_1 = squareDiscriminant_2 and d mod 8 = 4) or
           (epsilon_1 = 1 and epsilon_2 = -1 and not (squareDiscriminant_1 and squareDiscriminant_2)) then

            size := 4 * size;

            # [HR10] tells us to 'adjoin appropriate products' of G_1, G_2 and D
            # to our generators, essentially meaning 'somehow throw in those 3
            # matrices while making sure that they have spinor norm 1'. This
            # monstrosity achieves just that, using the fact that G_i has
            # spinor norm 1 iff squareDiscriminant_{3 - i} by Lemma 7.2 (2) in [HR10].
            # A short calculation using the mixed product property of the
            # Kronecker product shows that G_1 ^ 2, G_2 ^ 2 and D ^ 2 are all in
            # SO(epsilon_1, d1, q) \otimes SO(epsilon_2, d2, q) already, so if
            # exactly one of the matrices has spinor norm -1, we do not adjoin its
            # square and instead just adjoin the other two.
            if squareDiscriminant_2 then
                Add(gens, G_1);
                if squareDiscriminant_1 then
                    # This case is quite rare, but not impossible:
                    # It first appears for parameters 1, -1, -1, 6, 10, 3
                    Add(gens, G_2);
                    if FancySpinorNorm(F, field, D) = 1 then
                        # And this case is probably impossible
                        Add(gens, D);
                    fi;
                else
                    if FancySpinorNorm(F, field, D) = 1 then
                        Add(gens, D);
                    else
                        Add(gens, G_2 * D);
                    fi;
                fi;
            else
                if squareDiscriminant_1 then
                    Add(gens, G_2);
                    if FancySpinorNorm(F, field, D) = 1 then
                        Add(gens, D);
                    else
                        Add(gens, G_1 * D);
                    fi;
                else
                    Add(gens, G_1 * G_2);
                    if FancySpinorNorm(F, field, D) = 1 then
                        # This case is probably impossible
                        Add(gens, D);
                    else
                        # choosing G_1 here is arbitrary since both
                        # G_1 and G_2 have spinor norm -1 here.
                        Add(gens, G_1 * D);
                    fi;
                fi;
            fi;

        else

            size := 8 * size;

            Add(gens, G_1);
            Add(gens, G_2);
            Add(gens, D);

        fi;

    fi;

    for gen in orthogonalGens_1.generatorsOfOmega do
        Add(gens, KroneckerProduct(gen, IdentityMat(d2, field)));
    od;

    for gen in orthogonalGens_2.generatorsOfOmega do
        Add(gens, KroneckerProduct(IdentityMat(d1, field), gen));
    od;

    result := MatrixGroupWithSize(field, gens, size);
    CM_SetInvariantQuadraticFormFromMatrix(result, BilinearToQuadraticForm(F), field);

    if epsilon = -1 then
        return ConjugateToStandardForm(result, "O-", field);
    elif epsilon = 0 then
        return ConjugateToStandardForm(result, "O", field);
    else
        return ConjugateToStandardForm(result, "O+", field);
    fi;
end);

# Construction as in Proposition 7.4 of [HR10]
BindGlobal("SymplecticTensorProductStabilizerInOmega",
function(d1, d2, q)
    local d, m, gcd, field, one, gens, SpGen, size, zeta, A, B, Q, result;

    if IsOddInt(d1) or IsOddInt(d2) then
        ErrorNoReturn("<d1> and <d2> must be even");
    fi;

    if d1 >= d2 then
        ErrorNoReturn("<d1> must be less than <d2>");
    fi;

    d := d1 * d2;
    m := QuoInt(d, 2);
    gcd := Gcd(2, q - 1);
    field := GF(q);
    one := One(field);
    gens := [];

    for SpGen in GeneratorsOfGroup(Sp(d1, q)) do
        Add(gens, KroneckerProduct(SpGen, IdentityMat(d2, field)));
    od;

    for SpGen in GeneratorsOfGroup(Sp(d2, q)) do
        Add(gens, KroneckerProduct(IdentityMat(d1, field), SpGen));
    od;

    # Size according to Table 2.7 in [BHR13]
    size := SizeSp(d1, q) * SizeSp(d2, q);
    if d mod 8 = 4 or IsEvenInt(q) then
        size := QuoInt(size, gcd);
    else
        zeta := PrimitiveElement(field);
        A := IdentityMat(d1, field);
        A{[1..d1 / 2]}{[1..d1 / 2]} := zeta * IdentityMat(d1 / 2, field);
        B := IdentityMat(d2, field);
        B{[1..d2 / 2]}{[1..d2 / 2]} := zeta ^ (-1) * IdentityMat(d2 / 2, field);
        Add(gens, KroneckerProduct(A, B));
    fi;

    Q := KroneckerProduct(AntidiagonalHalfOneMat(d1, field) / gcd,
                          AntidiagonalHalfOneMat(d2, field) / gcd);
    Q{[m + 1..d]}{[1..m]} := NullMat(m, m, field);

    result := MatrixGroupWithSize(field, gens, size);
    CM_SetInvariantQuadraticFormFromMatrix(result, Q, field);

    return ConjugateToStandardForm(result, "O+", field);
end);
