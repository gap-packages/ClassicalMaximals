# Return the subgroup of <M>SL(n, q)</M> stabilizing the
# <A>k</A>-dimensional subspace of <M>F^n</M>, where <C>F := GF(q)</C>,
# consisting of all vectors whose first <C>n-k</C> entries are zero.
# Construction as in Proposition 4.1 of [HR05]
BindGlobal("SLStabilizerOfSubspace",
function(n, q, k)
    local F, A5, dirProd, z, T, size;
    F := GF(q);
    z := PrimitiveElement(F);
    A5 := DiagonalMat(
        Concatenation([z], List([2..n - 1], i -> z ^ 0), [z ^ -1])
    );
    dirProd := MatDirectProduct(SL(n - k, q), SL(k, q));
    T := IdentityMat(n, F) + SquareSingleEntryMatrix(F, n, 1, n - k + 1);
    # Size according to Table 2.3 of [BHR13]
    size := q ^ (k * (n - k)) * SizeSL(k, q) * SizeSL(n - k, q) * (q - 1);
    return MatrixGroupWithSize(F, Concatenation([A5], GeneratorsOfGroup(dirProd), [T]), size);
end);

# Construction as in Proposition 4.5 of [HR05]
# The subspace stabilised is < e_1, e_2, ..., e_k >.
BindGlobal("SUStabilizerOfIsotropicSubspace",
function(d, q, k)
    local F, zeta, generators, J, generator, nu, T1, T2, mu, D, size,
        generatorOfSL, generatorOfSU, result;

    if not k <= d / 2 then
        ErrorNoReturn("<k> must not be larger than <d> / 2");
    fi;

    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    generators := [];
    J := AntidiagonalMat(k, F);

    # The following elements generate SL(k, q ^ 2) x SU(d - 2 * k, q).
    # Note that we actually do need SL(k, q ^ 2) here and not GL(k, q ^ 2) as
    # claimed in the proof of Proposition 4.5 in [HR05] since some of the
    # generators constructed below would not have determinant 1 otherwise.
    for generatorOfSL in GeneratorsOfGroup(SL(k, q ^ 2)) do
        generator := IdentityMat(d, F);
        generator{[1..k]}{[1..k]} := generatorOfSL;
        generator{[d - k + 1..d]}{[d - k + 1..d]} := J * HermitianConjugate(generatorOfSL, q) ^ (-1) 
                                                       * J;
        Add(generators, generator);
    od;
    if d - 2 * k > 0 then
        for generatorOfSU in GeneratorsOfGroup(ConjugateToSesquilinearForm(SU(d - 2 * k, q), 
                                                                           "U", 
                                                                           AntidiagonalMat(d - 2 * k,
                                                                                           F))) 
        do
            generator := IdentityMat(d, F);
            generator{[k + 1..d - k]}{[k + 1..d - k]} := generatorOfSU;
            Add(generators, generator);
        od;
    fi;

    # the following two transvections generate a group of order q ^ (k * (2 * d - 3 * k))
    if IsOddInt(q) then
        nu := zeta ^ QuoInt(q + 1, 2);
    else
        nu := zeta ^ 0;
    fi;
    T1 := IdentityMat(d, F) + nu * SquareSingleEntryMatrix(F, d, d, 1);
    if d - 2 * k > 1 then
        # Note that in the proof of Proposition 4.5 in [HR05], there is a + sign
        # instead of the - sign below, but this is wrong and will lead to T2
        # not being in SU(d, q).
        T2 := IdentityMat(d, F) + SquareSingleEntryMatrix(F, d, d, d - k)   
                                        - SquareSingleEntryMatrix(F, d, k + 1, 1);
    elif d - 2 * k = 1 then
        if IsEvenInt(q) then
            T2 := IdentityMat(d, F) + zeta * SquareSingleEntryMatrix(F, d, d, 1)
                                            + SquareSingleEntryMatrix(F, d, d, QuoCeil(d, 2))
                                            + SquareSingleEntryMatrix(F, d, QuoCeil(d, 2), 1);
        else
            mu := SolveFrobeniusEquation("P", -2 * zeta ^ 0, q);
            # Again, note that in the proof of Proposition 4.5 in [HR05], there is
            # a + sign instead of the - sign below, but this is wrong and will
            # lead to T2 not being in SU(d, q).
            T2 := IdentityMat(d, F) + SquareSingleEntryMatrix(F, d, d, 1)
                                            - mu * SquareSingleEntryMatrix(F, d, d, QuoCeil(d, 2))
                                            + mu ^ q * SquareSingleEntryMatrix(F, d, QuoCeil(d, 2), 1);
        fi;
    else
        # if d = 2 * k, we do not need a second transvection
        T2 := IdentityMat(d, F);
    fi;
    generators := Concatenation(generators, [T1, T2]);

    # finally a diagonal matrix of order q ^ 2 - 1 (or q - 1 if d = 2 * k)
    D := IdentityMat(d, F);
    if d - 2 * k > 1 then
        D[1, 1] := zeta;
        D[k + 1, k + 1] := zeta ^ (-1);
        D[d - k, d - k] := zeta ^ q;
        D[d, d] := zeta ^ (-q);
        Add(generators, D);
    elif d - 2 * k = 1 then
        D[1, 1] := zeta;
        D[k + 1, k + 1] := zeta ^ (q - 1);
        D[d, d] := zeta ^ (-q);
        Add(generators, D);
    else
        D[1, 1] := zeta ^ (q + 1);
        D[d, d] := zeta ^ (-q - 1);
        Add(generators, D);
    fi;

    # Size according to Table 2.3 of [BHR13]
    if d - 2 * k > 0 then
        size := q ^ (k * (2 * d - 3 * k)) * SizeSL(k, q ^ 2) 
                                          * SizeSU(d - 2 * k, q) 
                                          * (q ^ 2 - 1);
    else
        size := q ^ (k * (2 * d - 3 * k)) * SizeSL(k, q ^ 2)
                                          * (q - 1);
    fi;

    result := MatrixGroupWithSize(F, generators, size);
    SetInvariantSesquilinearForm(result, rec(matrix := AntidiagonalMat(d, F)));
    return ConjugateToStandardForm(result, "U");
end);

# Construction as in Proposition 4.6 of [HR05]
BindGlobal("SUStabilizerOfNonDegenerateSubspace",
function(d, q, k)
    local F, zeta, generators, kHalf, dHalf, generator, determinantShiftMatrix,
        alpha, beta, size, generatorOfSUSubspace, generatorOfSUComplement,
        standardFormSUk, standardFormSUdMinusk, result;
    if k >= d / 2 then
        ErrorNoReturn("<k> must be less than <d> / 2");
    fi;

    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    generators := [];
    kHalf := QuoInt(k, 2);
    dHalf := QuoInt(d, 2);
    standardFormSUk := AntidiagonalMat(k, F);
    standardFormSUdMinusk := AntidiagonalMat(d - k, F);

    if IsEvenInt(k) then
        # We stabilise the subspace < e_1, ..., e_{kHalf}, f_{kHalf}, ..., f_1 >  
        # and its complement (e_1, ..., e_{d / 2}, (w), f_{d / 2}, ..., f_1 is
        # the standard basis).
        #
        # The following matrices generate SU(k, q) x SU(d - k, q).
        for generatorOfSUSubspace in GeneratorsOfGroup(ConjugateToSesquilinearForm(SU(k, q), 
                                                                                   "U",
                                                                                   standardFormSUk)) 
        do
            generator := IdentityMat(d, F);
            generator{[1..kHalf]}{[1..kHalf]} := 
                generatorOfSUSubspace{[1..kHalf]}{[1..kHalf]};
            generator{[d - kHalf + 1..d]}{[d - kHalf + 1..d]} :=
                generatorOfSUSubspace{[kHalf + 1..k]}{[kHalf + 1..k]};
            generator{[d - kHalf + 1..d]}{[1..kHalf]} := 
                generatorOfSUSubspace{[kHalf + 1..k]}{[1..kHalf]};
            generator{[1..kHalf]}{[d - kHalf + 1..d]} := 
                generatorOfSUSubspace{[1..kHalf]}{[kHalf + 1..k]};
            Add(generators, generator);
        od;
        for generatorOfSUComplement in GeneratorsOfGroup(ConjugateToSesquilinearForm(SU(d - k, q),
                                                                                     "U",
                                                                                     standardFormSUdMinusk)) 
        do
            generator := IdentityMat(d, F);
            generator{[kHalf + 1..d - kHalf]}{[k / 2 + 1..d - kHalf]} := 
                generatorOfSUComplement;
            Add(generators, generator);
        od;

        # Now add a diagonal matrix where each of the SU(k, q) and SU(d - k, q)
        # blocks has determinant zeta ^ +- (q - 1).
        determinantShiftMatrix := DiagonalMat(Concatenation([zeta],
                                                            List([2..kHalf], i -> zeta ^ 0),
                                                            [zeta ^ (-1)],
                                                            List([kHalf + 2..d - kHalf -1], i -> zeta ^ 0),
                                                            [zeta ^ q],
                                                            List([d - kHalf + 1..d - 1], i -> zeta ^ 0),
                                                            [zeta ^ (-q)]));
        Add(generators, determinantShiftMatrix);
    elif IsOddInt(k) and IsOddInt(d) then        
        # We stabilise the subspace < e_1, ..., e_{kHalf}, w, f_{kHalf}, ..., f_1 >  
        # and its complement (e_1, ..., e_{d / 2}, w, f_{d / 2}, ..., f_1 is
        # the standard basis; division by 2 is to be understood as integer
        # division here).
        #
        # The following matrices generate SU(k, q) x SU(d - k, q).
        for generatorOfSUSubspace in GeneratorsOfGroup(ConjugateToSesquilinearForm(SU(k, q), 
                                                                                   "U",
                                                                                   standardFormSUk)) 
        do
            generator := IdentityMat(d, F);
            generator{[1..kHalf]}{[1..kHalf]} := 
                generatorOfSUSubspace{[1..kHalf]}{[1..kHalf]};
            generator{[d - kHalf + 1..d]}{[d - kHalf + 1..d]} := 
                generatorOfSUSubspace{[kHalf + 2..k]}{[kHalf + 2..k]};
            generator{[d - kHalf + 1..d]}{[1..kHalf]} := 
                generatorOfSUSubspace{[kHalf + 2..k]}{[1..kHalf]};
            generator{[1..kHalf]}{[d - kHalf + 1..d]} := 
                generatorOfSUSubspace{[1..kHalf]}{[kHalf + 2..k]};
            generator{[dHalf + 1]}{[1..kHalf]} := 
                generatorOfSUSubspace{[kHalf + 1]}{[1..kHalf]};
            generator{[dHalf + 1]}{[dHalf + 1]} := 
                generatorOfSUSubspace{[kHalf + 1]}{[kHalf + 1]};
            generator{[dHalf + 1]}{[d - kHalf + 1..d]} := 
                generatorOfSUSubspace{[kHalf + 1]}{[kHalf + 2..k]};
            generator{[1..kHalf]}{[dHalf + 1]} := 
                generatorOfSUSubspace{[1..kHalf]}{[kHalf + 1]};
            generator{[d - kHalf + 1..d]}{[dHalf + 1]} := 
                generatorOfSUSubspace{[kHalf + 2..k]}{[kHalf + 1]};
            Add(generators, generator);
        od;
        for generatorOfSUComplement in GeneratorsOfGroup(ConjugateToSesquilinearForm(SU(d - k, q), 
                                                                                     "U",
                                                                                     standardFormSUdMinusk)) 
        do
            generator := IdentityMat(d, F);
            generator{[kHalf + 1..dHalf]}{[kHalf + 1..dHalf]} := 
                generatorOfSUComplement{[1..(d - k) / 2]}{[1..(d - k) / 2]};
            generator{[kHalf + 1..dHalf]}{[dHalf + 2..d - kHalf]} :=
                generatorOfSUComplement{[1..(d - k) / 2]}{[(d - k) / 2 + 1..d - k]};
            generator{[dHalf + 2..d - kHalf]}{[kHalf + 1..dHalf]} := 
                generatorOfSUComplement{[(d - k) / 2 + 1..d - k]}{[1..(d - k) / 2]};
            generator{[dHalf + 2..d - kHalf]}{[dHalf + 2..d - kHalf]} := 
                generatorOfSUComplement{[(d - k) / 2 + 1..d - k]}{[(d - k) / 2 + 1..d - k]};
            Add(generators, generator);
        od;

        # Now add a diagonal matrix where each of the SU(k, q) and SU(d - k, q)
        # blocks has determinant zeta ^ +- (q - 1).
        # Note that the choice of matrix differs from the original Magma code,
        # but this is much cleaner.
        determinantShiftMatrix := DiagonalMat(Concatenation(List([1..dHalf - 1], i -> zeta ^ 0),
                                                            [zeta ^ (-1), zeta ^ (1 - q), zeta ^ q],
                                                            List([dHalf + 3..d], i -> zeta ^ 0)));
        Add(generators, determinantShiftMatrix);
    else
        # Find alpha, beta with alpha + alpha ^ q = 1 and beta * beta ^ q = -1.
        alpha := SolveFrobeniusEquation("S", zeta ^ 0, q);
        if IsOddInt(q) then
            beta := zeta ^ QuoInt(q - 1, 2);
        else
            beta := zeta ^ 0;
        fi;
        # We stabilise the subspace < e_1, ..., e_{kHalf}, w_1, f_{kHalf}, ..., f_1 >  
        # and its complement < e_{kHalf + 1}, ..., e_{dHalf - 1}, w_2, f_{dHalf - 1}, ..., f_{kHalf + 1} >,
        # where w_1 = alpha * e_{dHalf} + f_{dHalf} and 
        #       w_2 = -alpha ^ q * beta * e_{dHalf} + beta * f_{dHalf}.
        # (e_1, ..., e_{d / 2}, f_{d / 2}, ..., f_1 is the standard basis).
        #
        # Note that, by construction of alpha and beta,
        #       e_{dHalf} = w_1 + beta ^ q * w_2
        #       f_{dHalf} = alpha ^ q * w_1 - alpha * beta ^ q * w_2
        # Also by construction of alpha and beta, our standard unitary form
        # applied to w_1 and w_1 or w_2 and w_2, respectively, each gives 1
        # again, as needed.
        #
        # The following matrices generate SU(k, q) x SU(d - k, q).
        for generatorOfSUSubspace in GeneratorsOfGroup(ConjugateToSesquilinearForm(SU(k, q), 
                                                                                   "U",
                                                                                   standardFormSUk)) 
        do
            generator := IdentityMat(d, F);
            generator{[1..kHalf]}{[1..kHalf]} := 
                generatorOfSUSubspace{[1..kHalf]}{[1..kHalf]};
            generator{[d - kHalf + 1..d]}{[d - kHalf + 1..d]} := 
                generatorOfSUSubspace{[kHalf + 2..k]}{[kHalf + 2..k]};
            generator{[d - kHalf + 1..d]}{[1..kHalf]} := 
                generatorOfSUSubspace{[kHalf + 2..k]}{[1..kHalf]};
            generator{[1..kHalf]}{[d - kHalf + 1..d]} := 
                generatorOfSUSubspace{[1..kHalf]}{[kHalf + 2..k]};
            # use w_1 = alpha * e_{dHalf} + f_{dHalf} for the following lines
            generator{[1..kHalf]}{[dHalf]} := 
                alpha * generatorOfSUSubspace{[1..kHalf]}{[kHalf + 1]};
            generator{[1..kHalf]}{[dHalf + 1]} :=
                generatorOfSUSubspace{[1..kHalf]}{[kHalf + 1]};
            generator{[d - kHalf + 1..d]}{[dHalf]} :=
                alpha * generatorOfSUSubspace{[kHalf + 2..k]}{[kHalf + 1]};
            generator{[d - kHalf + 1..d]}{[dHalf]} :=
                generatorOfSUSubspace{[kHalf + 2..k]}{[kHalf + 1]};
            # now use e_{dHalf} = w_1 + beta ^ q * w_2
            #         f_{dHalf} = alpha ^ q * w_1 - alpha * beta ^ q * w_2
            generator{[dHalf]}{[1..kHalf]} :=
                generatorOfSUSubspace{[kHalf + 1]}{[1..kHalf]}; 
            generator{[dHalf + 1]}{[1..kHalf]} :=
                alpha ^ q * generatorOfSUSubspace{[kHalf + 1]}{[1..kHalf]};
            generator{[dHalf]}{[d - kHalf + 1..d]} :=
                generatorOfSUSubspace{[kHalf + 1]}{[kHalf + 2..k]};
            generator{[dHalf + 1]}{[d - kHalf + 1..d]} :=
                alpha ^ q * generatorOfSUSubspace{[kHalf + 1]}{[kHalf + 2..k]};
            # finally, for the central 2x2-submatrix, we have to use all four
            # relations above together
            generator[dHalf, dHalf] := 
                alpha * generatorOfSUSubspace[kHalf + 1, kHalf + 1]
                    + beta ^ q * (- alpha ^ q * beta);
            generator[dHalf, dHalf + 1] := 
                generatorOfSUSubspace[kHalf + 1, kHalf + 1]
                    + beta ^ q * beta;
            generator[dHalf + 1, dHalf] :=
                alpha ^ q * alpha * generatorOfSUSubspace[kHalf + 1, kHalf + 1]
                    - alpha * beta ^ q * (- alpha ^ q * beta);
            generator[dHalf + 1, dHalf + 1] :=
                alpha ^ q * generatorOfSUSubspace[kHalf + 1, kHalf + 1]
                    - alpha * beta ^ q * beta;
            Add(generators, generator);
        od;
        for generatorOfSUComplement in GeneratorsOfGroup(ConjugateToSesquilinearForm(SU(d - k, q), 
                                                                                     "U",
                                                                                     standardFormSUdMinusk)) 
        do
            generator := IdentityMat(d, F); 
            generator{[kHalf + 1..dHalf - 1]}{[kHalf + 1..dHalf - 1]} := 
                generatorOfSUComplement{[1..dHalf - kHalf - 1]}{[1..dHalf - kHalf - 1]};
            generator{[kHalf + 1..dHalf - 1]}{[dHalf + 2..d - kHalf]} := 
                generatorOfSUComplement{[1..dHalf - kHalf - 1]}{[dHalf - kHalf + 1..d - k]};
            generator{[dHalf + 2..d - kHalf]}{[kHalf + 1..dHalf - 1]} := 
                generatorOfSUComplement{[dHalf - kHalf + 1..d - k]}{[1..dHalf - kHalf - 1]};
            generator{[dHalf + 2..d - kHalf]}{[dHalf + 2..d - kHalf]} :=
                generatorOfSUComplement{[dHalf - kHalf + 1..d - k]}{[dHalf - kHalf + 1..d - k]};
            # use w_1 = alpha * e_{dHalf} + f_{dHalf} for the following lines
            generator{[kHalf + 1..dHalf - 1]}{[dHalf]} := 
                -alpha ^ q * beta * generatorOfSUComplement{[1..dHalf - kHalf - 1]}{[dHalf - kHalf]};
            generator{[kHalf + 1..dHalf - 1]}{[dHalf + 1]} :=
                beta * generatorOfSUComplement{[1..dHalf - kHalf - 1]}{[dHalf - kHalf]};
            generator{[dHalf + 2..d - kHalf]}{[dHalf]} :=
                -alpha ^ q * beta * generatorOfSUComplement{[dHalf - kHalf + 1..d - k]}{[dHalf - kHalf]};
            generator{[dHalf + 2..d - kHalf]}{[dHalf + 1]} :=
                beta * generatorOfSUComplement{[dHalf - kHalf + 1..d - k]}{[dHalf - kHalf]};
            # now use e_{dHalf} = w_1 + beta ^ q * w_2
            #         f_{dHalf} = alpha ^ q * w_1 - alpha * beta ^ q * w_2
            generator{[dHalf]}{[kHalf + 1..dHalf - 1]} :=
                beta ^ q * generatorOfSUComplement{[dHalf - kHalf]}{[1..dHalf - kHalf - 1]}; 
            generator{[dHalf + 1]}{[kHalf + 1..dHalf - 1]} :=
                -alpha * beta ^ q * generatorOfSUComplement{[dHalf - kHalf]}{[1..dHalf - kHalf - 1]};
            generator{[dHalf]}{[dHalf + 2..d - kHalf]} :=
                beta ^ q * generatorOfSUComplement{[dHalf - kHalf]}{[dHalf - kHalf + 1..d - k]};
            generator{[dHalf + 1]}{[dHalf + 2..d - kHalf]} :=
                -alpha * beta ^ q * generatorOfSUComplement{[dHalf - kHalf]}{[dHalf - kHalf + 1..d - k]};
            # finally, for the central 2x2-submatrix, we have to use all four
            # relations above together
            generator[dHalf, dHalf] := 
                beta ^ q * (- alpha ^ q * beta) * generatorOfSUComplement[dHalf - kHalf, dHalf - kHalf]
                    + alpha;
            generator[dHalf, dHalf + 1] := 
                beta ^ q * beta * generatorOfSUComplement[dHalf - kHalf, dHalf - kHalf]
                    + zeta ^ 0;
            generator[dHalf + 1, dHalf] :=
                alpha * beta ^ q * alpha ^ q * beta * generatorOfSUComplement[dHalf - kHalf, dHalf - kHalf]
                    + alpha ^ q * alpha;
            generator[dHalf + 1, dHalf + 1] :=
                - alpha * beta ^ q * beta * generatorOfSUComplement[dHalf - kHalf, dHalf - kHalf]
                    + alpha ^ q;
            Add(generators, generator);
        od;

        # Now add a diagonal matrix where each of the SU(k, q) and SU(d - k, q)
        # blocks has determinant zeta ^ +- (q - 1). We take the matrix obtained
        # by sending w_1 to zeta ^ (q - 1) * w_1 and w_2 to zeta ^ (1 - q) * w_2.
        # Note that this choice differs from the original Magma code, but it
        # is much cleaner this way.
        determinantShiftMatrix := IdentityMat(d, F);
        determinantShiftMatrix[dHalf, dHalf] :=
            beta ^ q * (-alpha ^ q * beta) * zeta ^ (1 - q) 
                + alpha * zeta ^ (q - 1);
        determinantShiftMatrix[dHalf, dHalf + 1] :=
            beta ^ q * beta * zeta ^ (1 - q)
                + zeta ^ (q - 1);
        determinantShiftMatrix[dHalf + 1, dHalf] :=
            alpha * beta ^ q * alpha ^ q * beta * zeta ^ (1 - q)
                + alpha ^ q * alpha * zeta ^ (q - 1);
        determinantShiftMatrix[dHalf + 1, dHalf + 1] :=
            -alpha * beta ^ q * beta * zeta ^ (1 - q)
                + alpha ^ q * zeta ^ (q - 1);
        Add(generators, determinantShiftMatrix);
    fi;

    # Size according to Table 2.3 of [BHR13]
    size := SizeSU(k, q) * SizeSU(d - k, q) * (q + 1);

    result := MatrixGroupWithSize(F, generators, size);
    SetInvariantSesquilinearForm(result, rec(matrix := AntidiagonalMat(d, F)));

    return ConjugateToStandardForm(result, "U");
end);


# Construction as in Proposition 4.3 of [HR05]
BindGlobal("SpStabilizerOfIsotropicSubspace",
function(d, q, k)
    local field, gens, I, J, GLgen, Xi, Spgen, Yi;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even");
    fi;

    if k >= d / 2 then
        ErrorNoReturn("<k> must be less than <d> / 2");
    fi;

    field := GF(q);
    gens := [];
    I := IdentityMat(d, field);
    J := AntidiagonalMat(k, field);

    # For each generator of Sp(d,q), we take an
    # invertible matrix GLgen which acts on
    # the first k basis vectors and put that generator
    # into a diagonal block matrix with another invertible
    # matrix which acts on the last d - k basis vectors.
    # This way, we preserve the decomposition into
    # two isotropic subspaces.
    # With the way we construct the second block matrix,
    # the form is also preserved.
    for GLgen in GeneratorsOfGroup(GL(k, q)) do
        Xi := IdentityMat(d, field);
        Xi{[1..k]}{[1..k]} := GLgen;
        Xi{[d - k + 1 .. d]}{[d - k + 1 .. d]} := J * TransposedMat(GLgen ^ (-1)) * J;
        Add(gens, Xi);
    od;

    # These two generators are diagonal block matrices with 2x2 blocks
    # that generate a subgroup of Sp(d, q) corresponding to Sp(d - 2 * k, q).
    for Spgen in GeneratorsOfGroup(Sp(d - 2 * k, q)) do
        Yi := IdentityMat(d, field);
        Yi{[k + 1 .. d - k]}{[k + 1 .. d - k]} := Spgen;
        Add(gens, Yi);
    od;

    # This generator is mapped to matrices "with 1s down the diagonal,
    # a (k x k) block in the middle that is symmetric about the anti-diagonal,
    # and zeros elsewhere" (cf. [HR05]) by GL(k, q) while also being fixed
    # by Sp(d - 2k, q).
    Add(gens, I + SquareSingleEntryMatrix(field, d, d, 1));

    # This generator is in Sp(d, q) and stabilises the group generated by
    # the first k unit vectors.
    Add(gens, I + SquareSingleEntryMatrix(field, d, d, d - k) - SquareSingleEntryMatrix(field, d, k + 1, 1));

    # Size according to Table 2.3 of [BHR13]
    return MatrixGroupWithSize(field, gens, q ^ (k * d + QuoInt(k - 3 * k * k, 2)) * SizeGL(k, q) * SizeSp(d - 2 * k, q));
end);


# Construction as in Proposition 4.4 of [HR05]
BindGlobal("SpStabilizerOfNonDegenerateSubspace",
function(d, q, k)
    local field, gens, twok, Spgen, Xi, Yi;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even");
    fi;

    if k >= d / 2 then
        ErrorNoReturn("<k> must be less than <d> / 2");
    fi;

    field := GF(q);
    gens := [];
    twok := 2 * k;

    # These generators are block matrices of the form
    # [[A 0 B], [0 C 0], [D 0 E]] which generate
    # a subgroup corresponding to Sp(2 * k, q).
    for Spgen in GeneratorsOfGroup(Sp(twok, q)) do
        Xi := IdentityMat(d, field);
        Xi{[1..k]}{[1..k]} := Spgen{[1..k]}{[1..k]};
        Xi{[1..k]}{[d - k + 1 .. d]} := Spgen{[1..k]}{[k + 1 .. twok]};
        Xi{[d - k + 1 .. d]}{[1..k]} := Spgen{[k + 1 .. 2 * k]}{[1..k]};
        Xi{[d - k + 1 .. d]}{[d - k + 1 .. d]} := Spgen{[k + 1 .. twok]}{[k + 1 .. twok]};
        Add(gens, Xi);
    od;

    # These generators are 2x2 block matrices with blocks which
    # generate a subgroup corresponding to Sp(d - 2 * k, q).
    for Spgen in GeneratorsOfGroup(Sp(d - twok, q)) do
        Yi := IdentityMat(d, field);
        Yi{[k + 1 .. d - k]}{[k + 1 .. d - k]} := Spgen;
        Add(gens, Yi);
    od;

    # Size according to Table 2.3 of [BHR13], except we replace
    # k with 2k because [BHR13] seems to have this wrong.
    return MatrixGroupWithSize(field, gens, SizeSp(twok, q) * SizeSp(d - twok, q));
end);

# Construction as in Lemma 4.4 of [HR10]
BindGlobal("OmegaStabilizerOfNonSingularVector",
function(epsilon, d, q)
    local field, m, one, zero, gamma, F, Q, w, L, HStar, N, H, j, wj,
        matForLinSys, rightSideForLinSys, particularSol, nullspace, basisVector, z,
        alpha, gens, result;
    
    if not epsilon in [-1, 1] then
        ErrorNoReturn("<epsilon> must be 1 or -1");
    elif not IsEvenInt(q) then
        ErrorNoReturn("<q> must be even");
    elif not IsEvenInt(d) then
        ErrorNoReturn("<d> must be even");
    fi;

    field := GF(q);
    m := QuoInt(d, 2);
    one := One(field);
    zero := Zero(field);

    # Q and F are the matrices of the quadratic form and corresponding polar
    # bilinear form we will use in what follows
    if epsilon = 1 then
        F := AntidiagonalMat(d, field);
        Q := AntidiagonalMat(Concatenation(ListWithIdenticalEntries(m, one), 
                                           ListWithIdenticalEntries(m, zero)), 
                             field);
    else
        gamma := FindGamma(q);
        F := AntidiagonalMat(d, field);
        Q := AntidiagonalMat(Concatenation(ListWithIdenticalEntries(m, one),
                                           ListWithIdenticalEntries(m, zero)),
                             field);
        Q[m, m] := one;
        Q[m + 1, m + 1] := gamma;
    fi;

    # This is the vector we will stabilise; we have w * Q * w^T = 1
    w := Concatenation([one], ListWithIdenticalEntries(d - 2, zero), [one]);

    gens := [];
    for L in GeneratorsOfGroup(ConjugateToSesquilinearForm(Sp(d - 2, q),
                                                           "S", 
                                                           AntidiagonalMat(d - 2, field))) do
        HStar := NullMat(d, d, field);
        HStar{[2..d - 1]}{[2..d - 1]} := L;
        N := Q + HStar * Q * TransposedMat(HStar);

        # H will be the element of the subgroup to construct corresponding to
        # the generator L of Sp(d - 2, q)
        H := NullMat(d, d, field);

        # The element L of Sp(d - 2, q) acts canonically on the quotient 
        # <w, v_2, ..., v_{d - 2}> / <w>.
        # To lift this action to the vector space <v_1, ..., v_d>, we construct
        # an image wj for v_j, 2 <= j <= d - 1, with wj in (vj + W) * L and 
        # wj * Q * wj^T = vj * Q * vj^T. 
        for j in [2..d - 1] do
            # It is a straightforward calculation to show that this does the job
            wj := HStar[j] + RootFFE(field, N[j, j], 2) * w;
            H[j] := wj;
        od;

        # Build a matrix with the wj^T in the first d - 2 columns and with w^T
        # in the last column
        matForLinSys := NullMat(d, d - 1, field);
        matForLinSys{[1..d]}{[1..d - 2]} := TransposedMat(H{[2..d - 1]});
        matForLinSys[1][d - 1] := one;
        matForLinSys[d][d - 1] := one;

        rightSideForLinSys := Concatenation(ListWithIdenticalEntries(d - 2, zero), 
                                            [one]);

        # We want a vector z with z * F * wj^T = 0 for all j and z * F * w^T = 1,
        # i.e. we need z * F * matForLinSys = rightSideForLinSys.
        particularSol := SolutionMat(F * matForLinSys, rightSideForLinSys);
        nullspace := NullspaceMat(F * matForLinSys);

        # We need z to not be in <w, v_2, ..., v_{d - 1}>, i.e. z[1] not equal
        # to z[d].
        if particularSol[1] <> particularSol[d] then
            z := particularSol;
        else
            for basisVector in nullspace do
                if basisVector[1] <> basisVector[d] then
                    z := particularSol + basisVector;
                    break;
                fi;
            od;
        fi;

        if not IsBound(z) then
            ErrorNoReturn("This should not have happened");
        fi;


        alpha := SolveQuadraticEquation(field, one, one, z * Q * z);
        # Now we can choose images for v_1, v_d
        H[d] := z + alpha * w;
        H[1] := (z + alpha * w) + w;

        # Adjust the spinor norm of H to be 1 by adding a reflection in w if
        # necessary
        if FancySpinorNorm(F, field, H) = -1 then
            H := H * ReflectionMatrix(d, q, Q, "Q", w);
        fi;

        Add(gens, H);
    od;

    # Size according to Table 2.3 of [BHR13]
    result := MatrixGroupWithSize(field, gens, SizeSp(d - 2, q));
    SetInvariantQuadraticForm(result, rec(matrix := Q));

    if epsilon = 1 then
        return ConjugateToStandardForm(result, "O+");
    else
        return ConjugateToStandardForm(result, "O-");
    fi;
end);
