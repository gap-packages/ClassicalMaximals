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
    Append(generators, [T1, T2]);

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
    local l, field, gens, I, J, GLgen, Xi, SpDim, Spgen, Yi, result;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even");
    fi;

    l := QuoInt(d, 2);
    if k > d / 2 then
        ErrorNoReturn("<k> must be less than or equal to <d> / 2");
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

    SpDim := d - 2 * k;
    if SpDim <> 0 then
        # These two generators are diagonal block matrices with 2x2 blocks
        # that generate a subgroup of Sp(d, q) corresponding to Sp(d - 2 * k, q).
        for Spgen in GeneratorsOfGroup(Sp(SpDim, q)) do
            Yi := IdentityMat(d, field);
            Yi{[k + 1 .. d - k]}{[k + 1 .. d - k]} := Spgen;
            Add(gens, Yi);
        od;
    fi;

    # This generator is mapped to matrices "with 1s down the diagonal,
    # a (k x k) block in the middle that is symmetric about the anti-diagonal,
    # and zeros elsewhere" (cf. [HR05]) by GL(k, q) while also being fixed
    # by Sp(d - 2k, q).
    Add(gens, I + SquareSingleEntryMatrix(field, d, d, 1));

    # This generator is in Sp(d, q) and stabilises the group generated by
    # the first k unit vectors.
    Add(gens, I + SquareSingleEntryMatrix(field, d, d, d - k) - SquareSingleEntryMatrix(field, d, k + 1, 1));

    # Size according to Table 2.3 of [BHR13]
    result := MatrixGroupWithSize(field, gens, q ^ (k * d + QuoInt(k - 3 * k * k, 2)) * SizeGL(k, q) * SizeSp(d - 2 * k, q));
    SetInvariantBilinearForm(result, rec(matrix := AntidiagonalMat(Concatenation(
        ListWithIdenticalEntries(l, One(field)), ListWithIdenticalEntries(l, -One(field))), field)));

    return ConjugateToStandardForm(result, "S");
end);


# Construction as in Proposition 4.4 of [HR05]
BindGlobal("SpStabilizerOfNonDegenerateSubspace",
function(d, q, k)
    local l, field, gens, twok, Spgen, Xi, Yi, result;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even");
    fi;

    l := QuoInt(d, 2);
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
    result :=  MatrixGroupWithSize(field, gens, SizeSp(twok, q) * SizeSp(d - twok, q));
    SetInvariantBilinearForm(result, rec(matrix := AntidiagonalMat(Concatenation(
        ListWithIdenticalEntries(l, One(field)), ListWithIdenticalEntries(l, -One(field))), field)));

    return ConjugateToStandardForm(result, "S");
end);

# Construction as in Lemma 4.2 of [HR10]
BindGlobal("OmegaStabilizerOfIsotropicSubspace",
function(epsilon, d, q, k)
    local m, field, one, gens, linearGens, orthogonalGens, L, H_1or2,
    OmegaGen, t, H_3or4, size, matrices, gamma, xi, eta, result;

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

    if IsEvenInt(q) and IsOddInt(d) then
        ErrorNoReturn("<d> must be even if <q> is even");
    fi;

    m := QuoInt(d, 2);

    if k > m then
        ErrorNoReturn("<k> must be less than or equal to <m>");
    fi;

    if k = m and epsilon = -1 then
        ErrorNoReturn("<k> must not be equal to <m> for <epsilon> = -1");
    fi;

    # the construction referenced above fails for d < 5
    if d < 5 then
        ErrorNoReturn("<d> must be at least 5");
    fi;

    field := GF(q);
    one := One(field);
    gens := [];

    linearGens := StandardGeneratorsOfLinearGroup(k, q);
    
    # We first construct the complement to the p-core of the stabilizer.
    if IsEvenInt(q) then

        for L in [linearGens.L1, linearGens.L2] do
            H_1or2 := IdentityMat(d, field);
            H_1or2{[1..k]}{[1..k]} := L;
            H_1or2{[d - k + 1..d]}{[d - k + 1..d]} := RotateMat(TransposedMat(L ^ -1));
            Add(gens, H_1or2);
        od;

        if k <> m then
            orthogonalGens := StandardGeneratorsOfOrthogonalGroup(epsilon, d - 2 * k, q);
            for OmegaGen in orthogonalGens.generatorsOfOmega do
                H_3or4 := IdentityMat(d, field);
                H_3or4{[k + 1..d - k]}{[k + 1..d - k]} := OmegaGen;
                Add(gens, H_3or4);
            od;
            # Size according to Table 2.3 of [BHR13]
            size := q ^ (k * d - QuoInt(k * (3 * k + 1), 2)) * SizeGL(k, q) * SizeOmega(epsilon, d - 2 * k, q);
        else
            # Size according to Table 2.3 of [BHR13]
            size := q ^ (k * d - QuoInt(k * (3 * k + 1), 2)) * SizeGL(k, q);
        fi;

    else

        if k = m then
            
            for L in [linearGens.L1, linearGens.L2 ^ 2] do
                H_1or2 := IdentityMat(d, field);
                H_1or2{[1..k]}{[1..k]} := L;
                H_1or2{[d - k + 1..d]}{[d - k + 1..d]} := RotateMat(TransposedMat(L ^ -1));
                Add(gens, H_1or2);
            od;

            # Size according to Table 2.3 of [BHR13]
            if IsEvenInt(d) then
                t := -1;
            else
                t := 1;
            fi;
            size := q ^ QuoInt(k * (k + t), 2) * QuoInt(SizeGL(k, q), 2);

        else

            orthogonalGens := StandardGeneratorsOfOrthogonalGroup(epsilon, d - 2 * k, q);
            for matrices in [[linearGens.L1, IdentityMat(d - 2 * k, field)], [linearGens.L2, orthogonalGens.S]] do
                H_1or2 := IdentityMat(d, field);
                H_1or2{[1..k]}{[1..k]} := matrices[1];
                H_1or2{[k + 1..d - k]}{[k + 1..d - k]} := matrices[2];
                H_1or2{[d - k + 1..d]}{[d - k + 1..d]} := RotateMat(TransposedMat(matrices[1] ^ -1));
                Add(gens, H_1or2);
            od;

            for OmegaGen in orthogonalGens.generatorsOfOmega do
                H_3or4 := IdentityMat(d, field);
                H_3or4{[k + 1..d - k]}{[k + 1..d - k]} := OmegaGen;
                Add(gens, H_3or4);
            od;

            # Size according to Table 2.3 of [BHR13]
            size := q ^ (k * d - QuoInt(k * (3 * k + 1), 2)) * SizeGL(k, q) * SizeOmega(epsilon, d - 2 * k, q);

        fi;

    fi;

    # We now construct the p-core of the stabilizer.
    if k = 1 then

        Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[2, 1, one], [d, d - 1, -one]]));

    elif k < QuoInt(d - 1, 2) then

        Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[d - 1, 1, one], [d, 2, -one]]));
        Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[k + 1, 1, one], [d, d - k, -one]]));

    elif IsEvenInt(d) and k = m - 1 then

        Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[d - 1, 1, one], [d, 2, -one]]));
        if epsilon = 1 then
            Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[k + 1, 1, one], [d, d - k, -one]]));
            # [HR10] wants the matrix
            # IdentityMat(d, field) + MatrixByEntries(field, d, d, [[k + 2, 1, one], [d - k - 1, 1, -one]])
            # here, but that just makes no sense. Instead, this works :)
            Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[k + 2, 1, one], [d, d - k - 1, -one]]));
        else
            if IsEvenInt(q) then
                gamma := FindGamma(q);
            else
                xi := PrimitiveElement(GF(q ^ 2));
                gamma := xi ^ (q + 1) * (xi + xi ^ q) ^ -2;
            fi;
            eta := (1 - 4 * gamma) ^ -1;
            Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[k + 1, 1, one], [d, 1, gamma * eta], [d, k + 1, 2 * gamma * eta], [d, k + 2, -eta]]));
        fi;
            
    else

        Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[d - 1, 1, one], [d, 2, -one]]));
        if IsOddInt(d) then
            Add(gens, IdentityMat(d, field) + MatrixByEntries(field, d, d, [[k + 1, 1, one], [d, d - k, -one], [d, 1, -one / 2]]));
        fi;

    fi;

    result := MatrixGroupWithSize(field, gens, size);
    SetInvariantQuadraticFormFromMatrix(result, StandardOrthogonalForm(epsilon, d, q).Q);

    if epsilon = -1 then
        return ConjugateToStandardForm(result, "O-");
    elif epsilon = 0 then
        return ConjugateToStandardForm(result, "O");
    else
        return ConjugateToStandardForm(result, "O+");
    fi;

end);

# Construction as in Lemma 4.3 of [HR10]
BindGlobal("OmegaStabilizerOfNonDegenerateSubspace",
function(epsilon, d, q, epsilon_0, k)
    local m, epsilon_1, epsilon_2, field, gens, one, zeta,
    bilinearFormMat_1, bilinearFormMat_2, nonzeroEntries,
    OmegaGens, R0, R1, orthogonalGens_1, orthogonalGens_2,
    Q, gen_1, gen_2, H, size, H_5, H_6, result;

    # All of the conditions below follow from the general rules of
    # orthogonal groups as well as Table 1 from [HR10], except we
    # use epsilon_0 where the table uses epsilon_1 since Lemma 4.3
    # repurposes that name.
    if not epsilon in [-1, 0, 1] then
        ErrorNoReturn("<epsilon> must be in [-1, 0, 1]");
    elif not epsilon_0 in [-1, 0, 1] then
        ErrorNoReturn("<epsilon_0> must be in [-1, 0, 1]");
    fi;
    if IsEvenInt(q) and IsOddInt(d) then
        ErrorNoReturn("<d> must be even if <q> is even");
    fi;

    m := QuoInt(d, 2);

    if epsilon = 0 then

        if IsEvenInt(d) then
            ErrorNoReturn("<d> must be odd");
        elif not epsilon_0 in [-1, 1] then
            ErrorNoReturn("<epsilon_0> must be -1 or 1");
        elif IsEvenInt(k) then
            ErrorNoReturn("<k> must be odd");
        elif k >= d then
            ErrorNoReturn("<k> must be less than <d>");
        fi;

        epsilon_1 := 0;
        epsilon_2 := epsilon_0;

    elif epsilon = 1 then

        if IsOddInt(d) then
            ErrorNoReturn("<d> must be even");
        fi;
        if IsOddInt(k) then
            if IsEvenInt(q) then
                ErrorNoReturn("<q> must be odd if <k> is odd");
            fi;
        fi;
        if epsilon_0 = 0 then
            if IsEvenInt(k) then
                ErrorNoReturn("<k> must be odd if <epsilon_0> is 0");
            fi;
        elif epsilon_0 in [-1, 1] then
            if IsOddInt(k) then
                ErrorNoReturn("<k> must be even if <epsilon_0> is 1 or -1");
            fi;
        fi;
        if k >= m then
            ErrorNoReturn("<k> must be less than <d> / 2");
        fi;

        epsilon_1 := epsilon_0;
        epsilon_2 := epsilon_0;

    elif epsilon = -1 then

        if IsOddInt(d) then
            ErrorNoReturn("<d> must be even");
        fi;
        if IsOddInt(k) then
            if IsEvenInt(q) then
                ErrorNoReturn("<q> must be odd if <k> is odd");
            fi;
        fi;
        if epsilon_0 = 0 then
            if IsEvenInt(k) then
                ErrorNoReturn("<k> must be odd if <epsilon_0> is 0");
            fi;
            if k = m then
                ErrorNoReturn("<k> must not be equal to <d> / 2 if <epsilon_0> is 0");
            fi;
        elif epsilon_0 in [-1, 1] then
            if IsOddInt(k) then
                ErrorNoReturn("<k> must be even if <epsilon_0> is 1 or -1");
            fi;
        fi;
        if k > m then
            ErrorNoReturn("<k> must be less than or equal to <d> / 2");
        fi;

        epsilon_1 := epsilon_0;
        epsilon_2 := -epsilon_0;

    fi;

    field := GF(q);
    gens := [];

    # In this case, the group preserves both a hyperbolic and
    # an elliptic form. If we lazily construct the form by
    # taking the direct sum of preserved standard forms,
    # we might end up with a form of incorrect type. To avoid
    # this, we need to manually construct a form of correct type
    # and conjugate accordingly. Note that this case only
    # occurs for q odd, so we can safely divide by 2 to get
    # the quadratic form matrix at the end.
    # Unfortunately, we also have to construct the matrices
    # S and G from Theorem 3.9 in [HR10] from scratch, because
    # conjugation does not preserve the spinor norm.
    # Thankfully though the forms we use here are very simple,
    # so finding vectors with square/nonsquare form is not too
    # complicated.
    if epsilon_0 = 0 then

        one := One(field);
        zeta := PrimitiveElement(field);

        bilinearFormMat_1 := IdentityMat(k, field);
        bilinearFormMat_2 := IdentityMat(d - k, field);
        if (epsilon = 1 and (q mod 4 = 3 and d mod 4 = 2)) or (epsilon = -1 and not (q mod 4 = 3 and d mod 4 = 2)) then
            bilinearFormMat_2[1, 1] := zeta;
        fi;

        # The following construction is akin to Theorem 3.9 in [HR10]
        # but with custom vectors for our form(s).
        # The vector v = [0, ..., 0, a, b] guarantees that beta(v, v)
        # is nonsquare for our bilinear form beta, so we can use
        # its reflection matrix to get spinor norm -1.
        # Of course the vector [0, ..., 0, 1] satisfies beta(v, v) square,
        # so its reflection matrix has spinor norm 1.
        nonzeroEntries := SolveQuadraticCongruence(zeta, q);

        if k = 1 then
            orthogonalGens_1 := rec( generatorsOfOmega := [IdentityMat(1, field)], S := IdentityMat(1, field), G := [[-one]] );
        else
            OmegaGens := GeneratorsOfGroup(ConjugateToSesquilinearForm(Omega(0, k, q), "O-B", bilinearFormMat_1));
            R0 := ReflectionMatrix(k, q, bilinearFormMat_1, "B",
                                    one * Concatenation(ListWithIdenticalEntries(k - 1, 0), [1]));
            R1 := ReflectionMatrix(k, q, bilinearFormMat_1, "B",
                                    one * Concatenation(ListWithIdenticalEntries(k - 2, 0), [nonzeroEntries.a, nonzeroEntries.b]));
            orthogonalGens_1 := rec( generatorsOfOmega := OmegaGens, S := R0 * R1, G := R0 );
        fi;

        OmegaGens := GeneratorsOfGroup(ConjugateToSesquilinearForm(Omega(0, d - k, q), "O-B", bilinearFormMat_2));
        R0 := ReflectionMatrix(d - k, q, bilinearFormMat_2, "B",
                                one * Concatenation(ListWithIdenticalEntries(d - k - 1, 0), [1]));
        R1 := ReflectionMatrix(d - k, q, bilinearFormMat_2, "B",
                                one * Concatenation(ListWithIdenticalEntries(d - k - 2, 0), [nonzeroEntries.a, nonzeroEntries.b]));
        orthogonalGens_2 := rec( generatorsOfOmega := OmegaGens, S := R0 * R1, G := R0 );

        Q := IdentityMat(d, field) / 2;
        Q[k + 1, k + 1] := bilinearFormMat_2[1, 1] / 2;

    else

        orthogonalGens_1 := StandardGeneratorsOfOrthogonalGroup(epsilon_1, k, q);
        orthogonalGens_2 := StandardGeneratorsOfOrthogonalGroup(epsilon_2, d - k, q);

        Q := IdentityMat(d, field);
        Q{[1..k]}{[1..k]} := StandardOrthogonalForm(epsilon_1, k, q).Q;
        Q{[k + 1..d]}{[k + 1..d]} := StandardOrthogonalForm(epsilon_2, d - k, q).Q;

    fi;

    for gen_1 in orthogonalGens_1.generatorsOfOmega do
        for gen_2 in orthogonalGens_2.generatorsOfOmega do
            H := IdentityMat(d, field);
            H{[1..k]}{[1..k]} := gen_1;
            H{[k + 1..d]}{[k + 1..d]} := gen_2;
            Add(gens, H);
        od;
    od;

    # Size according to Table 2.3 of [BHR13], in case q even
    # we will divide by 2. Because we use the size of SO instead
    # of Omega and Omega = SO (not |SO| = 2 * |Omega|) in case
    # k = 1, we do not need to divide by 2 for k = 1, but this
    # is still consistent with [HR10].
    size := SizeSO(epsilon_1, k, q) * SizeSO(epsilon_2, d - k, q);

    if IsEvenInt(q) then

        H_5 := IdentityMat(d, field);
        H_5{[1..k]}{[1..k]} := orthogonalGens_1.S;
        H_5{[k + 1..d]}{[k + 1..d]} := orthogonalGens_2.S;
        Add(gens, H_5);

        size := QuoInt(size, 2);
    else

        # The matrices G have spinor norm 1 and determinant -1
        # respectively, so the matrix H_5 has spinor norm 1 and
        # determinant 1 and is therefore in Omega(epsilon, d, q).
        H_5 := IdentityMat(d, field);
        H_5{[1..k]}{[1..k]} := orthogonalGens_1.G;
        H_5{[k + 1..d]}{[k + 1..d]} := orthogonalGens_2.G;
        Add(gens, H_5);

        # Strangely, [HR10] uses the matrices S for Omega(epsilon, k, q)
        # and Omega(epsilon, d - k, q) here, but those are not even
        # always well-defined, so we assume that to be a typo and go
        # with epsilon_1 and epsilon_2 here instead of epsilon.
        if k > 1 then
            H_6 := IdentityMat(d, field);
            H_6{[1..k]}{[1..k]} := orthogonalGens_1.S;
            H_6{[k + 1..d]}{[k + 1..d]} := orthogonalGens_2.S;
            Add(gens, H_6);
        fi;
    fi;

    result := MatrixGroupWithSize(field, gens, size);
    SetInvariantQuadraticFormFromMatrix(result, Q);

    if epsilon = -1 then
        return ConjugateToStandardForm(result, "O-");
    elif epsilon = 0 then
        return ConjugateToStandardForm(result, "O");
    else
        return ConjugateToStandardForm(result, "O+");
    fi;

end);

# Construction as in Lemma 4.4 of [HR10]
BindGlobal("OmegaStabilizerOfNonSingularVector",
function(epsilon, d, q)
    local field, one, zero, standardForm, F, Q, w, L, HStar, N, H, j, wj,
        matForLinSys, rightSideForLinSys, particularSol, nullspace, basisVector, z,
        alpha, gens, result;
    
    if not epsilon in [-1, 1] then
        ErrorNoReturn("<epsilon> must be 1 or -1");
    elif not IsEvenInt(q) then
        ErrorNoReturn("<q> must be even");
    elif not IsEvenInt(d) then
        ErrorNoReturn("<d> must be even");
    elif d <= 2 then
        ErrorNoReturn("<d> must be greater than 2");
    fi;

    field := GF(q);
    one := One(field);
    zero := Zero(field);

    # Q and F are the matrices of the quadratic form and corresponding polar
    # bilinear form we will use in what follows
    standardForm := StandardOrthogonalForm(epsilon, d, q);
    F := standardForm.F;
    Q := standardForm.Q;

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
