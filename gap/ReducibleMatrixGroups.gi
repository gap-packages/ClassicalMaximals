# Return the subgroup of <M>SL(n, q)</M> stabilizing the
# <A>k</A>-dimensional subspace of <M>F^n</M>, where <C>F := GF(q)</C>,
# consisting of all vectors whose first <C>n-k</C> entries are zero.
# Construction as in Proposition 4.1 of [2]
BindGlobal("SLStabilizerOfSubspace",
function(n, q, k)
    local A5, dirProd, z, T, result;
    z := PrimitiveElement(GF(q));
    A5 := DiagonalMat(
        Concatenation([z], List([2..n - 1], i -> z ^ 0), [z ^ -1])
    );
    dirProd := MatDirectProduct(SL(n - k, q), SL(k, q));
    T := IdentityMat(n, GF(q)) + SquareSingleEntryMatrix(GF(q), n, 1, n - k + 1);
    result := Group(Concatenation([A5], GeneratorsOfGroup(dirProd), [T]));
    # Size according to Table 2.3 of [1]
    SetSize(result,
            q ^ (k * (n - k)) * Size(SL(k, q)) * Size(SL(n - k, q)) * (q-1));
    return result;
end);

# Construction as in Proposition 4.5 of [2]
BindGlobal("SUStabilizerOfIsotropicSubspace",
function(d, q, k)
    local zeta, generatorsOfSL, generatorOfSL, generatorsOfSU, generatorOfSU, J,
    automorphism, generators, generator, T1, T2, nu, mu, D, result;

    if not k <= d / 2 then
        ErrorNoReturn("<k> must not be larger than <d> / 2 but <k> = ", k, 
                      " and <d> = ", d);
    fi;

    zeta := PrimitiveElement(GF(q ^ 2));
    generators := [];
    automorphism := x -> x ^ q;
    J := AntidiagonalMat(List([1..k], i -> 1), GF(q ^ 2));

    # The following elements generate SL(k, q ^ 2) x SU(d - 2 * k, q).
    # Note that we actually do need SL(k, q ^ 2) here and not GL(k, q ^ 2) as
    # claimed in the proof of Proposition 4.5 in [2] since some of the
    # generators constructed below would not have determinant 1 otherwise.
    generatorsOfSL := GeneratorsOfGroup(SL(k, q ^ 2));
    if d - 2 * k > 0 then
        generatorsOfSU := GeneratorsOfGroup(SU(d - 2 * k, q));
        for generatorOfSL in generatorsOfSL do
            for generatorOfSU in generatorsOfSU do
                generator := NullMat(d, d, GF(q ^ 2));
                generator{[1..k]}{[1..k]} := generatorOfSL;
                generator{[d - k + 1..d]}{[d - k + 1..d]} := J * ApplyFunctionToEntries(TransposedMat(generatorOfSL) ^ (-1),
                                                                                        automorphism) 
                                                               * J;
                generator{[k + 1..d - k]}{[k + 1..d - k]} := generatorOfSU;
                Add(generators, generator);
            od;
        od;
    else
        for generatorOfSL in generatorsOfSL do
            generator := NullMat(d, d, GF(q ^ 2));
            generator{[1..k]}{[1..k]} := generatorOfSL;
            generator{[d - k + 1..d]}{[d - k + 1..d]} := J * ApplyFunctionToEntries(TransposedMat(generatorOfSL) ^ (-1),
                                                                                    automorphism) 
                                                            * J;
            Add(generators, generator);
        od;
    fi;

    # the following two transvections generate a group of order q ^ (k * (2 * d - 3 * k))
    if IsOddInt(q) then
        nu := zeta ^ QuoInt(q + 1, 2);
    else
        nu := zeta ^ 0;
    fi;
    T1 := IdentityMat(d, GF(q ^ 2)) + nu * SquareSingleEntryMatrix(GF(q ^ 2), d, d, 1);
    if d - 2 * k > 1 then
        # Note that in the proof of Proposition 4.5 in [2], there is a + sign
        # instead of the - sign below, but this is wrong and will lead to T2
        # not being in SU(d, q).
        T2 := IdentityMat(d, GF(q ^ 2)) + SquareSingleEntryMatrix(GF(q ^ 2), d, d, d - k)   
                                        - SquareSingleEntryMatrix(GF(q ^ 2), d, k + 1, 1);
    elif d - 2 * k = 1 then
        if IsEvenInt(q) then
            T2 := IdentityMat(d, GF(q ^ 2)) + zeta * SquareSingleEntryMatrix(GF(q ^ 2), d, d, 1)
                                            + SquareSingleEntryMatrix(GF(q ^ 2), d, d, QuoCeil(d, 2))
                                            + SquareSingleEntryMatrix(GF(q ^ 2), d, QuoCeil(d, 2), 1);
        else
            mu := SolveFrobeniusEquation("P", -2 * zeta ^ 0, q);
            # Again, note that in the proof of Proposition 4.5 in [2], there is
            # a + sign instead of the - sign below, but this is wrong and will
            # lead to T2 not being in SU(d, q).
            T2 := IdentityMat(d, GF(q ^ 2)) + SquareSingleEntryMatrix(GF(q ^ 2), d, d, 1)
                                            - mu * SquareSingleEntryMatrix(GF(q ^ 2), d, d, QuoCeil(d, 2))
                                            + mu ^ q * SquareSingleEntryMatrix(GF(q ^ 2), d, QuoCeil(d, 2), 1);
        fi;
    else
        # if d = 2 * k we do not need a second transvection
        T2 := IdentityMat(d, GF(q ^ 2));
    fi;
    generators := Concatenation(generators, [T1, T2]);

    # finally a diagonal matrix of order q ^ 2 - 1 (or q - 1 if d = 2 * k)
    D := IdentityMat(d, GF(q ^ 2));
    if d - 2 * k > 1 then
        D[1][1] := zeta;
        D[k + 1][k + 1] := zeta ^ (-1);
        D[d - k][d - k] := zeta ^ q;
        D[d][d] := zeta ^ (-q);
        Add(generators, D);
    elif d - 2 * k = 1 then
        D[1][1] := zeta;
        D[k + 1][k + 1] := zeta ^ (q - 1);
        D[d][d] := zeta ^ (-q);
        Add(generators, D);
    else
        D := IdentityMat(d, GF(q ^ 2));
        D[1][1] := zeta ^ (q + 1);
        D[d][d] := zeta ^ (-q - 1);
        Add(generators, D);
    fi;

    result := Group(generators);
    # Size according to Table 2.3 of [1]
    if d - 2 * k > 0 then
        SetSize(result, q ^ (k * (2 * d - 3 * k)) * Size(SL(k, q ^ 2)) 
                                                  * Size(SU(d - 2 * k, q)) 
                                                  * (q ^ 2 - 1));
    else
        SetSize(result, q ^ (k * (2 * d - 3 * k)) * Size(SL(k, q ^ 2))
                                                  * (q - 1));
    fi;

    return result;
end);
