InstallGlobalFunction("MatrixByEntries",
function(field, nrRows, nrCols, entries)
    local i, m, o;
    o := One(field);
    if ForAll(entries, x -> IsList(x) and Length(x)=3) then
        m := NullMat(nrRows, nrCols, field);
        for i in entries do
            m[i[1]][i[2]] := i[3]*o;
        od;
    else
        if nrCols*nrRows<>Length(entries) then
            Error("the list <entries> should have length <nrRows> * <nrCols> = ", nrRows*nrCols, "but has length", Length(entries));
        fi;
        m := List([1..nrRows], x -> entries{[1+nrCols*(x-1)..nrCols*x]}*o);
    fi;

    if IsFFECollection(field) then
        m := ImmutableMatrix(field, m);
    fi;
    return m;
end);

InstallGlobalFunction("ChangeFixedSesquilinearForm",
function(group, gramMatrix)
    local gapForm, newForm, gapToCanonical, canonicalToNew, field;
    gapForm := PreservedSesquilinearForms(group)[1];
    field := BaseField(gapForm);
    if IsBilinearForm(gapForm) then
        newForm := BilinearFormByMatrix(gramMatrix, field);
    elif IsHermitianForm(gapForm) then
        newForm := HermitianFormByMatrix(gramMatrix, field);
    fi;
    # the following if condition can only ever be fulfilled if <group> is an
    # orthogonal group; there the case of even dimension is problematic since,
    # in that case, there are two similarity classes of bilinear forms
    if not WittIndex(gapForm) = WittIndex(newForm) then
       ErrorNoReturn("The form preserved by <group> must be similar to the form ", 
                     "described by the Gram matrix <gramMatrix>.");
    fi;
    gapToCanonical := BaseChangeHomomorphism(BaseChangeToCanonical(gapForm), 
                                             field);
    canonicalToNew := BaseChangeHomomorphism(BaseChangeToCanonical(newForm) ^ (-1), 
                                             field);
    return Group(canonicalToNew(gapToCanonical(GeneratorsOfGroup(group))));
end);

InstallGlobalFunction("AntidiagonalMat",
function(entries, field)
    local dimension;
    dimension := Length(entries);
    return MatrixByEntries(field, dimension, dimension, 
                           List([1..dimension], i -> [i, dimension - i + 1, entries[i]]));
end);

# Solving the congruence a ^ 2 + b ^ 2 = c in F_q by trial and error.
#
# A solution always exists by a simple counting argument using the pidgeonhole
# principle and the fact that there are (q + 1) / 2 > q / 2 squares in F_q (for
# q odd; the case q even is trivial). The trial and error approach taken here 
# should in principle almost always terminate quickly: Assuming that - 1 - a ^ 2 
# is evenly distributed in GF(q), the chance to hit a quadratic residue is about 
# 1 / 2 in each trial.
InstallGlobalFunction("SolveQuadraticCongruence",
function(c, q)
    local a, b;
    for a in GF(q) do
        b := RootFFE(GF(q), (c - a ^ 2) * Z(q) ^ 0, 2);
        if not b = fail then
            break;
        fi;
    od;
    return rec(a := a, b := b);
end);

InstallGlobalFunction("ApplyFunctionToEntries",
function(M, func)
    local numberRows, numberColumns, i, j, result;
    if not IsMatrix(M) or Length(M) = 0 then
        ErrorNoReturn("<M> must be a matrix but <M> = ", M);
    fi;

    numberRows := Length(M);
    numberColumns := Length(M[1]);
    result := NullMat(numberRows, numberColumns, DefaultFieldOfMatrix(M));
    for i in [1..numberRows] do
        for j in [1..numberColumns] do
            result[i][j] := func(M[i][j]);
        od;
    od;

    return result;
end);

# If type = "S" then find a beta in GF(q ^ 2) with beta + beta ^ q = alpha.
# If type = "P" then find a beta in GF(q ^ 2) with gamma * gamma ^ q = alpha.
# In both cases, alpha is an element of GF(q).
# Construction as in Lemma 2.2 of [2]
InstallGlobalFunction("SolveFrobeniusEquation",
function(type, alpha, q)
    local R, S, x, delta, polynomial, result;
    if not alpha in GF(q) then
        ErrorNoReturn("<alpha> must be an element of GF(<q>) but <alpha> = ",
                      alpha, " and <q> = ", q);
    fi;
    if not type in ["S", "P"] then
        ErrorNoReturn("<type> must be one of 'S' or 'P' but <type> = ", type);
    fi;
    # We have to make an exception for this case since the construction below
    # does not work here: x ^ 2 + delta is never irreducible over GF(q) since
    # all elements of GF(q) are squares for q even.
    if type = "S" and alpha = 0 and IsEvenInt(q) then
        return Z(q) ^ 0;
    fi;

    R := PolynomialRing(GF(q), ["x"]);
    S := PolynomialRing(GF(q ^ 2), ["x"]);
    x := Indeterminate(GF(q), "x");

    # A quick argument using the quadratic formula for q odd or some
    # algebraic manipulations and the non-surjectivity of the Artin-Schreier
    # map x -> x ^ 2 + x for q odd and alpha <> 0 shows that the construction
    # below always works.
    if type = "S" then
        for delta in GF(q) do
            polynomial := x ^ 2 - alpha * x + delta;
            if IsIrreducibleRingElement(R, polynomial) then
                result := -CoefficientsOfUnivariatePolynomial(Factors(S, polynomial)[1])[1];
                return result;
            fi;
        od;
    # A similar argument to the one used for type "S" works here as well. Note,
    # however, that the argument for q odd via the quadratic formula now
    # additionally needs that the squares in GF(q) do not form an arithmetic
    # progression (which is "closed", i.e. not only a_i+1 = a_i + d, but also
    # a_n + d = a_1), which can be proved in the following way: If they did,
    # then they would be given by -kd, ..., -d, 0, d, 2d, ..., ((q - 1) / 2 - k) * d
    # for some 0 <= k <= (q - 1) / 2; since they form a multiplicative
    # subgroup, we can divide by -d or d, respectively, and see that 
    # -+k, ..., -+1, 0, +-1, +-2, ..., +-((q - 1) / 2 - k) are also all the
    # squares in GF(q). Most notably they all are in GF(p) and thus there are
    # at most p squares in GF(q), which is < (q + 1) / 2 if q >= p ^ 2 - a
    # contradiction. Now we can restrict ourselves to q = p and reach a
    # contradiction for p >= 7 (we leave out the details); this leaves p = 3
    # and p = 5, which can easily be checked manually.
    elif type = "P" then
        for delta in GF(q) do
            polynomial := x ^ 2 + delta * x + alpha;
            if IsIrreducibleRingElement(R, polynomial) then
                result := -CoefficientsOfUnivariatePolynomial(Factors(S, polynomial)[1])[1];
                return result;
            fi;
        od;
    fi;
end);

# An n x n - matrix of zeroes with a 1 in position (row, column)
InstallGlobalFunction("SquareSingleEntryMatrix",
function(field, n, row, column)
    return MatrixByEntries(field, n, n, [[row, column, 1]]);
end);

# Compute Ceil(m / n) for two integers m, n
InstallGlobalFunction("QuoCeil",
function(m, n)
    if m mod n = 0 then
        return QuoInt(m, n);
    else
        return QuoInt(m, n) + 1;
    fi;
end);
