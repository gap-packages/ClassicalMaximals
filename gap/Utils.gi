InstallGlobalFunction("MatrixByEntries",
function(field, nrRows, nrCols, entries)
    local i, m, o;
    o := One(field);
    m := NullMat(nrRows, nrCols, field);
    for i in entries do
        m[i[1],i[2]] := i[3]*o;
    od;
    return ImmutableMatrix(field, m);
end);

# Note that <group> must have the attribute InvariantBilinearForm or
# InvariantSesquilinearForm for this to work.
InstallGlobalFunction("ChangeFixedSesquilinearForm",
function(group, type, gramMatrix)
    local gapForm, newForm, gapToCanonical, canonicalToNew, field;
    if not type in ["S", "O", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O', but <type> = ",
                      type);
    fi;
    field := DefaultFieldOfMatrixGroup(group);
    if type = "S" or type = "O" then
        gapForm := BilinearFormByMatrix(InvariantBilinearForm(group).matrix, 
                                        field);
        newForm := BilinearFormByMatrix(gramMatrix, field);
    else
        gapForm := HermitianFormByMatrix(InvariantSesquilinearForm(group).matrix,
                                         field);
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
    local d, m, i;
    d := Length(entries);
    m := NullMat(d, d, field);
    for i in [1..d] do
        m[i, d - i + 1] := entries[i];
    od;
    return ImmutableMatrix(field, m);
end);

# Solving the congruence a ^ 2 + b ^ 2 = c in F_q by trial and error.
#
# A solution always exists by a simple counting argument using the pigeonhole
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

    numberRows := NrRows(M);
    numberColumns := NrCols(M);
    result := NullMat(numberRows, numberColumns, DefaultFieldOfMatrix(M));
    for i in [1..numberRows] do
        for j in [1..numberColumns] do
            result[i, j] := func(M[i, j]);
        od;
    od;

    return result;
end);

InstallGlobalFunction("HermitianConjugate",
function(M, q)
    return TransposedMat(ApplyFunctionToEntries(M, x -> x ^ q));
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

ReflectionMatrix := function(n, q, gramMatrix, v)
    local reflectionMatrix, i, basisVector, reflectBasisVector, beta;
    reflectionMatrix := NullMat(n, n, GF(q));
    beta := BilinearFormByMatrix(gramMatrix);
    for i in [1..n] do
        basisVector := List([1..n], j -> 0 * Z(q));
        basisVector[i] := Z(q) ^ 0;
        reflectBasisVector := basisVector 
                              - 2 * EvaluateForm(beta, v, basisVector) 
                              / EvaluateForm(beta, v, v) * v;
        reflectionMatrix[i]{[1..n]} := reflectBasisVector;
    od;
    return reflectionMatrix;
end;

# Construct generators for the orthogonal groups with the properties listed in
# Lemma 2.4 of [2].
# Construction as in: C. M. Roney-Dougal. "Conjugacy of Subgroups of the
# General Linear Group." Experimental Mathematics, vol. 13 no. 2, 2004, pp.
# 151-163. Lemma 2.4.
# We take the notation from [2].
InstallGlobalFunction("GeneratorsOfOrthogonalGroup",
function(epsilon, n, q)
    local gramMatrix, generatorsOfSO, vectorOfSquareNorm, D, E, zeta, a, b,
    solutionOfQuadraticCongruence;
    if IsEvenInt(q) then
        ErrorNoReturn("This function was only designed for <q> odd but <n> = ", 
                      n, "and <q> = ", q);
    fi;

    zeta := PrimitiveElement(GF(q));
    if IsOddInt(n) then
            gramMatrix := IdentityMat(n, GF(q));
            generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                            "O",
                                                                            gramMatrix));
            D := - IdentityMat(n, GF(q));
            E := zeta * IdentityMat(n, GF(q));
    else 
        if epsilon = 1 then
            gramMatrix := AntidiagonalMat(List([1..n], i -> 1), GF(q));
            generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                            "O",
                                                                            gramMatrix));
            # Our standard bilinear form is given by the Gram matrix 
            # Antidiag(1, ..., 1). The norm of [1, 0, ..., 0, 2] under this
            # bilinear form is 4, i.e. a square. (Recall q odd, so this is not zero!)
            vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                           List([1..n - 2], i -> 0), 
                                                           [2]);
            D := ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
            E := DiagonalMat(Concatenation(List([1..n / 2], i -> zeta), 
                                           List([1..n / 2], i -> zeta ^ 0)));
        elif epsilon = -1 then

            # Get a, b in GF(q) with a ^ 2 + b ^ 2 = zeta
            solutionOfQuadraticCongruence := SolveQuadraticCongruence(zeta, q);
            a := solutionOfQuadraticCongruence.a;
            b := solutionOfQuadraticCongruence.b;

            if IsOddInt(n * (q - 1) / 4) then
                gramMatrix := IdentityMat(n, GF(q));
                generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                                "O",
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(1, ..., 1). The norm of [1, 0, ..., 0] under this bilinear
                # form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                               List([1..n - 1], i -> 0));
                D := ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
                # Block diagonal matrix consisting of n / 2 blocks of the form 
                # [[a, b], [b, -a]].
                E := MatrixByEntries(GF(q), n, n, 
                                     Concatenation(List([1..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([1..n], i -> [i, i + (-1) ^ (i + 1), b])));
            else
                gramMatrix := Z(q) ^ 0 * DiagonalMat(Concatenation([zeta],
                                                                   List([1..n - 1], i -> 1)));
                generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                                "O",
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(zeta, 1, ..., 1). The norm of [0, ..., 0, 1] under this
                # bilinear form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation(List([1..n - 1], i -> 0), 
                                                               [1]);
                D := ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
                # Block diagonal matrix consisting of one block [[0, zeta], [1, 0]]
                # and n / 2 - 1 blocks of the form [[a, b], [b, -a]].
                E := MatrixByEntries(GF(q), n, n, 
                                     Concatenation([[1, 2, zeta], [2, 1, zeta ^ 0]],
                                                   List([3..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([3..n], i -> [i, i + (-1) ^ (i + 1), b])));
            fi;
        fi;
    fi;
    
    return rec(generatorsOfSO := generatorsOfSO, D := D, E := E);
end);

