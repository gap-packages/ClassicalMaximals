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

InstallGlobalFunction("AntidiagonalMat",
function(entries, field)
    local d, m, i;
    if IsInt(entries) then
        d := entries;
        entries := ListWithIdenticalEntries(d, One(field));
    else
        d := Length(entries);
    fi;
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
    local F, a, b;
    F := GF(q);
    for a in F do
        b := RootFFE(F, (c - a ^ 2) * Z(q) ^ 0, 2);
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
# Construction as in Lemma 2.2 of [HR05]
InstallGlobalFunction("SolveFrobeniusEquation",
function(type, alpha, q)
    local F, R, S, x, delta, polynomial, result;

    F := GF(q);
    if not alpha in F then
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

    R := PolynomialRing(F, ["x"]);
    S := PolynomialRing(GF(q ^ 2), ["x"]);
    x := Indeterminate(F, "x");

    # A quick argument using the quadratic formula for q odd or some
    # algebraic manipulations and the non-surjectivity of the Artin-Schreier
    # map x -> x ^ 2 + x for q odd and alpha <> 0 shows that the construction
    # below always works.
    if type = "S" then
        for delta in F do
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
        for delta in F do
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


# Compute the size of Sp(n, q) according to Theorem 1.6.22 in [BHR13]
InstallGlobalFunction("SizeSp",
function(n, q)
    local m, result, powerOfq, i;
    if IsOddInt(n) then
        ErrorNoReturn("Dimension <n> must be even but ", n, " was given.");
    fi;
    m := QuoInt(n, 2);
    result := q ^ (m * m);
    powerOfq := 1;
    for i in [1..m] do
        powerOfq := powerOfq * q * q;
        result := result * (powerOfq - 1);
    od;
    return result;
end);


# Compute the size of PSp(n, q) according to Table 1.3 in [BHR13],
InstallGlobalFunction("SizePSp",
function(n, q)
    return QuoInt(SizeSp(n, q), Gcd(2, q - 1));
end);


# Compute the size of SU(n, q) according to Theorem 1.6.22 in [BHR13]
# using the formula for GU(n, q) but starting with i = 2
# because Table 1.3 gives [GU(n, q):SU(n, q)] = q + 1.
InstallGlobalFunction("SizeSU",
function(n, q)
    local result, powerOfq, sign, i;
    result := q ^ QuoInt(n * (n - 1), 2);
    powerOfq := q;
    sign := 1;
    for i in [2..n] do
        powerOfq := powerOfq * q;
        sign := -sign;
        result := result * (powerOfq + sign);
    od;
    return result;
end);

# Compute the size of PSU(n, q) according to Table 1.3 in [BHR13]
# Namely, we have | G / Z(G) : S / Z(S) | = | G : S | * |Z(S)| / |Z(G)| so due
# to | G : S | = q + 1, |Z(G)| = q + 1 and | G / Z(G) : S / Z(S) | = (q + 1, n), 
# which are given in said table, this gives |Z(S)| = (q + 1, n). 
InstallGlobalFunction("SizePSU",
function(n, q)
    return SizeSU(n, q) / Gcd(n, q + 1);
end);

# Compute the size of GU(n, q) according to Table 1.3 in [BHR13]
InstallGlobalFunction("SizeGU",
function(n, q)
    return (q + 1) * SizeSU(n, q);
end);


# Compute the size of GO(epsilon, n, q) according to Theorem 1.6.22 in [BHR13]
InstallGlobalFunction("SizeGO",
function(epsilon, n, q)
    local m, result, powerOfq, i;
    if epsilon = 0 then

        if IsEvenInt(n) then
            ErrorNoReturn("for <epsilon> = ", epsilon, " the dimension <n> must be odd but ", n, " was given.");
        fi;

        if IsEvenInt(q) then
            return SizeSp(n - 1, q);
        fi;

        m := QuoInt(n - 1, 2);
        result := 2 * q ^ (m * m);

    elif epsilon in [-1, 1] then

        if IsOddInt(n) then
            ErrorNoReturn("for <epsilon> = ", epsilon, " the dimension <n> must be even but ", n, " was given.");
        fi;

        m := QuoInt(n, 2);
        result := 2 * q ^ (m * (m - 1)) * (q ^ m - epsilon);
        m := m - 1;
    else
        ErrorNoReturn("<epsilon> must be in [-1, 0, 1] but ", epsilon, " was given.");
    fi;

    powerOfq := 1;
    for i in [1..m] do
        powerOfq := powerOfq * q * q;
        result := result * (powerOfq - 1);
    od;

    return result;
end);


# Compute the size of SO(epsilon, n, q) according to Table 1.3 in [BHR13]
InstallGlobalFunction("SizeSO",
function(epsilon, n, q)
    return QuoInt(SizeGO(epsilon, n, q), Gcd(2, q - 1));
end);


ReflectionMatrix := function(n, q, gramMatrix, v)
    local F, reflectionMatrix, i, basisVector, reflectBasisVector, beta;
    F := GF(q);
    reflectionMatrix := NullMat(n, n, F);
    beta := BilinearFormByMatrix(gramMatrix);
    if IsZero(EvaluateForm(beta, v, v)) then
        ErrorNoReturn("The vector <v> must have non-zero norm with respect to",
                      " the bilinear form given by <gramMatrix>");
    fi;
    for i in [1..n] do
        basisVector := List([1..n], j -> Zero(F));
        basisVector[i] := Z(q) ^ 0;
        reflectBasisVector := basisVector 
                              - 2 * EvaluateForm(beta, v, basisVector) 
                              / EvaluateForm(beta, v, v) * v;
        reflectionMatrix[i]{[1..n]} := reflectBasisVector;
    od;
    return reflectionMatrix;
end;

# Construct generators for the orthogonal groups with the properties listed in
# Lemma 2.4 of [HR05].
# Construction as in: C. M. Roney-Dougal. "Conjugacy of Subgroups of the
# General Linear Group." Experimental Mathematics, vol. 13 no. 2, 2004, pp.
# 151-163. Lemma 2.4.
# We take the notation from [HR05].
InstallGlobalFunction("GeneratorsOfOrthogonalGroup",
function(epsilon, n, q)
    local F, gramMatrix, generatorsOfSO, vectorOfSquareNorm, D, E, zeta, a, b,
    solutionOfQuadraticCongruence;
    if IsEvenInt(q) then
        ErrorNoReturn("This function was only designed for <q> odd but <n> = ", 
                      n, "and <q> = ", q);
    fi;

    F := GF(q);
    zeta := PrimitiveElement(F);
    if IsOddInt(n) then
            gramMatrix := IdentityMat(n, F);
            generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                            "O",
                                                                            gramMatrix));
            D := - IdentityMat(n, F);
            E := zeta * IdentityMat(n, F);
    else 
        if epsilon = 1 then
            gramMatrix := AntidiagonalMat(n, F);
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
                gramMatrix := IdentityMat(n, F);
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
                E := MatrixByEntries(F, n, n, 
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
                E := MatrixByEntries(F, n, n, 
                                     Concatenation([[1, 2, zeta], [2, 1, zeta ^ 0]],
                                                   List([3..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([3..n], i -> [i, i + (-1) ^ (i + 1), b])));
            fi;
        fi;
    fi;
    
    return rec(generatorsOfSO := generatorsOfSO, D := D, E := E);
end);

InstallGlobalFunction("MatrixGroup",
function(F, gens)
    return Group(List(gens, g -> ImmutableMatrix(F, g)));
end);

InstallGlobalFunction("MatrixGroupWithSize",
function(F, gens, size)
    local result;
    result := MatrixGroup(gens, F);
    SetSize(result, size);
    return result;
end);
