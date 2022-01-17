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
    return m;
end);

# Solving the congruence a ^ 2 + b ^ 2 = c in F_q by trial and error.
#
# A solution always exists by a simple counting argument using the pigeonhole
# principle and the fact that there are (q + 1) / 2 > q / 2 squares in F_q (for
# q odd; the case q even is trivial). The trial and error approach taken here 
# should in principle almost always terminate quickly: Assuming that - 1 - a ^ 2 
# is evenly distributed in GF(q), the chance to hit a quadratic residue is about 
# 1 / 2 in each trial.
BindGlobal("SolveQuadraticCongruence",
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

# Return a matrix N with the property that N[i, j] = func(M[i, j]).
BindGlobal("ApplyFunctionToEntries",
function(M, func)
    local numberRows, numberColumns, i, j, result;
    if not IsMatrix(M) or Length(M) = 0 then
        ErrorNoReturn("<M> must be a matrix");
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

# Take an m x n-matrix M and change its shape to a rows x cols-matrix, where
# entries are copied column by column. 
BindGlobal("ReshapeMatrix",
function(M, rows, cols)
    local m, n, result, currentRow, currentCol, i, j;

    m := NrRows(M);
    n := NrCols(M);

    if rows * cols <> m * n then
        ErrorNoReturn("<rows> * <cols> must be the same as the number",
                      "of entries of <M>");
    fi;

    result := NullMat(rows, cols, DefaultFieldOfMatrix(M));
    currentRow := 1;
    currentCol := 1;
    for i in [1..m] do
        for j in [1..n] do
            result[currentRow, currentCol] := M[i, j];
            currentCol := currentCol + 1;
            if currentCol > cols then
                currentCol := 1;
                currentRow := currentRow + 1;
            fi;
        od;
    od;

    return result;
end);

# Return a matrix N obtained from M by first raising each entry to the q-th
# power and then transposing the result.
BindGlobal("HermitianConjugate",
function(M, q)
    return TransposedMat(ApplyFunctionToEntries(M, x -> x ^ q));
end);

# If type = "S" then find a beta in GF(q ^ 2) with beta + beta ^ q = alpha.
# If type = "P" then find a beta in GF(q ^ 2) with gamma * gamma ^ q = alpha.
# In both cases, alpha is an element of GF(q).
# Construction as in Lemma 2.2 of [HR05]
BindGlobal("SolveFrobeniusEquation",
function(type, alpha, q)
    local F, R, S, x, delta, polynomial, result;

    F := GF(q);
    if not alpha in F then
        ErrorNoReturn("<alpha> must be an element of GF(<q>)");
    fi;
    if not type in ["S", "P"] then
        ErrorNoReturn("<type> must be one of 'S' or 'P'");
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

# Find gamma in GF(q) such that x ^ 2 + x + gamma is irreducible for q a power
# of two.
BindGlobal("FindGamma",
function(q)
    local F, B, M, i;

    if not IsEvenInt(q) then
        ErrorNoReturn("<q> must be even");
    elif not IsPrimePowerInt(q) then
        ErrorNoReturn("<q> must be a power of 2");
    fi;

    F := GF(q);
    
    # It suffices to find gamma not in the image of x ^ 2 + x. Notice that this
    # is a linear transformation of the GF(2)-vector space GF(q).
    B := CanonicalBasis(F);
    M := List(B, b -> Coefficients(B, b + b ^ 2));
    ConvertToMatrixRep(M);
    M := RREF(M);
    i := First([1..Length(M)], i -> IsZero(M[i, i]));

    return B[i];
end);

# Return a root of a * x ^ 2 + b * x + c = 0 over a finite field GF(q) of
# characteristic 2.
BindGlobal("SolveQuadraticEquation",
function(F, a, b, c)
    local d, V, B, M, t;

    if not Characteristic(F) = 2 then
        ErrorNoReturn("<F> must be a field of characteristic 2");
    elif IsZero(a) then
        ErrorNoReturn("<a> must be non-zero");
    fi;

    if IsZero(b) then
        return RootFFE(F, -c / a, 2);
    fi;

    # We have (a / b ^ 2) * (a * x ^ 2 + b * x + c) 
    #       = (a / b * x) ^ 2 + (a / b * x) + (c * a / b ^ 2) 
    # Hence we find a solution of t ^ 2 + t + c * a / b ^ 2 = 0.
    d := c * a / b ^ 2; 

    # Note that the map t --> t ^ 2 + t is linear so we can express it via a
    # representation matrix and find a pre-image of -d (if one exists) by
    # solving a linear system 
    B := CanonicalBasis(F);
    M := List(B, b -> Coefficients(B, b + b ^ 2));

    # Solve v * M = Coefficients(B, d) and express v as an element of F again
    t := LinearCombination(B, SolutionMat(M, Coefficients(B, d)));

    return b / a * t;
end);

# Compute the Trace of an element x in GF(q ^ s) over GF(q). Since the Galois
# group of GF(q ^ s) over GF(q) is cyclic with generator x -> x ^ q, this is
# just x + x ^ q + x ^ (q  ^ 2) + ... + x ^ (q  ^ (s - 1))
BindGlobal("TraceOverFiniteField",
function(x, q, s)
    return Sum(List([0..s - 1], i -> x ^ (q ^ i)));
end);

# An n x n - matrix of zeroes over <field> with a 1 in position (<row>, <column>)
BindGlobal("SquareSingleEntryMatrix",
function(field, n, row, column)
    return MatrixByEntries(field, n, n, [[row, column, 1]]);
end);

# Compute Ceil(m / n) for two integers m, n
BindGlobal("QuoCeil",
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
        ErrorNoReturn("Dimension <n> must be even");
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
            ErrorNoReturn("for <epsilon> = ", epsilon, " the dimension <n> must be odd");
        fi;

        if IsEvenInt(q) then
            return SizeSp(n - 1, q);
        fi;

        m := QuoInt(n - 1, 2);
        result := 2 * q ^ (m * m);

    elif epsilon in [-1, 1] then

        if IsOddInt(n) then
            ErrorNoReturn("for <epsilon> = ", epsilon, " the dimension <n> must be even");
        fi;

        m := QuoInt(n, 2);
        result := 2 * q ^ (m * (m - 1)) * (q ^ m - epsilon);
        m := m - 1;
    else
        ErrorNoReturn("<epsilon> must be in [-1, 0, 1]");
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

# Return the matrix corresponding to the reflection in the vector <v> of the 
# space GF(q) ^ n equipped with the bilinear or quadratic form given by the 
# argument <gramMatrix>, depending on whether type = "B" or type = "Q".
# Note that, if q is even, we require type = "Q".
BindGlobal("ReflectionMatrix",
function(n, q, gramMatrix, type, v)
    local F, reflectionMatrix, i, basisVector, reflectBasisVector, beta, Q,
    halfOfbeta;
    F := GF(q);
    reflectionMatrix := NullMat(n, n, F);

    if type = "B" and IsEvenInt(q) then
        ErrorNoReturn("If <q> is even, <type> must be 'Q'");
    fi;

    if type = "B" then
        beta := BilinearFormByMatrix(gramMatrix);
        # We have to divide by 2 here as the function
        # QuadraticFormByBilinearForm returns a quadratic form with 
        # Q(v) = halfOfbeta(v, v) = 1 / 2 * beta(v, v)
        halfOfbeta := BilinearFormByMatrix(1 / 2 * gramMatrix);
        Q := QuadraticFormByBilinearForm(halfOfbeta);
    elif type = "Q" then
        Q := QuadraticFormByMatrix(gramMatrix);
        beta := AssociatedBilinearForm(Q);
    else
        ErrorNoReturn("<type> must be 'B' or 'Q'");
    fi;

    if IsZero(EvaluateForm(Q, v)) then
        ErrorNoReturn("The vector <v> must have non-zero norm with respect to",
                      " the form given by <gramMatrix>");
    fi;

    for i in [1..n] do
        basisVector := ListWithIdenticalEntries(n, Zero(F));
        basisVector[i] := One(F);
        reflectBasisVector := basisVector 
                              - EvaluateForm(beta, v, basisVector) 
                              / EvaluateForm(Q, v) * v;
        reflectionMatrix[i] := reflectBasisVector;
    od;

    return reflectionMatrix;
end);

# Construct generators for the orthogonal groups with the properties listed in
# Lemma 2.4 of [HR05].
# Construction as in: C. M. Roney-Dougal. "Conjugacy of Subgroups of the
# General Linear Group." Experimental Mathematics, vol. 13 no. 2, 2004, pp.
# 151-163. Lemma 2.4.
# We take the notation from [HR05].
BindGlobal("GeneratorsOfOrthogonalGroup",
function(epsilon, n, q)
    local F, gramMatrix, generatorsOfSO, vectorOfSquareNorm, D, E, zeta, a, b,
    solutionOfQuadraticCongruence;
    if IsEvenInt(q) then
        ErrorNoReturn("This function was only designed for <q> odd");
    fi;

    F := GF(q);
    zeta := PrimitiveElement(F);
    if IsOddInt(n) then
            gramMatrix := IdentityMat(n, F);
            generatorsOfSO := GeneratorsOfGroup(ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                            "O-B",
                                                                            gramMatrix));
            D := - IdentityMat(n, F);
            E := zeta * IdentityMat(n, F);
    else 
        if epsilon = 1 then
            gramMatrix := AntidiagonalMat(n, F);
            generatorsOfSO := GeneratorsOfGroup(ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                            "O-B",
                                                                            gramMatrix));
            # Our standard bilinear form is given by the Gram matrix 
            # Antidiag(1, ..., 1). The norm of [1, 0, ..., 0, 2] under this
            # bilinear form is 4, i.e. a square. (Recall q odd, so this is not zero!)
            vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                           List([1..n - 2], i -> 0), 
                                                           [2]);
            D := ReflectionMatrix(n, q, gramMatrix, "B", vectorOfSquareNorm);
            E := DiagonalMat(Concatenation(List([1..n / 2], i -> zeta), 
                                           List([1..n / 2], i -> zeta ^ 0)));
        elif epsilon = -1 then

            # Get a, b in GF(q) with a ^ 2 + b ^ 2 = zeta
            solutionOfQuadraticCongruence := SolveQuadraticCongruence(zeta, q);
            a := solutionOfQuadraticCongruence.a;
            b := solutionOfQuadraticCongruence.b;

            if IsOddInt(n * (q - 1) / 4) then
                gramMatrix := IdentityMat(n, F);
                generatorsOfSO := GeneratorsOfGroup(ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                                "O-B",
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(1, ..., 1). The norm of [1, 0, ..., 0] under this bilinear
                # form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                               List([1..n - 1], i -> 0));
                D := ReflectionMatrix(n, q, gramMatrix, "B", vectorOfSquareNorm);
                # Block diagonal matrix consisting of n / 2 blocks of the form 
                # [[a, b], [b, -a]].
                E := MatrixByEntries(F, n, n, 
                                     Concatenation(List([1..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([1..n], i -> [i, i + (-1) ^ (i + 1), b])));
            else
                gramMatrix := Z(q) ^ 0 * DiagonalMat(Concatenation([zeta],
                                                                   List([1..n - 1], i -> 1)));
                generatorsOfSO := GeneratorsOfGroup(ConjugateToSesquilinearForm(SO(epsilon, n, q),
                                                                                "O-B",
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(zeta, 1, ..., 1). The norm of [0, ..., 0, 1] under this
                # bilinear form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation(List([1..n - 1], i -> 0), 
                                                               [1]);
                D := ReflectionMatrix(n, q, gramMatrix, "B", vectorOfSquareNorm);
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

# Construct standard generators generatorsOfOmega, S, G, D for the orthogonal 
# groups as used in [HR10], with the following properties:
#   * generatorsOfOmega generate Omega(epsilon, d, q)
#   * generatorsOfOmega and S generate SO(epsilon, d, q)
#   * generatorsOfOmega, S and G generate GO(epsilon, d, q)
#   * the spinor norm of G is 1 
#   * D generates CO(epsilon, d, q) mod GO(epsilon, d, q)
# Construction as in Theorem 3.9 loc. cit.
BindGlobal("StandardGeneratorsOfOrthogonalGroup",
function(epsilon, d, q)
    local field, one, zeta, standardForm, Q, m, conjugatedOmega, 
    generatorsOfOmega, e, p, R0, R1, S, G, D, xi;
    
    if not epsilon in [-1, 0, 1] then
        ErrorNoReturn("<epsilon> must be one of -1, 0, 1");
    fi;
    if epsilon = 0 and IsEvenInt(d) then
        ErrorNoReturn("<epsilon> must be one of -1 or 1 if <d> is even");
    fi;
    if epsilon <> 0 and IsOddInt(d) then
        ErrorNoReturn("<epsilon> must be 0 if <d> is odd");
    fi;
    if IsEvenInt(q) and IsOddInt(d) then
        ErrorNoReturn("<d> must be even if <q> is even");
    fi;

    field := GF(q);
    one := One(field);
    zeta := PrimitiveElement(field);

    # In this case, 1 = Omega = SO, GO = Z_2 and CO = Z_(q - 1)
    # up to isomorphisms.
    if d = 1 then
        return rec( generatorsOfOmega := [IdentityMat(1, field)], S := IdentityMat(1, field), G := [[-one]], D := [[zeta]] );
    fi;

    standardForm := StandardOrthogonalForm(epsilon, d, q);
    Q := standardForm.Q;
    m := QuoInt(d, 2);

    conjugatedOmega := ConjugateToSesquilinearForm(Omega(epsilon, d, q), "O-Q", Q);
    generatorsOfOmega := ShallowCopy(GeneratorsOfGroup(conjugatedOmega));
    if Length(generatorsOfOmega) = 1 then
        # this is in particular the case if d = 2
        Add(generatorsOfOmega, IdentityMat(d, GF(q)));
    fi;

    if IsOddInt(q) then
        if d = 2 and epsilon = -1 then
            e := DegreeOverPrimeField(field);
            p := Root(q, e);
            if IsEvenInt(e) or p mod 8 = 1 or p mod 8 = 7 then
                # by quadratic reciprocity, this is the case where 2 is a
                # square in GF(q)
                R0 := ReflectionMatrix(2, q, Q, "Q", one * [1, 0]);
                R1 := ReflectionMatrix(2, q, Q, "Q", one * [0, 1]);
            else
                R0 := ReflectionMatrix(2, q, Q, "Q", one * [0, 1]);
                R1 := ReflectionMatrix(2, q, Q, "Q", one * [1, 0]);
            fi;
        else
            R0 := ReflectionMatrix(d, q, Q, "Q", 
                                   one * Concatenation([1], 
                                                       ListWithIdenticalEntries(d - 2, 0), 
                                                       [1 / 2]));
            R1 := ReflectionMatrix(d, q, Q, "Q",
                                   one * Concatenation([1], 
                                                       ListWithIdenticalEntries(d - 2, 0),
                                                       [zeta / 2]));
        fi;

        S := R0 * R1;
        G := R0;

    else
        # q even
        if d = 2 and epsilon = -1 then
            S := ReflectionMatrix(2, q, Q, "Q", one * [1, 0]);
        else
            S := ReflectionMatrix(d, q, Q, "Q", 
                                  one * Concatenation([1],
                                                      ListWithIdenticalEntries(d - 2, 0),
                                                      [1]));
        fi;

        # SO(epsilon, d, q) = GO(epsilon, d, q) since q is even
        G := IdentityMat(d, GF(q));

        # as given in Table 2 of [MR11]
        D := zeta ^ (q / 2) * IdentityMat(d, field);
    fi;

    if epsilon = 0 then
        D := DiagonalMat(Concatenation(ListWithIdenticalEntries(m, zeta ^ 2),
                                       [zeta],
                                       ListWithIdenticalEntries(m, one)));
    elif epsilon = 1 then
        D := DiagonalMat(Concatenation(ListWithIdenticalEntries(m, zeta),
                                       ListWithIdenticalEntries(m, one)));
    elif IsOddInt(q) then
        xi := PrimitiveElement(GF(q ^ 2));
        D := DiagonalMat(Concatenation(ListWithIdenticalEntries(m - 1, zeta),
                                       one * [0, 0],
                                       ListWithIdenticalEntries(m - 1, one)));
        D[m, m + 1] := xi + xi ^ q;
        D[m + 1, m] := zeta * (xi + xi ^ q) ^ (-1);
    fi;

    return rec(generatorsOfOmega := generatorsOfOmega, S := S, G := G, D := D);
end);

# Construct standard generators L1, L2, L3 as used in [HR10]
# with the following properties:
#   * L1 and L2 generate GL(d, q)
#   * L1 and L3 generate SL(d, q)
#   * all matrix entries lie in {0, \pm 1, \pm zeta^{\pm 1}} where zeta is
#       a primitive element of GF(q)
# Construction as in [T87]
BindGlobal("StandardGeneratorsOfLinearGroup",
function(d, q)
    local field, one, zeta, L1, L2, L3;

    field := GF(q);
    one := One(field);
    zeta := PrimitiveElement(field);

    if d = 1 then

        L1 := [[one]];
        L2 := [[zeta]];
        L3 := [[one]];

    elif q in [2, 3] then

        L1 := NullMat(d, d, field);
        L1[1, d] := one;
        L1{[2..d]}{[1..d - 1]} := -IdentityMat(d - 1, field);

        # In case q = 2, this matrix is just equal to L3, which
        # makes sense because SL(d, 2) = GL(d, 2).
        # In case q = 3, since L1 and L3 generate SL(d, 3)
        # and [ GL(d, 3): SL(d, 3) ] = 2, adjoining any matrix 
        # of determinant -1 to L1 and L2 will give GL(d, 3).
        # Since we only want 2 generators, this matrix is
        # constructed to be a square root of L3 with determinant -1,
        # so L1 and L2 must already generate GL(d, 3).
        # This differs from the matrix given in [T87] because
        # [T87] does not fulfill our requirements in case q = 3.
        # TODO: This idea does not work for d = 2, q = 3 because
        # then, L3 does not seem to have a square root with
        # determinant -1, so that case might need hardcoding.
        L2 := IdentityMat(d, field);
        L2[1, 2] := -one;
        L2[d, d] := -one;

        L3 := IdentityMat(d, field);
        L3[1, 2] := one;

    else

        L1 := NullMat(d, d, field);
        L1[1, d] := one;
        L1[1, 1] := -one;
        L1{[2..d]}{[1..d - 1]} := -IdentityMat(d - 1, field);

        L2 := IdentityMat(d, field);
        L2[1, 1] := zeta;

        L3 := IdentityMat(d, field);
        L3[1, 1] := zeta;
        L3[2, 2] := zeta ^ (-1);

    fi;

    return rec(L1 := L1, L2 := L2, L3 := L3);
end);

# Compute the spinor norm of an element of an orthogonal group.
# We use Lemma 3.5 (2) from [HR10] for q even.
#
# Note that if q is odd, the argument <form> must be the Gram matrix of the
# bilinear form preserved by the orthogonal group to which M belongs. If q is
# even, the argument <form> is redundant.
BindGlobal("FancySpinorNorm",
function(form, F, M)
    # Don't fool yourself and return One(F) and -One(F) here ... - they are the
    # same in even characteristic!
    if IsOddInt(Characteristic(F)) then
        if IsOne(SpinorNorm(form, F, M)) then
            return 1;
        else 
            return -1;
        fi;
    else
        if IsEvenInt(RankMat(M + IdentityMat(NrRows(M), F))) then
            return 1;
        else
            return -1;
        fi;
    fi;
end);

InstallGlobalFunction("MatrixGroup",
function(F, gens)
    if IsEmpty(gens) then
        ErrorNoReturn("<gens> cannot be empty"); 
    elif not IsField(F) then
        ErrorNoReturn("<F> must be a field");
    fi;
    return Group(List(gens, g -> ImmutableMatrix(F, g)));
end);

InstallGlobalFunction("MatrixGroupWithSize",
function(F, gens, size)
    local result;
    result := MatrixGroup(F, gens);
    SetSize(result, size);
    return result;
end);
