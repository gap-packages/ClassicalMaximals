# TODO
# This does not seem to construct the full GammaL(1, q ^ s): to get the full
# GammaL(1, q ^ s), we would need the Frobenius x -> x ^ p as a generator, but
# we only take x -> x ^ q. However, the results of the other functions are as
# expected -- so it seems that we do not construct the full GammaL here, but
# that we don't need it anyway?
# TODO
#
# Construction as in Lemma 6.1 of [2]
BindGlobal("GammaLDimension1",
function(s, q)
    local F, primitivePolynomial, A, x, xq, B, row, i;
    F := GF(q);
    # Let w be a primitive element of GF(q ^ s) over GF(q).
    # A acts on the standard basis in the same way as w acts by multiplication
    # on the GF(q)-basis {1, w, w ^ 2, ...} of GF(q ^ s). (Note that A is a
    # Singer cycle, i.e. has order q ^ s - 1.)
    primitivePolynomial := MinimalPolynomial(F, Z(q ^ s));
    A := TransposedMat(CompanionMat(primitivePolynomial));
    # B acts on the standard basis in the same way as the Frobenius acts on the
    # basis {1, w, w ^ 2, ...} of GF(q ^ s) over GF(q), where w is as above.
    x := IndeterminateOfUnivariateRationalFunction(primitivePolynomial);
    xq := PowerMod(x, q, primitivePolynomial);
    B := [];
    for i in [0 .. s - 1] do
        row := CoefficientsOfUnivariatePolynomial(PowerMod(xq,
                                                           i,
                                                           primitivePolynomial));
        row := Concatenation(row,
                             ListWithIdenticalEntries(s - Length(row),
                                                      Zero(F)));
        Add(B, row);
    od;
    return rec(A := A, B := B);
end);

# Return the subgroup of <M>SL(n, q)</M> induced by the group of semilinear
# transformations of the vector space <M>F'^m</M> over the field 
# <C>F' := GF(q ^ s)</C>, where <M>m := n / s</M>. (More precisely, there is
# an isomorphism of <M>F</M>-vector spaces, where <C>F := GF(q)</C>, between
# <M>F'</M> and <M>F ^ s</M>, which in turn induces an <M>F</M>-vector space
# isomorphism between <M>F'^m</M> and <M>F^n</M> and consequently an embedding
# of <M>\Gamma L(m, q ^ s)</M> into <M>GL(n, q)</M>; the intersection of the
# image of this embedding with <M>SL(n, q)</M> is a subgroup of <M>SL(n,
# q)</M>.) Note that this means <A>s</A> must be a divisor of <A>n</A>. We
# further demand that <A>s</A> be a prime number, i.e. <M>F'</M> is a prime
# extension of <M>F</M>.
# Construction as in Proposition 6.3 of [2]
BindGlobal("GammaLMeetSL",
function(n, q, s)
    local F, As, Bs, Cs, Fs, m, gammaL1, Y, A, B, C, D, DBlock, ZBlock, i,
    range, result;
    if n mod s <> 0 or not IsPrime(s) then
        ErrorNoReturn("<s> must be prime and a divisor of <n> but <s> = ", s,
                      " and <n> = ", n);
    fi;
    F := GF(q);
    gammaL1 := CLASSICALMAXIMALS_GammaLDimension1(s, q);
    # Let w be a primitive element of GF(q ^ s) over GF(q). Since As is the
    # companion matrix of the minimal polynomial of w over GF(q), its
    # determinant is (-1) ^ s times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ s * the product of
    # all Galois conjugates of w. Hence, det(As) = w ^ ((q ^ s - 1) / (q - 1)).
    As := gammaL1.A;
    # By Lemma 6.2 det(Bs) = (-1) ^ (s - 1).
    Bs := gammaL1.B;
    # det(Cs) = det(As) ^ (q - 1) = w ^ (q ^ s - 1) = 1.
    Cs := As ^ (q - 1);
    m := QuoInt(n, s);
    if m = 1 then
        if n mod 2 = 1 then
            result := Group(Bs, Cs);
        elif q mod 2 = 1 then
            Fs := (As ^ QuoInt(q - 1, 2)) * Bs;
            result := Group(Cs, Fs);
        # n = s = 2 and q even
        else
            # In characteristic 2 we have det(Bs) = -1 = 1.
            result := Group(Bs, Cs);
        fi;
        SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
        return result;
    fi;

    A := IdentityMat(n, F);
    A{[1..s]}{[1..s]} := As;
    A{[s + 1..2 * s]}{[s + 1..2 * s]} := As ^ -1;
    Y := SL(m, q ^ s).2;
    B := KroneckerProduct(Y, IdentityMat(s, F));
    C := IdentityMat(n, F);
    C{[1..s]}{[1..s]} := Cs;
    D := IdentityMat(n, F);
    # The determinant of D might be -1. In these cases, adjust D.
    if s = 2 and IsOddInt(m) and IsOddInt(q) then
        ZBlock := As ^ QuoInt(q - 1, 2);
        DBlock := ZBlock * Bs;
    else
        DBlock := Bs;
    fi;
    for i in [0..m - 1] do
        range := [i * s + 1..(i + 1) * s];
        D{range}{range} := DBlock;
    od;

    result := Group(A, B, C, D);
    # Size according to Proposition 6.3 of [2]
    SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
    return result;
end);

# Return a block matrix where the block in place (i, j) is A ^ k if and only if
# the entry M[i, j] is omega ^ k (if M[i, j] = 0 then the corresponding block
# is zero as well).
Theta := function(M, A, omega)
    local result, i, j, exponent, dimensionOfA;

    if not NumberRows(A) = NumberColumns(A) then
        ErrorNoReturn("<A> must be a square matrix but <A> = ", A);
    fi;

    dimensionOfA := NumberRows(A);
    result := NullMat(NumberRows(M) * dimensionOfA, 
                      NumberColumns(M) * dimensionOfA, 
                      DefaultFieldOfMatrix(A));

    for i in [1..NumberRows(M)] do
        for j in [1..NumberColumns(M)] do
            if not IsZero(M[i, j]) then
                exponent := LogFFE(M[i, j], omega);
                result{[(i - 1) * dimensionOfA + 1..i * dimensionOfA]}
                      {[(j - 1) * dimensionOfA + 1..j * dimensionOfA]} 
                          := A ^ exponent;
            fi;
        od;
    od;

    return result;
end;

# Construction as in Proposition 6.6 of [2]
BindGlobal("GammaLMeetSU",
function(d, q, s)
    local F, As, Bs, Cs, Fs, m, gammaL1, Y, A, B, C, D, i,
    range, result, AsInGU, omega, generators;
    if d mod s <> 0 or not IsPrime(s) or not IsOddInt(s) then
        ErrorNoReturn("<s> must be an odd prime and a divisor of <d> but <s> = ", s,
                      " and <n> = ", d);
    fi;
    F := GF(q ^ 2);
    gammaL1 := GammaLDimension1(s, q ^ 2);
    # Let w be a primitive element of GF(q ^ (2 * s)) over GF(q ^ 2). Since As is the
    # companion matrix of the minimal polynomial of w over GF(q ^ 2), its
    # determinant is (-1) ^ s times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ s * the product of
    # all Galois conjugates of w. Hence, det(As) = w ^ ((q ^ (2 * s) - 1) / (q ^ 2 - 1)).
    As := gammaL1.A;
    # By Lemma 6.2 det(Bs) = (-1) ^ (s - 1). Bs has order s as it is the
    # Frobenius of the extension GF(q ^ 2) <= GF(q ^ (2 * s)).
    Bs := gammaL1.B;
    # Raise As to the (q ^ s - 1)-th power so that the result is in GammaU(1, q ^ s).
    # AsInGU now has order q ^ s + 1 (as As had order q ^ (2 * s) - 1).
    # det(AsInGU) = w ^ ((q ^ (2 * s) - 1) / (q + 1) * (q ^ s - 1) / (q - 1))
    AsInGU := As ^ (q ^ s - 1);
    # s is odd so (q ^ s - 1) / (q - 1) = 1 + q + ... + q ^ (s - 1) and q + 1
    # are coprime. Hence, we have to raise AsInGU to the (q + 1)-th power to
    # make the determinant 1. Cs has order (q ^ s + 1) / (q + 1).
    Cs := AsInGU ^ (q + 1);
    m := QuoInt(d, s);
    if m = 1 then
        # note that we require s to be odd
        generators := [Bs, Cs];
        generators := List(generators, M -> ImmutableMatrix(F, M));
        result := Group(generators);
        # Size according to Table 2.6 of [1]
        SetSize(result, Size(SU(d / s, q ^ s)) * (q ^ s + 1) / (q + 1) * s);
        # conjugate the result so that it preserves the standard unitary form
        return ConjugateToStandardForm(result, "U");
    fi;

    omega := PrimitiveElement(GF(q ^ (2 * s)));
    # The following two matrices generate SU(m, q ^ s) as a subgroup of SU(d, q)
    A := Theta(SU(m, q ^ s).1, As, omega);
    B := Theta(SU(m, q ^ s).2, As, omega);
    # Note that GU(m, q ^ s).1 ^ (q + 1) has determinant 1.
    C := Theta(GU(m, q ^ s).1 ^ (q + 1), As, omega);
    # det(D) = 1
    D := IdentityMat(d, GF(q));
    for i in [0..m - 1] do
        range := [i * s + 1..(i + 1) * s];
        D{range}{range} := Bs;
    od;

    generators := [A, B, C, D];
    generators := List(generators, M -> ImmutableMatrix(F, M));
    result := Group(generators);
    # Size according to Table 2.6 of [1]
    SetSize(result, Size(SU(d / s, q ^ s)) * (q ^ s + 1) / (q + 1) * s);
    # conjugate the result so that it preserves the standard unitary form 
    return ConjugateToStandardForm(result, "U");
end);
