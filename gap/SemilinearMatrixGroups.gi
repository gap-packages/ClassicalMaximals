# Construction as in Lemma 6.1 of [2]
InstallGlobalFunction(CLASSICALMAXIMALS_GammaLDimension1,
function(s, q)
    local A, B, primitivePolynomial, x, xq;
    # Let w be a primitive element of GF(q ^ s) over GF(q).
    # A acts on the standard basis in the same way as w acts by multiplication
    # on the GF(q)-basis {1, w, w ^ 2, ...} of GF(q ^ s).
    primitivePolynomial := MinimalPolynomial(GF(q), Z(q ^ s));
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
                                                      Zero(GF(q))));
        Add(B, row);
    od;
    return rec(A := A, B := B);
end);

# Construction as in Proposition 6.3 of [2]
InstallGlobalFunction(GammaLMeetSL,
function(n, q, s)
    local As, rootAs, Bs, Cs, Fs, m, gammaL1, Y, A, B, C, D, DBlock, ZBlock, i,
    range, result;
    if n mod s <> 0 or not IsPrime(s) then
        ErrorNoReturn("<s> must be prime and a divisor of <n> but <s> = ", s,
                      "<n> = ", n);
    fi;
    gammaL1 := CLASSICALMAXIMALS_GammaLDimension1(s, q);
    As := gammaL1.A;
    Bs := gammaL1.B;
    # Let w be a primitive element of GF(q ^ s) over GF(q). Since As is the
    # companion matrix of the minimal polynomial of w over GF(q), its
    # determinant is (-1) ^ s times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ s * the product of 
    # all Galois conjugates of w. Hence, det(As) = w ^ ((q ^ s - 1) / (q - 1)).
    # Now det(Cs) = det(As) ^ (q - 1) = w ^ (q ^ s - 1) = 1.
    Cs := As ^ (q - 1);
    m := QuoInt(n, s);
    if m = 1 then
        if n mod 2 = 1 then
            result := Group(Bs, Cs);
        elif q mod 2 = 1 then
            Fs := (As ^ QuoInt(q - 1, 2)) * Bs;
            result := Group(Cs, Fs);
        else
            # Although det(Bs) = -1 in the present case of s = 2, this is not a
            # problem since, in this case we have q mod 2 = 1 and so the field
            # GF(q) has characteristic 2, i.e. -1 = 1 and det(Bs) = 1.
            result := Group(Bs, Cs);
        fi;
        SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
        return result;
    fi;

    A := IdentityMat(n, GF(q));
    A{[1..s]}{[1..s]} := As;
    A{[s + 1..2 * s]}{[s + 1..2 * s]} := As ^ -1;
    Y := SL(m, q ^ s).2;
    B := KroneckerProduct(Y, IdentityMat(s, GF(q)));
    C := IdentityMat(n, GF(q));
    C{[1..s]}{[1..s]} := Cs;
    D := IdentityMat(n, GF(q));
    # As above, the case q even is trivial.
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
    SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
    return result;
end);
