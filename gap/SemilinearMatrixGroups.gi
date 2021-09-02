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
    Cs := As ^ (q - 1);
    m := QuoInt(n, s);
    if m = 1 then
        if n mod 2 = 1 then
            result := Group(Bs, Cs);
            SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
            return result;
        elif q mod 2 = 1 then
            Fs := (As ^ QuoInt(q - 1, 2)) * Bs;
            result := Group(Cs, Fs);
            SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
            return result;
        else
            # TODO
            # This is kind of a hack and is intended to cover the case n=q=s=2
            # which is not treated in [2] at all (technically, this combination
            # of arguments will not be called by the ClassicalMaximals function
            # as SL(2, 2) is soluble - but still!); formerly, this case would
            # just land in the previous elif block, but the quotient (q-1)/2
            # would not be an integer so this is nonsense -- this is a
            # workaround using the fact that for n=q=s=2 we have
            # [[1, 1], [1, 0]]^2 = As so this matrix is some sort of "root" of
            # As; making this choice seems to give the correct results since it
            # produces a group of order 6, as expected
            # --> talk this over with Sergio!!
            rootAs := Z(2) * [[1, 1], [1, 0]];
            Fs := rootAs * Bs;
            result := Group(Cs, Fs);
            SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
            return result;
        fi;
    fi;

    A := IdentityMat(n, GF(q));
    A{[1..s]}{[1..s]} := As;
    A{[s + 1..2 * s]}{[s + 1..2 * s]} := As ^ -1;
    Y := SL(m, q ^ s).2;
    B := KroneckerProduct(Y, IdentityMat(s, GF(q)));
    C := IdentityMat(n, GF(q));
    C{[1..s]}{[1..s]} := Cs;
    D := IdentityMat(n, GF(q));
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
