# Return the subgroup of <M>SL(n, p ^ e)</M> induced by the subgroup of
# <M>GL(n, p ^ e)</M> generated by <M>GL(n, p ^ f)</M> and the center
# <M>Z(GL(n, p ^ e))</M> (i.e. all scalar matrices), where <C>GF(p ^ f)</C> is
# a subfield of <C>GF(p ^ e)</C>. Note that this means <A>f</A> must be a
# divisor of <A>e</A>. We further demand that <A>p</A> be a prime number and
# that the quotient <C>f / e</C> be a prime number as well, i.e. <C>GF(p ^ e)
# </C> is a prime extension of <C>GF(p ^ f)</C>.
# Construction as in Proposition 8.1 of [HR05] 
BindGlobal("SubfieldSL", 
function(n, p, e, f)
    local F, A, B, C, D, c, k, matrixForCongruence, lambda, zeta, omega, z, X,
        result;
    if e mod f <> 0 or not IsPrimeInt(QuoInt(e, f)) then
        ErrorNoReturn("<f> must be a divisor of <e> and their quotient must be a prime but <e> = ", 
                      e, " and <f> = ", f);
    fi;

    F := GF(p ^ e);
    A := SL(n, p ^ f).1;
    B := SL(n, p ^ f).2;
    zeta := PrimitiveElement(F);
    k := Gcd(p ^ e - 1, n);
    c := QuoInt((k * Lcm(p ^ f - 1, QuoInt((p ^ e - 1), k))), (p ^ e - 1));
    C := zeta ^ (QuoInt(p ^ e - 1, k)) * IdentityMat(n, F);

    if c = Gcd(p ^ f - 1, n) then
        result := Group(A, B, C);
        # Size according to Table 2.8 of [BHR13]
        SetSize(result, Size(SL(n, p ^ f)) * Gcd(QuoInt(p ^ e - 1, p ^ f -
        1), n));
        return result;
    fi;

    omega := zeta ^ QuoInt(p ^ e - 1, p ^ f - 1);
    D := DiagonalMat(Concatenation([omega], List ([2..n], i -> zeta^0))) ^ c;

    # solving the congruence lambda * n = z (mod p ^ e - 1) by solving the
    # matrix equation (n, p ^ e - 1) * (lambda, t) ^ T = z over the integers
    matrixForCongruence := [[n], [p ^ e - 1]];
    z := c * QuoInt(p ^ e - 1, p ^ f - 1);
    lambda := SolutionMat(matrixForCongruence, [z])[1];

    X := zeta ^ (-lambda) * IdentityMat(n, F);
    result := Group(A, B, C, X * D);
    # Size according to Table 2.8 of [BHR13]
    SetSize(result,
            Size(SL(n, p ^ f)) * Gcd(QuoInt(p ^ e - 1, p ^ f - 1), n)); 
    return result;
end);

# Construction as in Proposition 8.3 of [HR05]
BindGlobal("UnitarySubfieldSU",
function(d, p, e, f)
    local F, A, B, C, D, c, k, q, matrixForCongruence, lambda, zeta, omega, z, X,
        result, generators;

    if e mod f <> 0 or not IsPrimeInt(QuoInt(e, f)) or not IsOddInt(QuoInt(e, f)) then
        ErrorNoReturn("<f> must be a divisor of <e> and their quotient must be",
                      "an odd prime but <e> = ", e, " and <f> = ", f);
    fi;

    q := p ^ e;
    F := GF(q ^ 2);
    A := SU(d, p ^ f).1;
    B := SU(d, p ^ f).2;
    zeta := PrimitiveElement(F);
    k := Gcd(q + 1, d);
    c := QuoInt(k * Lcm(p ^ f + 1, QuoInt(q + 1, k)), q + 1);
    # generates the center of SU(d, q)
    C := zeta ^ QuoInt(q ^ 2 - 1, k) * IdentityMat(d, F);

    if c = Gcd(p ^ f + 1, d) then
        generators := [A, B, C];
        # generators := List(generators, M -> ImmutableMatrix(F, M));
        result := Group(generators);
        # Size according to Table 2.8 of [BHR13]
        SetSize(result, Size(SU(d, p ^ f)) * Gcd(QuoInt(q + 1, p ^ f + 1), d));
        return result;
    fi;

    # a primitive element of GF(p ^ (2 * f))
    omega := zeta ^ QuoInt(q ^ 2 - 1, p ^ (2 * f) - 1);
    D := DiagonalMat(Concatenation([omega], 
                                   List([2..d - 1], i -> zeta ^ 0),
                                   [omega ^ (-p ^ f)])) ^ c;
    
    # det(D) = zeta ^ z
    z := - c * QuoInt(q ^ 2 - 1, p ^ f + 1);
    # solving the congruence lambda * (q - 1) * d = -z (mod q ^ 2 - 1)
    # by calculating (d / k) ^ (-1) (mod (q + 1) / k).
    lambda := - QuoInt(z, (q - 1) * k) * ((d / k) ^ (-1) mod ((q + 1) / k));
    # det(X) = 1 by construction of lambda
    X := zeta ^ (lambda * (q - 1)) * IdentityMat(d, F);

    generators := [A, B, C, X * D];
    generators := List(generators, M -> ImmutableMatrix(F, M));
    result := Group(generators);
    # Size according to Table 2.8 of [BHR13]
    SetSize(result, Size(SU(d, p ^ f)) * Gcd(QuoInt(q + 1, p ^ f + 1), d)); 

    return result;
end);

# Construction as in Proposition 8.5 of [HR05]
BindGlobal("SymplecticSubfieldSU",
function(d, q)
    local F, generators, zeta, k, C, c, result, D, form;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    F := GF(q ^ 2);
    form := AntidiagonalMat(Concatenation(List([1..d / 2], i -> One(F)),
                                          List([1..d / 2], i -> -1)) * Z(q ^ 2)^0,
                            F);
    generators := ShallowCopy(GeneratorsOfGroup(Sp(d, q)));
    zeta := PrimitiveElement(F);
    k := Gcd(q + 1, d);
    # generates the center of SU(d, q)
    C := zeta ^ QuoInt(q ^ 2 - 1, k) * IdentityMat(d, F);
    Add(generators, C);
    c := QuoInt(Gcd(2, q - 1) * Gcd(q + 1, d / 2), Gcd(q + 1, d));

    if c <> 1 then
        # q is odd and d = 0 mod 4 if c <> 1
        #
        # D preserves the standard symplectic form Antidiag(1, ..., 1, -1, ..., -1) 
        # up to a factor of -1. det(D) = 1 since d = 0 mod 4.
        D := DiagonalMat(Concatenation(List([1..d / 2], i -> zeta ^ ((q + 1) / 2)),
                                       List([1..d / 2], i -> - zeta ^ (- (q + 1) / 2))));
        Add(generators, D);
    fi;
    
    generators := List(generators, M -> ImmutableMatrix(F, M));
    result := Group(generators);
    if IsOddInt(q) then
        # The result preserves the unitary form given by 
        # - zeta ^ ((q + 1) / 2) * Antidiag(1, ..., 1, -1, ..., -1);
        # we conjugate it to preserve the standard unitary form given by
        # Antidiag(1, ..., 1). (If q is even, this is not necessary.)
        SetInvariantSesquilinearForm(result, 
                                     rec(matrix := - zeta ^ QuoInt(q + 1, 2) * form));
        result := ConjugateToStandardForm(result, "U");
    fi;
    # Size according to Table 2.8 of [BHR13]
    SetSize(result, Size(Sp(d, q)) * Gcd(q + 1, d / 2));

    return result;
end);

# Construction as in Proposition 8.4 of [HR05]
BindGlobal("OrthogonalSubfieldSU",
function(epsilon, d, q)
    local F, zeta, k, C, generators, SOChangedForm, result,
    generatorsOfOrthogonalGroup, D, E, i, W, n, form;

    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be an odd integer but <q> = ", q);
    elif epsilon = 0 and IsEvenInt(d) then
        ErrorNoReturn("<epsilon> cannot be zero if <d> is even but", 
                      "<epsilon> = ", epsilon, " and <d> = ", d);
    elif epsilon <> 0 and IsOddInt(d) then
        ErrorNoReturn("<epsilon> must be zero if <d> is odd but",
                      "<epsilon> = ", epsilon, " and <d> = ", d);
    elif not epsilon in [-1, 0, 1] then
        ErrorNoReturn("<epsilon> must be one of -1, 0, 1 but",
                      "<epsilon> = ", epsilon);
    fi;

    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    k := Gcd(q + 1, d);
    # generates the center of SU(d, q)
    C := zeta ^ QuoInt(q ^ 2 - 1, k) * IdentityMat(d, F);
    generators := [C];

    if IsOddInt(d) then
        SOChangedForm := ChangeFixedSesquilinearForm(SO(d, q),
                                                     "O",
                                                     AntidiagonalMat(d, F));
        generators := Concatenation(generators, GeneratorsOfGroup(SOChangedForm));
        generators := List(generators, M -> ImmutableMatrix(F, M));
        result := Group(generators);
    else
        generatorsOfOrthogonalGroup := GeneratorsOfOrthogonalGroup(epsilon, d, q);
        generators := Concatenation(generators, generatorsOfOrthogonalGroup.generatorsOfSO);
        # det(D) = -1 
        D := generatorsOfOrthogonalGroup.D;
        # det(E) = (epsilon * zeta ^ (q + 1)) ^ (d / 2)
        # E scales the standard orthogonal form F by a factor of zeta ^ (q + 1)
        E := generatorsOfOrthogonalGroup.E;
        # Multiplying by zeta ^ (-1) will lead to E preserving the form F *as a
        # unitary form* !!
        # det(E) = (epsilon * zeta ^ (q - 1)) ^ (d / 2)
        E := zeta ^ (-1) * E;

        if epsilon = 1 then
            # We already have generators for Z(SU(d, q)).SO(d, q);
            # additionally, an element W of order 2 mod Z(SU(d, q)).SO(d, q) is
            # needed.
            if IsEvenInt((q + 1) / k) then
                i := QuoInt(q ^ 2 - 1, 2 * k);
                # det(W) = 1 because det(D) = -1 and
                #   zeta ^ (i * d) = zeta ^ ((q ^ 2 - 1) * d / (2 * Gcd(q + 1, d)))
                #                  = zeta ^ ((q ^ 2 - 1) / 2) = -1
                # since d / Gcd(q + 1, d) is an odd integer by assumption.
                #
                # Multiplying D by zeta ^ i will not affect the result
                # preserving our unitary form since i is divisble by q - 1.
                W := zeta ^ i * D;
            elif IsEvenInt(d / k) then
                i := (q - 1) * ((q + 1) / k + 1) / 2;
                # det(W) = 1 because det(E) = (zeta ^ (q - 1)) ^ (d / 2) and
                #   zeta ^ (i * d) = zeta ^ (d * (q - 1) * ((q + 1) / k + 1) / 2)
                #                  = zeta ^ (d * (q - 1) / 2)
                #
                # Multiplying E by zeta ^ (-i) will not affect the result
                # preserving our unitary form since i is divisible by q - 1.
                W := zeta ^ (-i) * E;
            else 
                n := (k / d) mod ((q + 1) / k); 
                i := (q - 1) * n * (d + q + 1) / (2 * k);
                # det(W) = 1 because det(D) = -1, det(E) = zeta ^ (d * (q - 1) / 2)
                # and i * d mod q ^ 2 - 1 is
                #   (q - 1) * n * (d + q + 1) * d / (2 * k)
                #        = (q - 1) * (d + q + 1) / 2 
                #           + (q - 1) * (d + q + 1) * (n * d / k - 1) / 2
                #        = (q - 1) * (d + q + 1) / 2 = det(D * E) ^ (-1)
                # since the second summand is divisible by q - 1 (first
                # factor), by 2 * k (second factor; since d and q + 1 have the
                # same 2-adic valuation here) and by (q + 1) / k (third
                # factor), hence by q ^ 2 - 1.
                #
                # Multiplying D * E by zeta ^ (-i) will not affect the result
                # preserving our unitary form since i is divisible by q - 1.
                W := zeta ^ (-i) * D * E;
            fi;
            Add(generators, W);

            # the standard orthogonal form in this case is Antidiag(1, ..., 1),
            # i.e. has the same form matrix as the unitary form we want, so we
            # do not need to conjugate the result
            generators := List(generators, M -> ImmutableMatrix(F, M));
            result := Group(generators);

        elif epsilon = -1 then

            # similarly to above
            if IsEvenInt((q + 1) / k) then
                i := QuoInt(q ^ 2 - 1, 2 * k);
                W := zeta ^ i * D;
            elif IsEvenInt(d / k) then
                i := (q - 1) * ((q + 1) / k + 1) / 2;
                W := zeta ^ (-i) * E;
            elif IsEvenInt(d / 2) then
                n := (k / d) mod ((q + 1) / k); 
                i := (q - 1) * n * (d + q + 1) / (2 * k);
                W := zeta ^ (-i) * D * E;
            else
                # We have to make an additional exception in the last case if 
                # d / 2 is odd as we have an additional factor of -1 in the
                # determinant in this case due to 
                #   det(E) = (epsilon * zeta ^ (q - 1)) ^ (d  / 2) 
                #          = - zeta ^ ((q - 1) * d / 2) 
                # here.
                n := (k / d) mod ((q + 1) / k); 
                i := (q - 1) * n * (d + q + 1) / (2 * k);
                W := zeta ^ (-i) * E;
            fi;
            Add(generators, W);

            generators := List(generators, M -> ImmutableMatrix(F, M));
            result := Group(generators);

            # We still have to change the preserved unitary form to the
            # standard GAP unitary form Antidiag(1, ..., 1)
            if IsEvenInt(d * (q - 1) / 4) then
                # The form preserved by the constructed subgroup is given by
                # the matrix Diag(zeta ^ (q + 1), 1, ..., 1).
                form := DiagonalMat(Concatenation([zeta ^ (q + 1)],
                                                  List([2..d], i -> zeta ^ 0)));
                SetInvariantSesquilinearForm(result, rec(matrix := form));
                result := ConjugateToStandardForm(result, "U");
            else
                # The form preserved by the constructed subgroup is given by
                # the identity matrix.
                form := IdentityMat(d, F);
                SetInvariantSesquilinearForm(result, rec(matrix := form));
                result := ConjugateToStandardForm(result, "U");
            fi;
        fi;
    fi;

    # Size according to Table 2.8 of [BHR13]
    SetSize(result, Size(SO(epsilon, d, q)) * Gcd(q + 1, d));

    return result;
end);
