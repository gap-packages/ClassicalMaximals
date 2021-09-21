# Return the subgroup of <M>SL(n, q)</M> stabilising a
# decomposition <M>F^n=V_1\oplus V_2\oplus\dots\oplus V_t</M> of <M>F^n</M>,
# where <C>F := GF(q)</C>, as a direct sum of vector spaces of equal
# dimensions. Note that this means that <A>t</A> must be a divisor of <A>n</A>.
# We demand that <A>t</A> be greater than 1.
# Construction as in Proposition 5.1 of [2]
BindGlobal("ImprimitivesMeetSL", 
function(n, q, t)
    local det, E, gens, i, newGen, newGens, wreathProduct, z, m, result;
    if t = 1 or (n mod t) <> 0 then
        ErrorNoReturn("<t> must be greater than 1 and a divisor of <n> but <t> = ", t,
                      " and <n> = ", n);
    fi;
    m := QuoInt(n, t);
    wreathProduct := MatWreathProduct(SL(m, q), SymmetricGroup(t));
    gens := GeneratorsOfGroup(wreathProduct);
    # newGens will be analogous to A, B, C, D in [2]
    newGens := [];
    for i in [1..Length(gens)] do
        det := Determinant(gens[i]);
        if IsOne(det) then
            Add(newGens, gens[i]);
        else
            # rescale first column by -1
            newGen := gens[i] * DiagonalMat(Z(q) ^ 0
                * Concatenation([-1], List([2..n], i -> 1)));
            Add(newGens, newGen);
        fi;
    od;
    z := PrimitiveElement(GF(q));
    E := DiagonalMat(
        Concatenation([z], List([2..m], i -> z ^ 0),
                      [z ^ -1], List([m + 2..n], i -> z ^ 0))
    );
    Add(newGens, E);
    result := Group(newGens);
    # Size according to Table 2.5 of [1]
    SetSize(result, Size(SL(n/t, q)) ^ t * (q-1) ^ (t-1) * Factorial(t));
    return result;
end);

# Construction as in Proposition 5.5 of [2]
# The decomposition stabilized is given by the summands 
# < e_1, ..., e_{d / 2} > and < f_{d / 2}, ..., f_1 >, 
# where (e_1, ..., e_{d / 2}, f_{d / 2}, ..., f_1) is the standard basis.
BindGlobal("SUIsotropicImprimitives",
function(d, q)
    local F, zeta, generators, automorphism, J, generatorsOfSL, generatorOfSL,
    generator, C, D, result;
    if not IsEvenInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    generators := [];
    automorphism := x -> x ^ q;
    J := AntidiagonalMat(List([1..d / 2], i -> 1), F);

    # first generate SL(d / 2, q ^ 2) as a subgroup of SU(d, q)
    generatorsOfSL := GeneratorsOfGroup(SL(d / 2, q ^ 2));
    for generatorOfSL in generatorsOfSL do
        generator := NullMat(d, d, F);
        generator{[1..d / 2]}{[1..d / 2]} := generatorOfSL;
        generator{[d / 2 + 1..d]}{[d / 2 + 1..d]} := J * ApplyFunctionToEntries(TransposedMat(generatorOfSL) ^ (-1),
                                                                                automorphism) 
                                                       * J;
        Add(generators, generator);
    od;

    # now a matrix switching the two summands
    C := NullMat(d, d, F);
    C{[1..d / 2]}{[d / 2 + 1..d]} := IdentityMat(d / 2, F);
    C{[d / 2 + 1..d]}{[1..d / 2]} := IdentityMat(d / 2, F);
    # We have det(C) = 1 if d = 0 mod 4 and det(C) = -1 if d = 2 mod 4.
    # Hence, if d = 2 mod 4 and q is odd, we have to multiply C with a matrix
    # of determinant -1.
    if d mod 4 <> 0 and IsOddInt(q) then
        C := C * DiagonalMat(Concatenation([zeta ^ QuoInt(q + 1, 2)],
                                           List([2..d - 1], i -> zeta ^ 0),
                                           [zeta ^ (-q * QuoInt(q + 1, 2))]));
    fi;
    Add(generators, C);

    # finally a diagonal matrix accounting for the fact that the determinants
    # of the two blocks can be anything as long as they multiply to 1
    # Note that the original Magma code and [2] use
    #   D := DiagonalMat(Concatenation([zeta, zeta ^ q], 
    #                                  List([3..d - 2], i -> zeta ^ 0),
    #                                  [zeta ^ (-1), zeta ^ (-q)]));
    # but this obviously does not work for d = 2; the construction below,
    # however, works for all d.
    D := DiagonalMat(Concatenation([zeta ^ (q + 1)],
                                   List([2..d - 1], i -> zeta ^ 0),
                                   [zeta ^ (-q - 1)]));
    Add(generators, D);

    result := Group(generators);
    # Size according to Table 2.5 of [1]
    SetSize(result, Size(SL(d / 2, q ^ 2)) * (q - 1) * 2);

    return result;
end);
