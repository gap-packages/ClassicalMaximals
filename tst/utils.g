LoadPackage("recog");
LoadPackage( "ClassicalMaximals" );

CheckSize := function(G)
  local lvl, ri;
  if not HasSize(G) then
    Error("size not set");
  fi;
  # skip extra tests using group recognition?
  if IsBound(QUICK_CLASSICAL_MAXIMALS_TESTS) then
    return;
  fi;
  lvl:=InfoLevel(InfoRecog);
  SetInfoLevel(InfoRecog, 0);
  ri := RecogniseGroup(G);
  SetInfoLevel(InfoRecog, lvl);
  if Size(ri) <> Size(G) then
    Error("bad size");
  fi;
end;

CheckGeneratorsInvertible := function(G)
  if ForAny(GeneratorsOfGroup(G), g -> IsZero(Determinant(g))) then
    Error("not all generators are invertible");
  fi;
end;

CheckGeneratorsSpecial := function(G)
  if not ForAll(GeneratorsOfGroup(G), g -> IsOne(Determinant(g))) then
    Error("not all generators have determinant one");
  fi;
end;

# GAP's SL, SU, Sp or Omega for the type names of ClassicalMaximalsGeneric
StandardClassicalGroup := function(type, n, q)
  return rec(L := SL, U := SU, S := Sp, O := OmegaZero,
             ("O+") := OmegaPlus, ("O-") := OmegaMinus).(type)(n, q);
end;

# verify that the subgroups in L of Omega(epsilon, n, q), for type "O", "O+" or
# "O-", are pairwise non-conjugate, using the action on singular points
CheckPairwiseNonConjugateOmega := function(type, n, q, L)
  local Om, Q, v, hom, P, images, i, j;
  Om := StandardClassicalGroup(type, n, q);
  Q := InvariantQuadraticForm(Om).matrix;
  v := First(GF(q) ^ n, w -> not IsZero(w) and IsZero(w * Q * w));
  hom := ActionHomomorphism(Om, Orbit(Om, NormedRowVector(v), OnLines), OnLines);
  P := Image(hom);
  images := List(L, G -> ImagesSet(hom, G));
  for i in [1..Length(L)] do
    for j in [i + 1..Length(L)] do
      if Size(images[i]) = Size(images[j]) and IsConjugate(P, images[i], images[j]) then
        Error("groups ", i, " and ", j, " are conjugate");
      fi;
    od;
  od;
end;

# Pfaffian of a skew-symmetric matrix over a field of odd characteristic, by
# congruence transformations to a sum of 2x2 blocks
Pfaffian := function(A)
  local n, pf, i, j, k, c, row;
  A := MutableCopyMat(A);
  n := NrRows(A);
  pf := One(A[1, 1]);
  for i in [1, 3 .. n - 1] do
    j := First([i + 1 .. n], j -> not IsZero(A[i, j]));
    if j = fail then
      return Zero(pf);
    fi;
    if j <> i + 1 then
      A{[i + 1, j]} := A{[j, i + 1]};
      A{[1 .. n]}{[i + 1, j]} := A{[1 .. n]}{[j, i + 1]};
      pf := -pf;
    fi;
    pf := pf * A[i, i + 1];

    # clear rows and columns i, i + 1 outside the block
    for k in [i + 2 .. n] do
      for row in [[i, i + 1], [i + 1, i]] do
        c := A[row[1], k] / A[row[1], row[2]];
        A[k] := A[k] - c * A[row[2]];
        A{[1 .. n]}[k] := A{[1 .. n]}[k] - c * A{[1 .. n]}[row[2]];
      od;
    od;
  od;
  return pf;
end;

# For a subgroup G of Omega+(n, q), q odd, with bilinear form F, count the
# elements g of G by the nonzero values of Pf((g - g^-1) F). Conjugation by
# an isometry h multiplies the Pfaffian by det(h), so unequal counts prove
# that two groups are not conjugate in SO, let alone in Omega. This also
# works in dimensions out of reach of CheckPairwiseNonConjugateOmega.
PfaffianCounts := function(G)
  local F, counts, C, g, pf;
  F := InvariantBilinearForm(G).matrix;
  counts := [];
  for C in ConjugacyClasses(G) do
    g := Representative(C);
    pf := Pfaffian((g - g ^ -1) * F);
    if not IsZero(pf) then
      Add(counts, [pf, Size(C)]);
    fi;
  od;
  return List(Set(counts, c -> c[1]),
              pf -> [pf, Sum(Filtered(counts, c -> c[1] = pf), c -> c[2])]);
end;

# compare the orders of the results of ClassicalMaximalsGeneric with those of
# the maximal subgroups in the character table library; a maximal subgroup of
# a perfect group contains the centre, so the orders differ by its order. The
# optional argument names the simple group where the library has no alias.
CheckMaximalOrders := function(type, n, q, opt...)
  local name, tbl, G, z, orders, expected;
  if Length(opt) = 1 then
    name := opt[1];
  elif type in ["O+", "O-"] then
    name := Concatenation("O", String(n), type{[2]}, "(", String(q), ")");
  else
    name := Concatenation(type, String(n), "(", String(q), ")");
  fi;
  tbl := CharacterTable(name);
  if tbl = fail or not HasMaxes(tbl) then
    Error("no stored maximal subgroups of ", name);
  fi;

  G := StandardClassicalGroup(type, n, q);
  z := Size(G) / Size(tbl);
  orders := SortedList(List(ClassicalMaximalsGeneric(type, n, q), H -> Size(H) / z));
  expected := SortedList(List(Maxes(tbl), m -> Size(CharacterTable(m))));
  if orders <> expected then
    Error("maximal subgroups of ", name, " have orders ", orders,
          ", expected ", expected);
  fi;
end;

# verify that forms are given and preserved
CheckBilinearForm := function(G)
  local M;
  M := InvariantBilinearForm(G).matrix;
  if not ForAll(GeneratorsOfGroup(G), g -> g * M * TransposedMat(g) = M) then
    Error("not all generators preserve the bilinear form");
  fi;
end;

CheckQuadraticForm := function(G)
  local M, Q;
  M := InvariantBilinearForm(G).matrix;
  Q := InvariantQuadraticForm(G).matrix;
  if Q + TransposedMat(Q) <> M then
    Error("incompatible quadratic and bilinear form");
  fi;

  if not ForAll(GeneratorsOfGroup(G), g -> RespectsQuadraticForm(Q, g)) then
    Error("not all generators preserve the quadratic form");
  fi;
end;

CheckSesquilinearForm := function(G, q)
  local M;
  M := InvariantSesquilinearForm(G).matrix;
  if not ForAll(GeneratorsOfGroup(G), g -> g * M * HermitianConjugate(g,q) = M) then
    Error("not all generators preserve the sesquilinear form");
  fi;
end;

CheckIsSubsetSL := function(n, q, G)
  local m;
  m := DimensionOfMatrixGroup(G);
  if m <> n then
    Error("matrix group: expected degree ", n, " actual degree ", m);
  fi;
  if not IsSubset(GF(q), FieldOfMatrixGroup(G)) then
    Error("matrix group: entries not in GF(", q, ")");
  fi;
  CheckGeneratorsSpecial(G);
end;

# the matrix of the quadratic form with matrix Q that is upper triangular,
# hence unique
UpperTriangularQuadraticForm := function(Q)
  local n, N, i, j;
  n := NrRows(Q);
  N := List(Q, List);
  for i in [1..n] do
    for j in [1..i - 1] do
      N[j][i] := N[j][i] + N[i][j];
      N[i][j] := Zero(N[i][j]);
    od;
  od;
  return N;
end;

# The form of GAP's SU, Sp or Omega that the checks below compare with:
# sesquilinear, bilinear, or for Omega in even characteristic quadratic. The
# forms of Omega and SO differ; the standard one is that of Omega.
STANDARD_FORMS := rec();
StandardForm := function(type, n, q)
  local key, S;
  key := Concatenation(type, String(n), "_", String(q));
  if IsBound(STANDARD_FORMS.(key)) then
    return STANDARD_FORMS.(key);
  fi;
  if type = "U" then
    STANDARD_FORMS.(key) := InvariantSesquilinearForm(SU(n, q)).matrix;
  elif type = "S" then
    STANDARD_FORMS.(key) := InvariantBilinearForm(Sp(n, q)).matrix;
  else
    S := Omega(Position(["O-", "O", "O+"], type) - 2, n, q);
    if IsEvenInt(q) then
      STANDARD_FORMS.(key) := UpperTriangularQuadraticForm(InvariantQuadraticForm(S).matrix);
    else
      STANDARD_FORMS.(key) := InvariantBilinearForm(S).matrix;
    fi;
  fi;
  return STANDARD_FORMS.(key);
end;

# Verify that the stored form A is the standard form B up to a scalar. Compare
# plain lists: = is false for equal compressed matrices over GF(2) and GF(4).
CheckStandardForm := function(A, B)
  local pos, lambda;
  A := List(A, List);
  B := List(B, List);
  pos := PositionNonZero(Flat(B));
  lambda := Flat(A)[pos] / Flat(B)[pos];
  if IsZero(lambda) or A <> lambda * B then
    Error("stored form is not GAP's standard form up to a scalar");
  fi;
end;

CheckIsSubsetSp := function(n, q, G)
  CheckIsSubsetSL(n, q, G);
  CheckBilinearForm(G);
  CheckStandardForm(InvariantBilinearForm(G).matrix, StandardForm("S", n, q));
end;

CheckIsSubsetSU := function(n, q, G)
  CheckIsSubsetSL(n, q ^ 2, G);
  CheckSesquilinearForm(G, q);
  CheckStandardForm(InvariantSesquilinearForm(G).matrix, StandardForm("U", n, q));
end;

CheckIsSubsetOmega := function(epsilon, n, q, G)
  local field, invariantForm, type;
  CheckIsSubsetSL(n, q, G);
  field := GF(q);
  type := ["O-", "O", "O+"][epsilon + 2];
  if IsEvenInt(q) then
    CheckQuadraticForm(G);
    invariantForm := QuadraticFormByMatrix(InvariantQuadraticForm(G).matrix, field);
    CheckStandardForm(UpperTriangularQuadraticForm(InvariantQuadraticForm(G).matrix),
                      StandardForm(type, n, q));
  else
    CheckBilinearForm(G);
    invariantForm := BilinearFormByMatrix(InvariantBilinearForm(G).matrix, field);
    CheckStandardForm(InvariantBilinearForm(G).matrix, StandardForm(type, n, q));
  fi;
  if 2 * WittIndex(invariantForm) <> n + epsilon - 1 then
    Error("wrong Witt index");
  fi;
  if not ForAll(GeneratorsOfGroup(G), g -> FancySpinorNorm(InvariantBilinearForm(G).matrix, field, g) = 1) then
    Error("wrong spinor norm");
  fi;
end;

# type as for ClassicalMaximalsGeneric
CheckIsSubsetClassicalGroup := function(type, n, q, G)
  if type = "L" then
    CheckIsSubsetSL(n, q, G);
  elif type = "U" then
    CheckIsSubsetSU(n, q, G);
  elif type = "S" then
    CheckIsSubsetSp(n, q, G);
  else
    CheckIsSubsetOmega(Position(["O-", "O", "O+"], type) - 2, n, q, G);
  fi;
end;

# ClassicalMaximalsGeneric with every result checked; returns the number of
# results
NrCheckedMaximals := function(type, n, q, opts...)
  local L, G;
  L := CallFuncList(ClassicalMaximalsGeneric, Concatenation([type, n, q], opts));
  for G in L do
    CheckIsSubsetClassicalGroup(type, n, q, G);
  od;
  return Length(L);
end;
