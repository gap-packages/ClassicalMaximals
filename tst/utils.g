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

# verify that the subgroups in L of Omega(epsilon, n, q), for type "O", "O+" or
# "O-", are pairwise non-conjugate, using the action on singular points
CheckPairwiseNonConjugateOmega := function(type, n, q, L)
  local Om, Q, v, hom, P, images, i, j;
  Om := Omega(rec(O := 0, ("O+") := 1, ("O-") := -1).(type), n, q);
  Q := InvariantQuadraticForm(Om).matrix;
  v := First(GF(q) ^ n, w -> not IsZero(w) and IsZero(w * Q * w));
  hom := ActionHomomorphism(Om, Orbit(Om, NormedRowVector(v), OnLines), OnLines);
  P := Image(hom);
  images := List(L, G -> Group(List(GeneratorsOfGroup(G), g -> ImageElm(hom, g))));
  for i in [1..Length(L)] do
    for j in [i + 1..Length(L)] do
      if Size(images[i]) = Size(images[j]) and IsConjugate(P, images[i], images[j]) then
        Error("groups ", i, " and ", j, " are conjugate");
      fi;
    od;
  od;
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
  local m, F;
  m := DimensionOfMatrixGroup(G);
  if m <> n then
    Error("matrix group: expected degree ", n, " actual degree ", m);
  fi;
  F := DefaultFieldOfMatrixGroup(G);
  if Characteristic(F) <> PrimePowersInt(q)[1] then
      Error("matrix group: wrong characteristic of underlying field");
  fi;
  CheckGeneratorsSpecial(G);
end;

CheckIsSubsetSp := function(n, q, G)
  CheckIsSubsetSL(n, q, G);
  CheckBilinearForm(G);
end;

CheckIsSubsetSU := function(n, q, G)
  CheckIsSubsetSL(n, q ^ 2, G);
  CheckSesquilinearForm(G, q);
end;

CheckIsSubsetOmega := function(epsilon, n, q, G)
  local field, invariantForm;
  CheckIsSubsetSL(n, q, G);
  field := GF(q);
  if IsEvenInt(q) then
    CheckQuadraticForm(G);
    invariantForm := QuadraticFormByMatrix(InvariantQuadraticForm(G).matrix, field);
  else
    CheckBilinearForm(G);
    invariantForm := BilinearFormByMatrix(InvariantBilinearForm(G).matrix, field);
  fi;
  if 2 * WittIndex(invariantForm) <> n + epsilon - 1 then
    Error("wrong Witt index");
  fi;
  if not ForAll(GeneratorsOfGroup(G), g -> FancySpinorNorm(InvariantBilinearForm(G).matrix, field, g) = 1) then
    Error("wrong spinor norm");
  fi;
end;
