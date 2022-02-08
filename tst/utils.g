CheckSize := function(G)
  local lvl, ri;
  if not HasSize(G) then
    Error("size not set");
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

CheckSesquilinearForm := function(G)
  local M, F, q;
  M := InvariantSesquilinearForm(G).matrix;
  F := DefaultFieldOfMatrixGroup(G);
  q := RootInt(Size(F));
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
    Error("matrix group: expected field of size ", q, " actual size ", Size(F));
  fi;
  CheckGeneratorsSpecial(G);
end;

CheckIsSubsetSp := function(n, q, G)
  CheckIsSubsetSL(n, q, G);
  CheckBilinearForm(G);
end;

CheckIsSubsetSU := function(n, q, G)
  CheckIsSubsetSL(n, q ^ 2, G);
  CheckSesquilinearForm(G);
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
