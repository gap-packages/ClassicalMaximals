CheckSize := function(G)
  local lvl, ri;
  Assert(0, HasSize(G));
  lvl:=InfoLevel(InfoRecog);
  SetInfoLevel(InfoRecog, 0);
  ri := RecogniseGroup(G);
  SetInfoLevel(InfoRecog, lvl);
  return Size(ri) = Size(G);
end;

CheckGeneratorsInvertible := function(G)
  return ForAll(GeneratorsOfGroup(G),
              g -> not IsZero(Determinant(g)));
end;

CheckGeneratorsSpecial := function(G)
  return ForAll(GeneratorsOfGroup(G),
              g -> IsOne(Determinant(g)));
end;

# verify that forms are given and preserved
CheckBilinearForm := function(G)
  local M;
  M := InvariantBilinearForm(G).matrix;
  return ForAll(GeneratorsOfGroup(G),
              g -> g*M*TransposedMat(g) = M);
end;

CheckQuadraticForm := function(G)
  local M, Q;
  M := InvariantBilinearForm(G).matrix;
  Q := InvariantQuadraticForm(G).matrix;
  return (Q+TransposedMat(Q) = M) and
         ForAll(GeneratorsOfGroup(G),
           g -> RespectsQuadraticForm(Q, g));
end;

CheckSesquilinearForm := function(G)
  local M, F, q;
  M := InvariantSesquilinearForm(G).matrix;
  F := DefaultFieldOfMatrixGroup(G);
  q := RootInt(Size(F));
  return ForAll(GeneratorsOfGroup(G),
              g -> g*M*HermitianConjugate(g,q) = M);
end;

IsSubsetSL := function(n, q, G)
  Assert(0, DimensionOfMatrixGroup(G) = n);
  Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
  Assert(0, CheckGeneratorsSpecial(G));
  return true;
end;

IsSubsetSp := function(n, q, G)
  Assert(0, DimensionOfMatrixGroup(G) = n);
  Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
  Assert(0, CheckGeneratorsSpecial(G));
  Assert(0, CheckBilinearForm(G));
  return true;
end;

IsSubsetSU := function(n, q, G)
  Assert(0, DimensionOfMatrixGroup(G) = n);
  Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q^2));
  Assert(0, CheckGeneratorsSpecial(G));
  Assert(0, CheckSesquilinearForm(G));
  return true;
end;

IsSubsetOmega := function(epsilon, n, q, G)
  local field, invariantForm;
  field := GF(q);
  if IsEvenInt(q) then
    Assert(0, CheckQuadraticForm(G));
    invariantForm := QuadraticFormByMatrix(InvariantQuadraticForm(G).matrix, field);
  else
    Assert(0, CheckBilinearForm(G));
    invariantForm := BilinearFormByMatrix(InvariantBilinearForm(G).matrix, field);
  fi;
  if epsilon = 0 then
    Assert(0, WittIndex(invariantForm) = QuoInt(n - 1, 2));
  elif epsilon = 1 then
    Assert(0, WittIndex(invariantForm) = QuoInt(n, 2));
  elif epsilon = -1 then
    Assert(0, WittIndex(invariantForm) = QuoInt(n, 2) - 1);
  fi;
  Assert(0, DimensionOfMatrixGroup(G) = n);
  Assert(0, DefaultFieldOfMatrixGroup(G) = field);
  Assert(0, CheckGeneratorsSpecial(G));
  Assert(0, ForAll(GeneratorsOfGroup(G), g -> FancySpinorNorm(InvariantBilinearForm(G).matrix, field, g) = 1));
  return true;
end;
