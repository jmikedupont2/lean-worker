import Lean

/-!
# The trust polynomial and its lattice-window validator (user-supplied)

The declarations below are exactly as supplied, apart from the doc comments. Facts about
them are proved in `RequestProject/TrustPolynomialSpec.lean`. Real per-declaration values are
filled in by `tools/trust_capsule.py` (see `RequestProject/TrustCapsuleMeasured.lean`).
-/

namespace TrustCapsule

-- Represents the finite field bounds (GF(N) and GF(M))
structure FieldBound where
  characteristic : Nat
  orderExponent : Nat
  deriving Repr

-- The Multivariate Trust Polynomial P(C, K, B, D)
structure TrustPolynomial where
  logicalComplexity : Nat  -- C: Constants and axioms count
  kernelWeight : Nat       -- K: Kernel features / source paths touched
  binaryFootprint : Nat    -- B: Byte size from libleanshared.so symbols (nm)
  bootstrapDepth : Nat     -- D: Distance down to GNU Mes / stage0 hex
  deriving Repr

-- Evaluate the polynomial into a scalar verification weight
def evaluatePolynomial (p : TrustPolynomial) : Nat :=
  (p.logicalComplexity * 1) +
  (p.kernelWeight * 10) +
  (p.binaryFootprint / 1024) + -- scaled to KB
  (p.bootstrapDepth * 100)

-- The Full-Stack Trust Capsule for a declaration
structure Capsule where
  declName : Lean.Name
  constants : List Lean.Name
  axioms : List Lean.Name
  poly : TrustPolynomial
  lowerBound : FieldBound
  upperBound : FieldBound
  deriving Repr

-- Lattice Sandwich Validator: GF(N) < P(C,K,B,D) < GF(M)
def validateLatticeBounds (c : Capsule) : Bool :=
  let weight := evaluatePolynomial c.poly
  -- Checking that the evaluated footprint sits strictly between field orders
  c.lowerBound.orderExponent < weight && weight < c.upperBound.orderExponent

end TrustCapsule
