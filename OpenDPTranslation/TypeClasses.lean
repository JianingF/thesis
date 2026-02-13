class ProductOrd (TA : Type) [LE TA] [DecidableRel (α := TA) (· ≤ ·)] where
  total_clamp : TA → TA → TA → TA
  total_clamp_in_bounds : ∀ (value lower upper : TA),
    lower ≤ upper →
    lower ≤ total_clamp value lower upper ∧
    total_clamp value lower upper ≤ upper

class Primitive (T : Type) where

class Number (T : Type) where
  one : T
  max_consecutive : T
  exact_int_cast : Nat → Except String T

class InfCast (T : Type) [Number T] where
  inf_cast : Nat → T

class InfMul (T : Type) [Number T] where
  inf_mul : T → T → T

class PartialEq (T : Type) where
  eq : T → T → Bool

class DatasetMetric (M : Type) where
  dummy : M → M

class HasDistance (M : Type) (T : Type) where
  distance : M → List T → List T → Nat

class HasScalarDistance (M : Type) (T : Type) where
  scalar_distance : M → T → T → Nat

class MetricSpace (Domain : Type) (M : Type) where

inductive SymmetricDistance where
  | mk : SymmetricDistance

inductive AbsoluteDistance (T : Type) where
  | mk : AbsoluteDistance T

inductive LpDistance (P Q : Type) where
  | mk : LpDistance P Q

def stability_map_identity (d_in : Nat) : Nat := d_in
