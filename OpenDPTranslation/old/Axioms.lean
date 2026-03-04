import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations

axiom row_function_nonincreasing
    {TA M : Type} [LE TA] [HasDistance M TA] [DatasetMetric M]
    (metric : M)
    (row_function : TA → Except String TA)
    (u v : List TA)
    (output_u output_v : List TA)
    (h_deterministic : ∀ x y, row_function x = Except.ok y →
                              ∀ z, row_function x = Except.ok z → y = z)
    (h_u : u.mapM row_function = Except.ok output_u)
    (h_v : v.mapM row_function = Except.ok output_v) :
    HasDistance.distance metric output_u output_v ≤
    HasDistance.distance metric u v

instance : Number Int where
  one := 1
  max_consecutive := Int.ofNat (2^63 - 1)
  exact_int_cast := fun n =>
    if n ≤ 2^63 - 1 then Except.ok (Int.ofNat n)
    else Except.error "overflow"

instance : HasScalarDistance (AbsoluteDistance Int) Int where
  scalar_distance := fun _ x y => Int.natAbs (x - y)

instance : InfCast Int where
  inf_cast := fun n => Int.ofNat n

instance : InfMul Int where
  inf_mul := fun x y => x * y

-- Count with saturation is 1-Lipschitz (Lemma dsym-sens)
theorem count_with_saturation_stable
    (len_x len_x' : Nat)
    (output_x output_x' : Int)
    (h_x : Number.exact_int_cast (T := Int) len_x = Except.ok output_x)
    (h_x' : Number.exact_int_cast (T := Int) len_x' = Except.ok output_x') :
    HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := Int)) output_x output_x' ≤
    Int.natAbs (len_x - len_x') := by
  show Int.natAbs (output_x - output_x') ≤ Int.natAbs (len_x - len_x')
  simp only [Number.exact_int_cast] at *
  split at h_x <;> split at h_x' <;> simp_all <;> omega

-- Length difference bounded by symmetric distance (Lemma len-sum-equiv)
axiom length_bounded_by_symmetric_distance
    {TIA : Type} [HasDistance SymmetricDistance TIA]
    (metric : SymmetricDistance)
    (x x' : List TIA) :
    Int.natAbs (x.length - x'.length) ≤ HasDistance.distance metric x x'

def lpDistance {T Q : Type}
    [HasScalarDistance (AbsoluteDistance Q) T]
    (x y : List T) : Nat :=
  match x, y with
  | [a], [b] => HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := Q)) a b
  | _, _     => 0

instance [HasScalarDistance (AbsoluteDistance Q) T] :
    HasDistance (LpDistance T Q) T where
  distance := fun _ x y => lpDistance (Q := Q) x y

-- Lp distance on singletons equals absolute distance
theorem lp_singleton_equals_absolute
    {T Q : Type} [Number T] [Number Q]
    [HasScalarDistance (AbsoluteDistance Q) T]
    (metric : AbsoluteDistance Q)
    (x x' : T) :
    HasDistance.distance (LpDistance.mk (P := T) (Q := Q)) [x] [x'] =
    HasScalarDistance.scalar_distance metric x x' := by
  simp [HasDistance.distance, lpDistance]
