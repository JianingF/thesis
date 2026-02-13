import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations

-- Row functions cannot increase dataset distance (Lemma f-sim)
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

-- Count with saturation is 1-Lipschitz (Lemma dsym-sens)
axiom count_with_saturation_stable
    {TO : Type} [Number TO] [HasScalarDistance (AbsoluteDistance TO) TO]
    (len_x len_x' : Nat)
    (output_x output_x' : TO)
    (h_x : output_x = match Number.exact_int_cast len_x with
                      | Except.ok n => n
                      | Except.error _ => Number.max_consecutive)
    (h_x' : output_x' = match Number.exact_int_cast len_x' with
                        | Except.ok n => n
                        | Except.error _ => Number.max_consecutive) :
    HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := TO)) output_x output_x' ≤
    Int.natAbs (len_x - len_x')

-- Length difference bounded by symmetric distance (Lemma len-sum-equiv)
axiom length_bounded_by_symmetric_distance
    {TIA : Type} [HasDistance SymmetricDistance TIA]
    (metric : SymmetricDistance)
    (x x' : List TIA) :
    Int.natAbs (x.length - x'.length) ≤ HasDistance.distance metric x x'

-- Lp distance on singletons equals absolute distance
axiom lp_singleton_equals_absolute
    {T Q : Type} [Number T] [Number Q]
    [HasScalarDistance (AbsoluteDistance Q) T]
    [HasDistance (LpDistance T Q) T]
    (metric : AbsoluteDistance Q)
    (x x' : T) :
    HasDistance.distance (LpDistance.mk (P := T) (Q := Q)) [x] [x'] =
    HasScalarDistance.scalar_distance metric x x'
