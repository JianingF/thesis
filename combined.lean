-- ============================================================================
-- Type Classes
-- ============================================================================

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

-- ============================================================================
-- Metrics
-- ============================================================================

inductive SymmetricDistance where
  | mk : SymmetricDistance

inductive AbsoluteDistance (T : Type) where
  | mk : AbsoluteDistance T

inductive LpDistance (P Q : Type) where
  | mk : LpDistance P Q

def stability_map_identity (d_in : Nat) : Nat := d_in

-- ============================================================================
-- Domains
-- ============================================================================

structure Bounds (TA : Type) [LE TA] where
  lower : TA
  upper : TA
  valid : lower ≤ upper

namespace Bounds
  def new_closed {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) : Except String (Bounds TA) :=
    if h : bounds.1 ≤ bounds.2 then
      Except.ok ⟨bounds.1, bounds.2, h⟩
    else
      Except.error "Invalid bounds: lower must be ≤ upper"

  theorem new_closed_valid {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) (b : Bounds TA) :
      new_closed bounds = Except.ok b → bounds.1 ≤ bounds.2 := by
    intro h
    simp [new_closed] at h
    split at h
    · case isTrue h_le => exact h_le
    · case isFalse => contradiction

  theorem new_closed_lower {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) (b : Bounds TA) :
      new_closed bounds = Except.ok b → b.lower = bounds.1 := by
    intro h
    simp [new_closed] at h
    split at h
    · case isTrue h_le => cases h; rfl
    · case isFalse => contradiction

  theorem new_closed_upper {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) (b : Bounds TA) :
      new_closed bounds = Except.ok b → b.upper = bounds.2 := by
    intro h
    simp [new_closed] at h
    split at h
    · case isTrue h_le => cases h; rfl
    · case isFalse => contradiction
end Bounds

structure AtomDomain (TA : Type) [LE TA] where
  bounds : Option (Bounds TA)
  is_non_null : Bool

namespace AtomDomain
  def contains {TA : Type} [LE TA] (domain : AtomDomain TA) (value : TA) : Prop :=
    match domain.bounds with
    | none => domain.is_non_null = true
    | some b => domain.is_non_null = true ∧ b.lower ≤ value ∧ value ≤ b.upper

  def default {TA : Type} [LE TA] : AtomDomain TA :=
    { bounds := none, is_non_null := true }
end AtomDomain

structure VectorDomain (RowDomain : Type) where
  element_domain : RowDomain

-- ============================================================================
-- Transformation Structures
-- ============================================================================

structure Transformation (InputRowType OutputType : Type) [LE InputRowType] [LE OutputType] where
  input_domain : VectorDomain (AtomDomain InputRowType)
  output_domain : AtomDomain OutputType
  apply : List InputRowType → Except String OutputType

structure RowByRowTransformation (TA : Type) [LE TA] where
  input_domain : VectorDomain (AtomDomain TA)
  output_domain : AtomDomain TA
  apply : List TA → Except String (List TA)

structure RowByRowTransformationCross (TIA TOA : Type) [LE TIA] [LE TOA] where
  input_domain : VectorDomain (AtomDomain TIA)
  output_domain : AtomDomain TOA
  apply : List TIA → Except String (List TOA)

structure ScalarToVectorTransformation (T : Type) [LE T] where
  input_domain : AtomDomain T
  output_domain : VectorDomain (AtomDomain T)
  apply : T → Except String (List T)

-- ============================================================================
-- Validity Predicates
-- ============================================================================

def is_valid_row_by_row_transformation
    {TA : Type} [LE TA]
    (input_domain : VectorDomain (AtomDomain TA))
    (bounds : TA × TA)
    (t : RowByRowTransformation TA) : Prop :=
  ∀ (input : List TA),
    (∀ v ∈ input, input_domain.element_domain.contains v) →
    ∃ (output : List TA),
      t.apply input = Except.ok output ∧
      (∀ v ∈ output, t.output_domain.contains v)

def is_valid_transformation_count
    {TIA TO : Type} [LE TIA] [LE TO]
    (input_domain : VectorDomain (AtomDomain TIA))
    (t : Transformation TIA TO) : Prop :=
  ∀ (input : List TIA),
    (∀ v ∈ input, input_domain.element_domain.contains v) →
    ∃ (output : TO),
      t.apply input = Except.ok output ∧
      t.output_domain.contains output

def is_valid_scalar_to_vector_transformation
    {T : Type} [LE T]
    (input_domain : AtomDomain T)
    (t : ScalarToVectorTransformation T) : Prop :=
  ∀ (input : T),
    input_domain.contains input →
    ∃ (output : List T),
      t.apply input = Except.ok output ∧
      output.length = 1 ∧
      (∀ v ∈ output, t.output_domain.element_domain.contains v)

def is_valid_row_by_row_cross_transformation
    {TIA TOA : Type} [LE TIA] [LE TOA]
    (input_domain : VectorDomain (AtomDomain TIA))
    (t : RowByRowTransformationCross TIA TOA) : Prop :=
  ∀ (input : List TIA),
    (∀ v ∈ input, input_domain.element_domain.contains v) →
    ∃ (output : List TOA),
      t.apply input = Except.ok output ∧
      (∀ v ∈ output, t.output_domain.contains v)

-- ============================================================================
-- Core Axioms
-- ============================================================================

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

-- ============================================================================
-- make_row_by_row_fallible
-- ============================================================================

def make_row_by_row_fallible
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → Except String TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      ∀ result, row_function value = Except.ok result →
      output_row_domain.contains result) :
    RowByRowTransformation TA :=
  { input_domain := input_domain
    output_domain := output_row_domain
    apply := fun values => values.mapM row_function }

theorem make_row_by_row_fallible_correct
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → Except String TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      ∀ result, row_function value = Except.ok result →
      output_row_domain.contains result)
    (input : List TA)
    (h_input_valid : ∀ v ∈ input, input_domain.element_domain.contains v)
    (h_all_succeed : ∀ v ∈ input, ∃ result, row_function v = Except.ok result) :
    let t := make_row_by_row_fallible input_domain input_metric output_row_domain row_function h_preserves
    ∃ output, t.apply input = Except.ok output ∧
              ∀ v ∈ output, output_row_domain.contains v := by
  simp only [make_row_by_row_fallible]
  induction input with
  | nil =>
    exists []
    constructor
    · rfl
    · intro v h_v; simp at h_v
  | cons head tail ih =>
    have h_head_succ := h_all_succeed head (by simp)
    obtain ⟨result_head, h_result_head⟩ := h_head_succ
    have h_tail_valid : ∀ v ∈ tail, input_domain.element_domain.contains v := by
      intro v h_v; apply h_input_valid; simp [h_v]
    have h_tail_succeed : ∀ v ∈ tail, ∃ result, row_function v = Except.ok result := by
      intro v h_v; apply h_all_succeed; simp [h_v]
    obtain ⟨output_tail, h_tail_eq, h_tail_contains⟩ := ih h_tail_valid h_tail_succeed
    exists (result_head :: output_tail)
    constructor
    · show List.mapM row_function (head :: tail) = Except.ok (result_head :: output_tail)
      rw [List.mapM_cons, h_result_head, h_tail_eq]; rfl
    · intro v h_v_in
      simp [List.mem_cons] at h_v_in
      cases h_v_in with
      | inl h_eq =>
        rw [h_eq]
        apply h_preserves head
        · apply h_input_valid; simp
        · exact h_result_head
      | inr h_in_tail =>
        exact h_tail_contains v h_in_tail

theorem make_row_by_row_fallible_stable
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
    [DatasetMetric M] [HasDistance M TA]
    [MetricSpace (VectorDomain (AtomDomain TA)) M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → Except String TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      ∀ result, row_function value = Except.ok result →
      output_row_domain.contains result)
    (h_deterministic : ∀ x y, row_function x = Except.ok y →
                              ∀ z, row_function x = Except.ok z → y = z) :
    ∀ (u v : List TA) (d_in d_out : Nat),
      (∀ x ∈ u, input_domain.element_domain.contains x) →
      (∀ x ∈ v, input_domain.element_domain.contains x) →
      (∀ x ∈ u, ∃ result, row_function x = Except.ok result) →
      (∀ x ∈ v, ∃ result, row_function x = Except.ok result) →
      HasDistance.distance input_metric u v ≤ d_in →
      stability_map_identity d_in ≤ d_out →
      let t := make_row_by_row_fallible input_domain input_metric output_row_domain
                                        row_function h_preserves
      ∃ (output_u output_v : List TA),
        t.apply u = Except.ok output_u ∧
        t.apply v = Except.ok output_v ∧
        HasDistance.distance input_metric output_u output_v ≤ d_out := by
  intro u v d_in d_out h_u_valid h_v_valid h_u_succeed h_v_succeed h_close h_stability
  intro t
  have h_u_result := make_row_by_row_fallible_correct
    input_domain input_metric output_row_domain row_function h_preserves
    u h_u_valid h_u_succeed
  have h_v_result := make_row_by_row_fallible_correct
    input_domain input_metric output_row_domain row_function h_preserves
    v h_v_valid h_v_succeed
  obtain ⟨output_u, h_u_apply, h_u_contains⟩ := h_u_result
  obtain ⟨output_v, h_v_apply, h_v_contains⟩ := h_v_result
  exists output_u, output_v
  constructor
  · exact h_u_apply
  constructor
  · exact h_v_apply
  · unfold make_row_by_row_fallible at h_u_apply h_v_apply
    simp only at h_u_apply h_v_apply
    have h_u_mapM : u.mapM row_function = Except.ok output_u := by
      cases h_u_eq : u.mapM row_function
      · simp [h_u_eq] at h_u_apply
      · simp [h_u_eq] at h_u_apply; cases h_u_apply; rfl
    have h_v_mapM : v.mapM row_function = Except.ok output_v := by
      cases h_v_eq : v.mapM row_function
      · simp [h_v_eq] at h_v_apply
      · simp [h_v_eq] at h_v_apply; cases h_v_apply; rfl
    have h_dist_nonincreasing := row_function_nonincreasing
      input_metric row_function u v output_u output_v h_deterministic
      h_u_mapM h_v_mapM
    calc HasDistance.distance input_metric output_u output_v
        ≤ HasDistance.distance input_metric u v := h_dist_nonincreasing
      _ ≤ d_in := h_close
      _ = stability_map_identity d_in := rfl
      _ ≤ d_out := h_stability

theorem make_row_by_row_fallible_sound
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
    [DatasetMetric M] [HasDistance M TA]
    [MetricSpace (VectorDomain (AtomDomain TA)) M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → Except String TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      ∀ result, row_function value = Except.ok result →
      output_row_domain.contains result)
    (h_deterministic : ∀ x y, row_function x = Except.ok y →
                              ∀ z, row_function x = Except.ok z → y = z) :
    let t := make_row_by_row_fallible input_domain input_metric output_row_domain row_function h_preserves
    (∀ (input : List TA),
      (∀ v ∈ input, input_domain.element_domain.contains v) →
      (∀ v ∈ input, ∃ result, row_function v = Except.ok result) →
      ∃ output, t.apply input = Except.ok output ∧
                ∀ v ∈ output, output_row_domain.contains v) ∧
    (∀ (u v : List TA) (d_in d_out : Nat),
      (∀ x ∈ u, input_domain.element_domain.contains x) →
      (∀ x ∈ v, input_domain.element_domain.contains x) →
      (∀ x ∈ u, ∃ result, row_function x = Except.ok result) →
      (∀ x ∈ v, ∃ result, row_function x = Except.ok result) →
      HasDistance.distance input_metric u v ≤ d_in →
      stability_map_identity d_in ≤ d_out →
      ∃ (output_u output_v : List TA),
        t.apply u = Except.ok output_u ∧
        t.apply v = Except.ok output_v ∧
        HasDistance.distance input_metric output_u output_v ≤ d_out) := by
  intro t
  constructor
  · exact fun input h_valid h_succeed =>
      make_row_by_row_fallible_correct input_domain input_metric output_row_domain
        row_function h_preserves input h_valid h_succeed
  · exact make_row_by_row_fallible_stable input_domain input_metric output_row_domain
      row_function h_preserves h_deterministic

-- ============================================================================
-- make_row_by_row (infallible wrapper)
-- ============================================================================

def make_row_by_row
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      output_row_domain.contains (row_function value)) :
    RowByRowTransformation TA :=
  let fallible_function (x : TA) : Except String TA := Except.ok (row_function x)
  have h_preserves_fallible : ∀ value,
      input_domain.element_domain.contains value →
      ∀ result, fallible_function value = Except.ok result →
      output_row_domain.contains result := by
    intro value h_in result h_eq
    simp [fallible_function] at h_eq
    cases h_eq
    exact h_preserves value h_in
  make_row_by_row_fallible input_domain input_metric output_row_domain
    fallible_function h_preserves_fallible

theorem make_row_by_row_correct
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      output_row_domain.contains (row_function value))
    (input : List TA)
    (h_input_valid : ∀ v ∈ input, input_domain.element_domain.contains v) :
    let t := make_row_by_row input_domain input_metric output_row_domain row_function h_preserves
    ∃ output, t.apply input = Except.ok output ∧
              ∀ v ∈ output, output_row_domain.contains v := by
  simp only [make_row_by_row]
  let fallible_f : TA → Except String TA := fun x => Except.ok (row_function x)
  have h_all_succeed : ∀ v ∈ input, ∃ result, fallible_f v = Except.ok result := by
    intro v h_v_in; exists (row_function v)
  have h_preserves_fallible : ∀ value,
      input_domain.element_domain.contains value →
      ∀ result, fallible_f value = Except.ok result →
      output_row_domain.contains result := by
    intro value h_in result h_eq
    simp [fallible_f] at h_eq; cases h_eq
    exact h_preserves value h_in
  exact make_row_by_row_fallible_correct
    input_domain input_metric output_row_domain
    fallible_f h_preserves_fallible
    input h_input_valid h_all_succeed

theorem make_row_by_row_stable
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
    [DatasetMetric M] [HasDistance M TA]
    [MetricSpace (VectorDomain (AtomDomain TA)) M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      output_row_domain.contains (row_function value)) :
    ∀ (u v : List TA) (d_in d_out : Nat),
      (∀ x ∈ u, input_domain.element_domain.contains x) →
      (∀ x ∈ v, input_domain.element_domain.contains x) →
      HasDistance.distance input_metric u v ≤ d_in →
      stability_map_identity d_in ≤ d_out →
      let t := make_row_by_row input_domain input_metric output_row_domain row_function h_preserves
      ∃ (output_u output_v : List TA),
        t.apply u = Except.ok output_u ∧
        t.apply v = Except.ok output_v ∧
        HasDistance.distance input_metric output_u output_v ≤ d_out := by
  intro u v d_in d_out h_u_valid h_v_valid h_close h_stability
  let fallible_f : TA → Except String TA := fun x => Except.ok (row_function x)
  have h_deterministic : ∀ x y, fallible_f x = Except.ok y →
                                ∀ z, fallible_f x = Except.ok z → y = z := by
    intro x y h_y z h_z
    simp [fallible_f] at h_y h_z; cases h_y; cases h_z; rfl
  have h_u_succeed : ∀ x ∈ u, ∃ result, fallible_f x = Except.ok result := by
    intro x h_x; exists (row_function x)
  have h_v_succeed : ∀ x ∈ v, ∃ result, fallible_f x = Except.ok result := by
    intro x h_x; exists (row_function x)
  have h_preserves_fallible : ∀ value,
      input_domain.element_domain.contains value →
      ∀ result, fallible_f value = Except.ok result →
      output_row_domain.contains result := by
    intro value h_in result h_eq
    simp [fallible_f] at h_eq; cases h_eq
    exact h_preserves value h_in
  show ∃ (output_u output_v : List TA),
        (make_row_by_row input_domain input_metric output_row_domain row_function h_preserves).apply u = Except.ok output_u ∧
        (make_row_by_row input_domain input_metric output_row_domain row_function h_preserves).apply v = Except.ok output_v ∧
        HasDistance.distance input_metric output_u output_v ≤ d_out
  have h_eq_u : (make_row_by_row input_domain input_metric output_row_domain row_function h_preserves).apply u =
                (make_row_by_row_fallible input_domain input_metric output_row_domain fallible_f h_preserves_fallible).apply u := by
    rfl
  have h_eq_v : (make_row_by_row input_domain input_metric output_row_domain row_function h_preserves).apply v =
                (make_row_by_row_fallible input_domain input_metric output_row_domain fallible_f h_preserves_fallible).apply v := by
    rfl
  rw [h_eq_u, h_eq_v]
  exact make_row_by_row_fallible_stable
    input_domain input_metric output_row_domain
    fallible_f h_preserves_fallible h_deterministic
    u v d_in d_out h_u_valid h_v_valid h_u_succeed h_v_succeed h_close h_stability

theorem make_row_by_row_sound
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
    [DatasetMetric M] [HasDistance M TA]
    [MetricSpace (VectorDomain (AtomDomain TA)) M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (output_row_domain : AtomDomain TA)
    (row_function : TA → TA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      output_row_domain.contains (row_function value)) :
    let t := make_row_by_row input_domain input_metric output_row_domain row_function h_preserves
    (∀ (input : List TA),
      (∀ v ∈ input, input_domain.element_domain.contains v) →
      ∃ output, t.apply input = Except.ok output ∧
                ∀ v ∈ output, output_row_domain.contains v) ∧
    (∀ (u v : List TA) (d_in d_out : Nat),
      (∀ x ∈ u, input_domain.element_domain.contains x) →
      (∀ x ∈ v, input_domain.element_domain.contains x) →
      HasDistance.distance input_metric u v ≤ d_in →
      stability_map_identity d_in ≤ d_out →
      ∃ (output_u output_v : List TA),
        t.apply u = Except.ok output_u ∧
        t.apply v = Except.ok output_v ∧
        HasDistance.distance input_metric output_u output_v ≤ d_out) := by
  intro t
  constructor
  · exact fun input h_valid =>
      make_row_by_row_correct input_domain input_metric output_row_domain
        row_function h_preserves input h_valid
  · exact make_row_by_row_stable input_domain input_metric output_row_domain
      row_function h_preserves

-- ============================================================================
-- make_row_by_row_cross (type-changing row transformation)
-- ============================================================================

def make_row_by_row_cross
    {TIA TOA M : Type} [LE TIA] [LE TOA]
    [DecidableRel (α := TIA) (· ≤ ·)] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : M)
    (output_row_domain : AtomDomain TOA)
    (row_function : TIA → TOA)
    (h_preserves : ∀ value,
      input_domain.element_domain.contains value →
      output_row_domain.contains (row_function value)) :
    RowByRowTransformationCross TIA TOA :=
  { input_domain := input_domain
    output_domain := output_row_domain
    apply := fun values => Except.ok (values.map row_function) }

-- ============================================================================
-- make_clamp
-- ============================================================================

def make_clamp
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
    [ProductOrd TA] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (bounds : TA × TA)
    (h_input_non_null : input_domain.element_domain.is_non_null = true) :
    Except String (RowByRowTransformation TA) :=
  match h : Bounds.new_closed bounds with
  | Except.error e => Except.error e
  | Except.ok bounds_obj =>
    let output_row_domain : AtomDomain TA := {
      bounds := some bounds_obj,
      is_non_null := true
    }
    let clamper (value : TA) : TA :=
      ProductOrd.total_clamp value bounds.1 bounds.2
    have h_lower_eq : bounds_obj.lower = bounds.1 :=
      Bounds.new_closed_lower bounds bounds_obj h
    have h_upper_eq : bounds_obj.upper = bounds.2 :=
      Bounds.new_closed_upper bounds bounds_obj h
    have h_bounds_valid : bounds.1 ≤ bounds.2 :=
      Bounds.new_closed_valid bounds bounds_obj h
    have h_clamper_preserves : ∀ value,
        input_domain.element_domain.contains value →
        output_row_domain.contains (clamper value) := by
      intro value h_value_in_domain
      show output_row_domain.is_non_null = true ∧
           bounds_obj.lower ≤ clamper value ∧
           clamper value ≤ bounds_obj.upper
      constructor
      · show true = true; rfl
      constructor
      · show bounds_obj.lower ≤ ProductOrd.total_clamp value bounds.1 bounds.2
        rw [h_lower_eq]
        exact (ProductOrd.total_clamp_in_bounds value bounds.1 bounds.2 h_bounds_valid).1
      · show ProductOrd.total_clamp value bounds.1 bounds.2 ≤ bounds_obj.upper
        rw [h_upper_eq]
        exact (ProductOrd.total_clamp_in_bounds value bounds.1 bounds.2 h_bounds_valid).2
    Except.ok (make_row_by_row input_domain input_metric output_row_domain clamper h_clamper_preserves)

theorem make_clamp_output_in_domain
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
    [ProductOrd TA] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (bounds : TA × TA)
    (h_input_non_null : input_domain.element_domain.is_non_null = true)
    (bounds_obj : Bounds TA)
    (h_bounds : Bounds.new_closed bounds = Except.ok bounds_obj)
    (input : List TA)
    (h_input_valid : ∀ v ∈ input, input_domain.element_domain.contains v) :
    let t := make_row_by_row input_domain input_metric
              (AtomDomain.mk (some bounds_obj) true)
              (fun value => ProductOrd.total_clamp value bounds.1 bounds.2)
              (by intro value h_value_in
                  unfold AtomDomain.contains
                  simp only
                  constructor
                  · trivial
                  constructor
                  · rw [Bounds.new_closed_lower bounds bounds_obj h_bounds]
                    exact (ProductOrd.total_clamp_in_bounds value bounds.1 bounds.2
                           (Bounds.new_closed_valid bounds bounds_obj h_bounds)).1
                  · rw [Bounds.new_closed_upper bounds bounds_obj h_bounds]
                    exact (ProductOrd.total_clamp_in_bounds value bounds.1 bounds.2
                           (Bounds.new_closed_valid bounds bounds_obj h_bounds)).2)
    ∃ output, t.apply input = Except.ok output ∧
              ∀ v ∈ output, t.output_domain.contains v := by
  exact make_row_by_row_correct
    input_domain input_metric
    (AtomDomain.mk (some bounds_obj) true)
    (fun value => ProductOrd.total_clamp value bounds.1 bounds.2)
    _
    input h_input_valid

theorem make_clamp_correct
    {TA M : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
    [ProductOrd TA] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TA))
    (input_metric : M)
    (bounds : TA × TA)
    (h_input_non_null : input_domain.element_domain.is_non_null = true)
    (t : RowByRowTransformation TA)
    (h_result : make_clamp input_domain input_metric bounds h_input_non_null = Except.ok t) :
    is_valid_row_by_row_transformation input_domain bounds t := by
  unfold is_valid_row_by_row_transformation
  intro input h_input_valid
  unfold make_clamp at h_result
  split at h_result
  · contradiction
  · rename_i bounds_obj h_bounds
    cases h_result
    exact make_clamp_output_in_domain input_domain input_metric bounds h_input_non_null
                                      bounds_obj h_bounds input h_input_valid

-- ============================================================================
-- make_count
-- ============================================================================

def make_count
    {TIA TO : Type} [LE TIA] [LE TO]
    [Primitive TIA] [Number TO] [InfCast TO] [InfMul TO]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance) :
    Transformation TIA TO :=
  let function (arg : List TIA) : Except String TO :=
    let size := arg.length
    match Number.exact_int_cast size with
    | Except.ok result => Except.ok result
    | Except.error _ => Except.ok Number.max_consecutive
  { input_domain := input_domain
    output_domain := AtomDomain.default
    apply := function }

theorem make_count_output_in_domain
    {TIA TO : Type} [LE TIA] [LE TO]
    [Primitive TIA] [Number TO] [InfCast TO] [InfMul TO]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance)
    (input : List TIA)
    (h_input_valid : ∀ v ∈ input, input_domain.element_domain.contains v) :
    let t := make_count input_domain input_metric
    ∃ (output : TO),
      t.apply input = Except.ok output ∧
      t.output_domain.contains output := by
  show ∃ (output : TO),
    (match Number.exact_int_cast input.length with
     | Except.ok result => Except.ok result
     | Except.error _ => Except.ok Number.max_consecutive) = Except.ok output ∧
    AtomDomain.default.contains output
  split
  · rename_i result h_cast; exists result
  · exists Number.max_consecutive

theorem make_count_correct
    {TIA TO : Type} [LE TIA] [LE TO]
    [Primitive TIA] [Number TO] [InfCast TO] [InfMul TO]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance) :
    is_valid_transformation_count input_domain (make_count (TO := TO) input_domain input_metric) := by
  unfold is_valid_transformation_count
  intro input h_input_valid
  exact make_count_output_in_domain input_domain input_metric input h_input_valid

theorem make_count_stable
    {TIA TO : Type} [LE TIA] [LE TO]
    [Primitive TIA] [Number TO] [InfCast TO] [InfMul TO]
    [HasDistance SymmetricDistance TIA]
    [HasScalarDistance (AbsoluteDistance TO) TO]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance) :
    ∀ (x x' : List TIA) (d_in : Nat) (d_out : Nat),
      (∀ v ∈ x, input_domain.element_domain.contains v) →
      (∀ v ∈ x', input_domain.element_domain.contains v) →
      HasDistance.distance input_metric x x' ≤ d_in →
      d_in ≤ d_out →
      let t := make_count input_domain input_metric
      ∃ (output_x output_x' : TO),
        t.apply x = Except.ok output_x ∧
        t.apply x' = Except.ok output_x' ∧
        HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := TO)) output_x output_x' ≤ d_out := by
  intro x x' d_in d_out h_x_valid h_x'_valid h_close h_stability
  intro t
  have h_x_result := make_count_output_in_domain (TO := TO) input_domain input_metric x h_x_valid
  have h_x'_result := make_count_output_in_domain (TO := TO) input_domain input_metric x' h_x'_valid
  obtain ⟨output_x, h_x_apply, h_x_in_domain⟩ := h_x_result
  obtain ⟨output_x', h_x'_apply, h_x'_in_domain⟩ := h_x'_result
  exists output_x, output_x'
  constructor
  · exact h_x_apply
  constructor
  · exact h_x'_apply
  · have h_distance_bound :
      HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := TO)) output_x output_x' ≤ d_in := by
      unfold make_count at h_x_apply h_x'_apply
      simp only at h_x_apply h_x'_apply
      have h_output_x_def : output_x = match Number.exact_int_cast (T := TO) x.length with
                                        | Except.ok n => n
                                        | Except.error _ => Number.max_consecutive := by
        cases h_cast : Number.exact_int_cast (T := TO) x.length with
        | ok n => simp only [h_cast] at h_x_apply; cases h_x_apply; rfl
        | error e => simp only [h_cast] at h_x_apply; cases h_x_apply; rfl
      have h_output_x'_def : output_x' = match Number.exact_int_cast (T := TO) x'.length with
                                          | Except.ok n => n
                                          | Except.error _ => Number.max_consecutive := by
        cases h_cast : Number.exact_int_cast (T := TO) x'.length with
        | ok n => simp only [h_cast] at h_x'_apply; cases h_x'_apply; rfl
        | error e => simp only [h_cast] at h_x'_apply; cases h_x'_apply; rfl
      have h_saturation := count_with_saturation_stable x.length x'.length output_x output_x'
                                                        h_output_x_def h_output_x'_def
      have h_length_bound := length_bounded_by_symmetric_distance input_metric x x'
      calc HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := TO)) output_x output_x'
          ≤ Int.natAbs (x.length - x'.length) := h_saturation
        _ ≤ HasDistance.distance input_metric x x' := h_length_bound
        _ ≤ d_in := h_close
    calc HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := TO)) output_x output_x'
        ≤ d_in := h_distance_bound
      _ ≤ d_out := h_stability

theorem make_count_sound
    {TIA TO : Type} [LE TIA] [LE TO]
    [Primitive TIA] [Number TO] [InfCast TO] [InfMul TO]
    [HasDistance SymmetricDistance TIA]
    [HasScalarDistance (AbsoluteDistance TO) TO]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance) :
    let t := make_count (TO := TO) input_domain input_metric
    (∀ (input : List TIA),
      (∀ v ∈ input, input_domain.element_domain.contains v) →
      ∃ output, t.apply input = Except.ok output ∧
                t.output_domain.contains output) ∧
    (∀ (x x' : List TIA) (d_in d_out : Nat),
      (∀ v ∈ x, input_domain.element_domain.contains v) →
      (∀ v ∈ x', input_domain.element_domain.contains v) →
      HasDistance.distance input_metric x x' ≤ d_in →
      d_in ≤ d_out →
      ∃ (output_x output_x' : TO),
        t.apply x = Except.ok output_x ∧
        t.apply x' = Except.ok output_x' ∧
        HasScalarDistance.scalar_distance (AbsoluteDistance.mk (T := TO)) output_x output_x' ≤ d_out) := by
  intro t
  constructor
  · exact fun input h_valid =>
      make_count_output_in_domain input_domain input_metric input h_valid
  · exact make_count_stable input_domain input_metric

-- ============================================================================
-- make_vec
-- ============================================================================

def make_vec
    {T Q : Type} [LE T] [Number T] [Number Q]
    (input_domain : AtomDomain T)
    (input_metric : AbsoluteDistance Q) :
    ScalarToVectorTransformation T :=
  { input_domain := input_domain
    output_domain := VectorDomain.mk input_domain
    apply := fun arg => Except.ok [arg] }

theorem make_vec_output_valid
    {T Q : Type} [LE T] [Number T] [Number Q]
    (input_domain : AtomDomain T)
    (input_metric : AbsoluteDistance Q)
    (input : T)
    (h_input_valid : input_domain.contains input) :
    let t := make_vec input_domain input_metric
    ∃ (output : List T),
      t.apply input = Except.ok output ∧
      output.length = 1 ∧
      (∀ v ∈ output, t.output_domain.element_domain.contains v) := by
  exists [input]
  constructor
  · rfl
  constructor
  · rfl
  · intro v h_v_in_output
    simp only [List.mem_singleton] at h_v_in_output
    rw [h_v_in_output]
    exact h_input_valid

theorem make_vec_correct
    {T Q : Type} [LE T] [Number T] [Number Q]
    (input_domain : AtomDomain T)
    (input_metric : AbsoluteDistance Q) :
    is_valid_scalar_to_vector_transformation input_domain (make_vec input_domain input_metric) := by
  unfold is_valid_scalar_to_vector_transformation
  intro input h_input_valid
  exact make_vec_output_valid input_domain input_metric input h_input_valid

theorem make_vec_stable
    {T Q : Type} [LE T] [Number T] [Number Q]
    [HasScalarDistance (AbsoluteDistance Q) T]
    [HasDistance (LpDistance T Q) T]
    (input_domain : AtomDomain T)
    (input_metric : AbsoluteDistance Q) :
    ∀ (x x' : T) (d_in d_out : Nat),
      input_domain.contains x →
      input_domain.contains x' →
      HasScalarDistance.scalar_distance input_metric x x' ≤ d_in →
      d_in ≤ d_out →
      let t := make_vec input_domain input_metric
      ∃ (output_x output_x' : List T),
        t.apply x = Except.ok output_x ∧
        t.apply x' = Except.ok output_x' ∧
        HasDistance.distance (LpDistance.mk (P := T) (Q := Q)) output_x output_x' ≤ d_out := by
  intro x x' d_in d_out h_x_valid h_x'_valid h_close h_stability
  intro t
  have h_x_result := make_vec_output_valid input_domain input_metric x h_x_valid
  have h_x'_result := make_vec_output_valid input_domain input_metric x' h_x'_valid
  obtain ⟨output_x, h_x_apply, h_x_len, h_x_in_domain⟩ := h_x_result
  obtain ⟨output_x', h_x'_apply, h_x'_len, h_x'_in_domain⟩ := h_x'_result
  exists output_x, output_x'
  constructor
  · exact h_x_apply
  constructor
  · exact h_x'_apply
  · have h_singleton_distance :
          HasDistance.distance (LpDistance.mk (P := T) (Q := Q)) output_x output_x' =
          HasScalarDistance.scalar_distance input_metric x x' := by
          unfold make_vec at h_x_apply h_x'_apply
          simp only at h_x_apply h_x'_apply
          cases h_x_apply; cases h_x'_apply
          exact lp_singleton_equals_absolute input_metric x x'
    calc HasDistance.distance (LpDistance.mk (P := T) (Q := Q)) output_x output_x'
        = HasScalarDistance.scalar_distance input_metric x x' := h_singleton_distance
      _ ≤ d_in := h_close
      _ ≤ d_out := h_stability

theorem make_vec_sound
    {T Q : Type} [LE T] [Number T] [Number Q]
    [HasScalarDistance (AbsoluteDistance Q) T]
    [HasDistance (LpDistance T Q) T]
    (input_domain : AtomDomain T)
    (input_metric : AbsoluteDistance Q) :
    let t := make_vec input_domain input_metric
    (∀ (input : T),
      input_domain.contains input →
      ∃ output, t.apply input = Except.ok output ∧
                output.length = 1 ∧
                ∀ v ∈ output, t.output_domain.element_domain.contains v) ∧
    (∀ (x x' : T) (d_in d_out : Nat),
      input_domain.contains x →
      input_domain.contains x' →
      HasScalarDistance.scalar_distance input_metric x x' ≤ d_in →
      d_in ≤ d_out →
      ∃ (output_x output_x' : List T),
        t.apply x = Except.ok output_x ∧
        t.apply x' = Except.ok output_x' ∧
        HasDistance.distance (LpDistance.mk (P := T) (Q := Q)) output_x output_x' ≤ d_out) := by
  intro t
  constructor
  · exact fun input h_valid =>
      make_vec_output_valid input_domain input_metric input h_valid
  · exact make_vec_stable input_domain input_metric

-- ============================================================================
-- make_is_equal
-- ============================================================================

def make_is_equal
    {TIA M : Type} [LE TIA] [DecidableRel (α := TIA) (· ≤ ·)]
    [PartialEq TIA] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : M)
    (value : TIA) :
    RowByRowTransformationCross TIA Bool :=
  { input_domain := input_domain
    output_domain := AtomDomain.default
    apply := fun values => Except.ok (values.map (PartialEq.eq value)) }

theorem make_is_equal_correct
    {TIA M : Type} [LE TIA] [DecidableRel (α := TIA) (· ≤ ·)]
    [PartialEq TIA] [DatasetMetric M]
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : M)
    (value : TIA) :
    is_valid_row_by_row_cross_transformation input_domain
      (make_is_equal input_domain input_metric value) := by
  unfold is_valid_row_by_row_cross_transformation make_is_equal
  intro input h_input_valid
  exists (input.map (fun arg => PartialEq.eq value arg))
  constructor
  · rfl
  · intro v h_v_in
    unfold AtomDomain.default AtomDomain.contains
    simp only
