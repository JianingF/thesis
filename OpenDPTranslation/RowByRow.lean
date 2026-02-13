import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations
import OpenDPTranslation.Axioms
import OpenDPTranslation.RowByRowFallible

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
