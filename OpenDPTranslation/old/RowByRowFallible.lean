import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations
import OpenDPTranslation.Axioms

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
