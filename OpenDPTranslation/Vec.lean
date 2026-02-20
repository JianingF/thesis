import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations
import OpenDPTranslation.Axioms

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
