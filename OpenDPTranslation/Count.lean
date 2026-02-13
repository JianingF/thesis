import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations
import OpenDPTranslation.Axioms

def is_valid_transformation_count
    {TIA TO : Type} [LE TIA] [LE TO]
    (input_domain : VectorDomain (AtomDomain TIA))
    (t : Transformation TIA TO) : Prop :=
  ∀ (input : List TIA),
    (∀ v ∈ input, input_domain.element_domain.contains v) →
    ∃ (output : TO),
      t.apply input = Except.ok output ∧
      t.output_domain.contains output

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
