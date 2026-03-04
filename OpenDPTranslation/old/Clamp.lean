import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations
import OpenDPTranslation.Axioms
import OpenDPTranslation.RowByRow

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
