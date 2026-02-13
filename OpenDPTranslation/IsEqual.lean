import OpenDPTranslation.TypeClasses
import OpenDPTranslation.Domains
import OpenDPTranslation.Transformations
import OpenDPTranslation.Axioms

def is_valid_row_by_row_cross_transformation
    {TIA TOA : Type} [LE TIA] [LE TOA]
    (input_domain : VectorDomain (AtomDomain TIA))
    (t : RowByRowTransformationCross TIA TOA) : Prop :=
  ∀ (input : List TIA),
    (∀ v ∈ input, input_domain.element_domain.contains v) →
    ∃ (output : List TOA),
      t.apply input = Except.ok output ∧
      (∀ v ∈ output, t.output_domain.contains v)

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
