/-
  Lean 4 formalization of `make_is_equal` from OpenDP.

  The transformation checks if each element in a vector dataset is equivalent
  to a given value, returning a vector of booleans.

  Proves soundness by showing the equality row function satisfies the
  preconditions of `make_row_by_row`, then appealing to its soundness.
-/

import OpenDPTranslation.OpenDPCore
import OpenDPTranslation.MakeRowByRowFallible
import OpenDPTranslation.MakeRowByRow

-- ============================================================================
-- 1. make_is_equal
-- ============================================================================

section MakeIsEqual

variable {DI DO M TIA : Type*}
  [DatasetDomain DI] [DatasetDomain DO]
  [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
  [RowByRowDomain DI DO]
  [OpenDPMetricSpace DI M] [OpenDPMetricSpace DO M]
  [DatasetMetric M DI DO]
  [InfCast (Metric.Distance M) (Metric.Distance M)]
  [InfMul (Metric.Distance M)]
  [HasOne (Metric.Distance M)]
  [InfCastSelfNonDec (Metric.Distance M)]
  [OneInfMulNonDec (Metric.Distance M)]
  [BEq TIA]

/--
  The equality-checking row function: compares each row value to a fixed `value`.
  Returns a boolean (the row carrier of the output domain).

  Corresponds to `is_equal` in the pseudocode.
  Since `PartialEq.eq` always returns a `bool`, this function is total (infallible).
-/
def is_equal_row_function
    (value : TIA)
    (to_TIA : DatasetDomain.RowCarrier DI → TIA)
    (from_bool : Bool → DatasetDomain.RowCarrier DO)
    : DatasetDomain.RowCarrier DI → DatasetDomain.RowCarrier DO :=
  fun x => from_bool (BEq.beq (to_TIA x) value)

/--
  Construct the transformation corresponding to `make_is_equal`.

  Delegates to `make_row_by_row` with the equality-checking row function.
-/
def make_is_equal
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (value : TIA)
    (to_TIA : DatasetDomain.RowCarrier DI → TIA)
    (from_bool : Bool → DatasetDomain.RowCarrier DO)
    : Transformation DI DO M :=
  make_row_by_row input_domain input_metric output_row_domain
    (is_equal_row_function value to_TIA from_bool)

-- ============================================================================
-- 2. Soundness Theorem
-- ============================================================================

theorem make_is_equal_is_valid
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (value : TIA)
    (to_TIA : DatasetDomain.RowCarrier DI → TIA)
    (from_bool : Bool → DatasetDomain.RowCarrier DO)
    (h_bool_mem : ∀ (b : Bool),
      Domain.mem output_row_domain (from_bool b))
    : (make_is_equal input_domain input_metric output_row_domain value to_TIA from_bool).IsValid := by
  unfold make_is_equal
  apply make_row_by_row_is_valid
  · intro r _h_r_mem
    exact h_bool_mem _

end MakeIsEqual
