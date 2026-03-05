/-
  Lean 4 formalization of `make_row_by_row` from OpenDP.

  This constructor is a special case of `make_row_by_row_fallible`.
  The row function is total (infallible), so it is lifted into `Option`
  and the proof appeals directly to the soundness of `make_row_by_row_fallible`.
-/

import OpenDPTranslation.OpenDPCore
import OpenDPTranslation.MakeRowByRowFallible

-- ============================================================================
-- 1. make_row_by_row
-- ============================================================================

section MakeRowByRow

variable {DI DO M : Type*}
  [DatasetDomain DI] [DatasetDomain DO]
  [Metric M]
  [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
  [RowByRowDomain DI DO]
  [OpenDPMetricSpace DI M] [OpenDPMetricSpace DO M]
  [DatasetMetric M DI DO]
  [InfCast (Metric.Distance M) (Metric.Distance M)]
  [InfMul (Metric.Distance M)]
  [HasOne (Metric.Distance M)]
  [InfCastSelfNonDec (Metric.Distance M)]
  [OneInfMulNonDec (Metric.Distance M)]

/--
  Construct the transformation corresponding to `make_row_by_row`.

  This is a special case of `make_row_by_row_fallible` where the row function
  is total (infallible). The total function `row_function : RowCarrier DI → RowCarrier DO`
  is lifted to `fun r => some (row_function r)` and delegated to `make_row_by_row_fallible`.
-/
def make_row_by_row
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (row_function : DatasetDomain.RowCarrier DI → DatasetDomain.RowCarrier DO)
    : Transformation DI DO M :=
  make_row_by_row_fallible input_domain input_metric output_row_domain
    (fun r => some (row_function r))

-- ============================================================================
-- 2. Soundness Theorem
-- ============================================================================

/--
  **Soundness of `make_row_by_row`.**

  Since the preconditions for `make_row_by_row` are a superset of those for
  `make_row_by_row_fallible` (total functions are a special case of fallible ones),
  the proof appeals directly to `make_row_by_row_fallible_is_valid`.
-/
theorem make_row_by_row_is_valid
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (row_function : DatasetDomain.RowCarrier DI → DatasetDomain.RowCarrier DO)
    -- Precondition: row_function maps valid rows to output_row_domain
    (h_row_fn : ∀ r, Domain.mem (DatasetDomain.elementDomain input_domain) r →
      Domain.mem output_row_domain (row_function r))
    : (make_row_by_row input_domain input_metric output_row_domain row_function).IsValid := by
  unfold make_row_by_row
  apply make_row_by_row_fallible_is_valid
  · intro r h_r_mem
    exact ⟨row_function r, rfl, h_row_fn r h_r_mem⟩

end MakeRowByRow
