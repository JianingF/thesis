/-
  Lean 4 formalization of `make_clamp` from OpenDP.

  Proves soundness of `make_clamp` by showing its clamping row function
  satisfies the preconditions of `make_row_by_row_fallible`, then
  appealing to the soundness of that constructor.
-/

import OpenDPTranslation.OpenDPCore
import OpenDPTranslation.MakeRowByRowFallible

-- ============================================================================
-- 1. ProductOrd and Bounds
-- ============================================================================

/--
  `ProductOrd` mirrors the Rust `ProductOrd` trait.
  It provides a total comparison on a type that may contain non-comparable
  values (e.g., NaN floats), hence operations return `Option`.

  `total_clamp x lo hi` clamps `x` to the interval `[lo, hi]`.
-/
class ProductOrd (α : Type*) where
  total_cmp   : α → α → Option Ordering
  total_clamp : α → α → α → Option α
  /-- If all three arguments are comparable (non-null), then `total_clamp`
      succeeds and returns a value between `lo` and `hi`. -/
  total_clamp_spec :
    ∀ (x lo hi : α),
      total_cmp lo hi = some Ordering.lt ∨ total_cmp lo hi = some Ordering.eq →
      total_cmp lo x ≠ none →
      total_cmp x hi ≠ none →
      ∃ y, total_clamp x lo hi = some y

/--
  `Bounds` represents a closed interval `[lower, upper]`.
  The validity condition ensures `lower ≤ upper` in the `ProductOrd` sense,
  corresponding to `Bounds.new_closed` not raising an exception.
-/
structure Bounds (α : Type*) [ProductOrd α] where
  lower : α
  upper : α
  valid : ProductOrd.total_cmp lower upper = some Ordering.lt ∨
          ProductOrd.total_cmp lower upper = some Ordering.eq

-- ============================================================================
-- 2. make_clamp
-- ============================================================================

section MakeClamp

variable {DI DO M α : Type*}
  [DatasetDomain DI] [DatasetDomain DO]
  [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
  [RowByRowDomain DI DO]
  [OpenDPMetricSpace DI M] [OpenDPMetricSpace DO M]
  [DatasetMetric M DI DO]
  [InfCast (Metric.Distance M) (Metric.Distance M)]
  [InfMul (Metric.Distance M)]
  [HasOne (Metric.Distance M)]
  [ProductOrd α]

/--
  The clamping row function: clamps each row value to `[bounds.lower, bounds.upper]`.
  This is fallible because `total_clamp` may fail on non-comparable values.

  Corresponds to `clamper` in the pseudocode.
-/
def clamp_row_function
    (bounds : Bounds α)
    (to_α : DatasetDomain.RowCarrier DI → α)
    (from_α : α → DatasetDomain.RowCarrier DO)
    : DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO) :=
  fun x => (ProductOrd.total_clamp (to_α x) bounds.lower bounds.upper).map from_α

/--
  Construct the transformation corresponding to `make_clamp`.

  Delegates to `make_row_by_row_fallible` with the clamping row function.
-/
def make_clamp
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (bounds : Bounds α)
    (to_α : DatasetDomain.RowCarrier DI → α)
    (from_α : α → DatasetDomain.RowCarrier DO)
    : Transformation DI DO M :=
  make_row_by_row_fallible input_domain input_metric output_row_domain
    (clamp_row_function bounds to_α from_α)

-- ============================================================================
-- 3. Soundness Theorem
-- ============================================================================

theorem make_clamp_is_valid
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (bounds : Bounds α)
    (to_α : DatasetDomain.RowCarrier DI → α)
    (from_α : α → DatasetDomain.RowCarrier DO)
    (h_clamp : ∀ r, Domain.mem (DatasetDomain.elementDomain input_domain) r →
      ∃ r', clamp_row_function bounds to_α from_α r = some r' ∧
        Domain.mem output_row_domain r')
    (h_one_mul : ∀ (d_in d_out : Metric.Distance M),
      new_stability_map_from_constant (HasOne.one) d_in = some d_out →
      d_in ≤ d_out)
    : (make_clamp input_domain input_metric output_row_domain bounds to_α from_α).IsValid := by
  unfold make_clamp
  exact make_row_by_row_fallible_is_valid
    input_domain input_metric output_row_domain
    (clamp_row_function bounds to_α from_α)
    h_clamp h_one_mul

end MakeClamp
