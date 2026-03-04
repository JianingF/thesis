/-
  Lean 4 formalization of `make_row_by_row_fallible` from OpenDP.

  Proves soundness: the returned Transformation has a valid stability map,
  i.e., if inputs are d_in-close then outputs are d_out-close whenever
  stability_map(d_in) ≤ d_out.
-/

import Mathlib.Order.Basic
import Mathlib.Tactic

-- ============================================================================
-- 1. Core Abstractions (mirroring OpenDP traits)
-- ============================================================================

/-- A `Domain` has a carrier type and a membership predicate. -/
class Domain (D : Type*) where
  Carrier : Type*
  mem : D → Carrier → Prop

/-- A `Metric` assigns a distance type (independent of the carrier). -/
class Metric (M : Type*) where
  Distance : Type*
  distOrd : Preorder Distance

instance Metric.instPreorderDistance {M : Type*} [m : Metric M] : Preorder m.Distance :=
  m.distOrd

instance Metric.instLEDistance {M : Type*} [m : Metric M] : LE m.Distance :=
  m.distOrd.toLE

/-- A `MetricOn` provides the actual distance function for a specific carrier. -/
class MetricOn (M : Type*) (α : Type*) [Metric M] where
  dist : M → α → α → Metric.Distance M

/-- `OpenDPMetricSpace` asserts that metric `m` is valid on domain `d`.
    Named to avoid collision with Mathlib's `MetricSpace`. -/
class OpenDPMetricSpace (D : Type*) (M : Type*) [Domain D] [Metric M] [MetricOn M (Domain.Carrier D)] where
  valid : D → M → Prop

/-- `DatasetDomain` is a domain whose elements are themselves drawn from a row domain. -/
class DatasetDomain (D : Type*) extends Domain D where
  ElementDomain : Type*
  elementDomainInstance : Domain ElementDomain
  elementDomain : D → ElementDomain

instance DatasetDomain.instElementDomain {D : Type*} [dd : DatasetDomain D] :
    Domain dd.ElementDomain :=
  dd.elementDomainInstance

/-- The carrier of rows in a `DatasetDomain`. -/
abbrev DatasetDomain.RowCarrier (D : Type*) [dd : DatasetDomain D] :=
  Domain.Carrier dd.ElementDomain

/--
  `RowByRowDomain DI DO` mirrors the Rust trait.
  It provides:
  - `translate`: build an output domain from an output row domain
  - `apply_rows`: map a fallible row function over a dataset
  - key property: applying a valid row function to a member of `d` yields
    a member of `translate d output_row_domain`
-/
class RowByRowDomain (DI DO : Type*)
    [DatasetDomain DI] [DatasetDomain DO] where
  translate : DI → DatasetDomain.ElementDomain DO → DO
  apply_rows :
    Domain.Carrier DI →
    (DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO)) →
    Option (Domain.Carrier DO)
  /-- If `row_function` maps rows in `d`'s row domain to `output_row_domain`
      (or returns `none` for data-independent errors), and `data ∈ d`,
      then `apply_rows` returns `some result` with `result ∈ translate d ord`. -/
  apply_rows_mem :
    ∀ (d : DI) (ord : DatasetDomain.ElementDomain DO)
      (row_fn : DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO))
      (data : Domain.Carrier DI),
      Domain.mem d data →
      (∀ r, Domain.mem (DatasetDomain.elementDomain d) r →
        ∃ r', row_fn r = some r' ∧ Domain.mem ord r') →
      ∃ result, apply_rows data row_fn = some result ∧
        Domain.mem (translate d ord) result

/--
  A `DatasetMetric` is a metric on datasets where row-wise application of a
  deterministic, side-effect-free function cannot increase distance.

  This is the key property used in Lemma f-sim from the proof document.
  It holds for standard dataset metrics (SymmetricDistance, ChangeOneDistance, etc.)
  because they count differing rows, and a deterministic function preserves equality.
-/
class DatasetMetric (M : Type*) (DI DO : Type*)
    [DatasetDomain DI] [DatasetDomain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
    [RowByRowDomain DI DO] where
  /-- Lemma f-sim: applying a deterministic function row-wise cannot increase
      the dataset metric distance.
      If `f` is deterministic and side-effect-free, then
        d_M(map f u, map f v) ≤ d_M(u, v). -/
  map_non_expansive :
    ∀ (m : M)
      (f : DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO))
      (u v : Domain.Carrier DI)
      (result_u result_v : Domain.Carrier DO),
      RowByRowDomain.apply_rows u f = some result_u →
      RowByRowDomain.apply_rows v f = some result_v →
      MetricOn.dist m result_u result_v ≤ MetricOn.dist m u v

-- ============================================================================
-- 2. Transformation
-- ============================================================================

/--
  A `Transformation` bundles:
  - input/output domains and metrics
  - a (fallible) function from input carrier to output carrier
  - a stability map from input distance to output distance
-/
structure Transformation (DI DO : Type*) (M : Type*)
    [Domain DI] [Domain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)] where
  input_domain  : DI
  output_domain : DO
  function      : Domain.Carrier DI → Option (Domain.Carrier DO)
  input_metric  : M
  output_metric : M
  stability_map : Metric.Distance M → Metric.Distance M

/--
  A `Transformation` is **valid** (sound) if:
  1. For all inputs in the input domain, the function returns a value in the
     output domain (appropriate output domain).
  2. For all d_in, d_out: if `u, v` are d_in-close and `stability_map(d_in) ≤ d_out`,
     then `function(u), function(v)` are d_out-close (stability guarantee).
-/
structure Transformation.IsValid {DI DO M : Type*}
    [Domain DI] [Domain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
    (t : Transformation DI DO M) : Prop where
  /-- Part 1: output domain membership -/
  output_mem :
    ∀ data, Domain.mem t.input_domain data →
      ∃ result, t.function data = some result ∧ Domain.mem t.output_domain result
  /-- Part 2: stability -/
  stability :
    ∀ (u v : Domain.Carrier DI) (d_in : Metric.Distance M)
      (result_u result_v : Domain.Carrier DO),
      Domain.mem t.input_domain u →
      Domain.mem t.input_domain v →
      MetricOn.dist t.input_metric u v ≤ d_in →
      t.function u = some result_u →
      t.function v = some result_v →
      MetricOn.dist t.output_metric result_u result_v ≤ t.stability_map d_in

-- ============================================================================
-- 3. make_row_by_row_fallible
-- ============================================================================

/--
  Construct the transformation corresponding to `make_row_by_row_fallible`.
  The stability map is the identity (constant multiplier 1), matching
  `new_stability_map_from_constant(1)` in the pseudocode.
-/
def make_row_by_row_fallible
    {DI DO M : Type*}
    [DatasetDomain DI] [DatasetDomain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
    [RowByRowDomain DI DO]
    [OpenDPMetricSpace DI M] [OpenDPMetricSpace DO M]
    [DatasetMetric M DI DO]
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (row_function : DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO))
    : Transformation DI DO M :=
  { input_domain  := input_domain
    output_domain := RowByRowDomain.translate input_domain output_row_domain
    function      := fun data => RowByRowDomain.apply_rows data row_function
    input_metric  := input_metric
    output_metric := input_metric
    stability_map := id  -- identity, i.e. multiplier 1
  }

-- ============================================================================
-- 4. Soundness Theorem
-- ============================================================================

/--
  **Soundness of `make_row_by_row_fallible`.**

  Under the preconditions from the proof document:
  - `row_function` has no side-effects (captured by `DatasetMetric.map_non_expansive`)
  - `row_function` maps rows in the input row domain to `output_row_domain`
    (or returns a data-independent error)

  the returned `Transformation` is valid.
-/
theorem make_row_by_row_fallible_is_valid
    {DI DO M : Type*}
    [DatasetDomain DI] [DatasetDomain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
    [RowByRowDomain DI DO]
    [OpenDPMetricSpace DI M] [OpenDPMetricSpace DO M]
    [inst : DatasetMetric M DI DO]
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (row_function : DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO))
    -- Precondition: row_function maps valid rows to output_row_domain (or errors)
    (h_row_fn : ∀ r, Domain.mem (DatasetDomain.elementDomain input_domain) r →
      ∃ r', row_function r = some r' ∧ Domain.mem output_row_domain r')
    : (make_row_by_row_fallible input_domain input_metric output_row_domain row_function).IsValid :=
  { -- Part 1: appropriate output domain
    output_mem := by
      intro data h_data
      simp [make_row_by_row_fallible]
      exact RowByRowDomain.apply_rows_mem input_domain output_row_domain
        row_function data h_data h_row_fn

    -- Part 2: stability map (uses Lemma f-sim)
    stability := by
      intro u v d_in result_u result_v h_u_mem h_v_mem h_close h_fu h_fv
      simp [make_row_by_row_fallible] at h_fu h_fv ⊢
      -- By DatasetMetric.map_non_expansive (Lemma f-sim):
      --   d_M(result_u, result_v) ≤ d_M(u, v)
      have h_non_exp := inst.map_non_expansive input_metric row_function
        u v result_u result_v h_fu h_fv
      -- By assumption: d_M(u, v) ≤ d_in
      -- stability_map = id, so stability_map(d_in) = d_in
      -- Chain: d_M(result_u, result_v) ≤ d_M(u, v) ≤ d_in = stability_map(d_in)
      exact le_trans h_non_exp h_close
  }

-- ============================================================================
-- 5. Lemma f-sim (standalone, for documentation)
-- ============================================================================

/--
  **Lemma f-sim** (from the proof document).

  Let `f` be a deterministic, side-effect-free row function.
  For any datasets `u, v` and any `DatasetMetric` `M`:
    d_M(map f u, map f v) ≤ d_M(u, v)

  Intuition: if u_i = v_i then f(u_i) = f(v_i) (determinism + no side effects),
  so applying f cannot increase the number of differing rows. It can only
  decrease it (e.g., if f is constant).

  In our formalization this is an axiom of `DatasetMetric`, since proving it
  generically would require committing to a concrete representation of datasets
  (e.g., `List α`) and a concrete metric (e.g., symmetric distance).
-/
theorem lemma_f_sim
    {DI DO M : Type*}
    [DatasetDomain DI] [DatasetDomain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
    [RowByRowDomain DI DO]
    [inst : DatasetMetric M DI DO]
    (m : M)
    (f : DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO))
    (u v : Domain.Carrier DI)
    (fu fv : Domain.Carrier DO)
    (h_fu : RowByRowDomain.apply_rows u f = some fu)
    (h_fv : RowByRowDomain.apply_rows v f = some fv)
    : MetricOn.dist m fu fv ≤ MetricOn.dist m u v :=
  inst.map_non_expansive m f u v fu fv h_fu h_fv
