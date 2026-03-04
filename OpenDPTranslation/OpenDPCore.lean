/-
  OpenDP Core Abstractions for Lean 4.

  Shared infrastructure used across transformation proofs:
  Domain, Metric, MetricOn, OpenDPMetricSpace, DatasetDomain,
  RowByRowDomain, DatasetMetric, Transformation, and Transformation.IsValid.

  FAITHFULNESS NOTES (vs. prior version):
  - Stability maps are now fallible (`→ Option Distance`), matching Rust's
    `StabilityMap` which returns `Fallible<MO::Distance>`.
  - `Transformation.IsValid` stability condition only applies when the
    stability map succeeds, matching the Rust semantics where a failing
    stability map is a conservative "can't certify" outcome.
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
-- 2. Transformation (with fallible stability map)
-- ============================================================================

/--
  A `Transformation` bundles:
  - input/output domains and metrics
  - a (fallible) function from input carrier to output carrier
  - a **fallible** stability map from input distance to output distance

  The stability map is fallible (`→ Option Distance`), matching the Rust type:
    `StabilityMap<MI, MO>(Arc<dyn Fn(&MI::Distance) -> Fallible<MO::Distance>>)`
  A `none` return means the map cannot certify the given input distance,
  which is a conservative (safe) outcome.
-/
structure Transformation (DI DO : Type*) (M : Type*)
    [Domain DI] [Domain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)] where
  input_domain  : DI
  output_domain : DO
  function      : Domain.Carrier DI → Option (Domain.Carrier DO)
  input_metric  : M
  output_metric : M
  stability_map : Metric.Distance M → Option (Metric.Distance M)

/--
  A `Transformation` is **valid** (sound) if:
  1. For all inputs in the input domain, the function returns a value in the
     output domain (appropriate output domain).
  2. For all d_in: if `u, v` are d_in-close and the stability map succeeds
     with `stability_map(d_in) = some d_out`, then `function(u), function(v)`
     are d_out-close (stability guarantee).

  Note: the stability condition only applies when `stability_map` returns
  `some`. If it returns `none`, no guarantee is needed — this matches the
  Rust semantics where a failing stability map means "cannot certify".
-/
structure Transformation.IsValid {DI DO M : Type*}
    [Domain DI] [Domain DO]
    [Metric M] [MetricOn M (Domain.Carrier DI)] [MetricOn M (Domain.Carrier DO)]
    (t : Transformation DI DO M) : Prop where
  /-- Part 1: output domain membership -/
  output_mem :
    ∀ data, Domain.mem t.input_domain data →
      ∃ result, t.function data = some result ∧ Domain.mem t.output_domain result
  /-- Part 2: stability (only when the stability map succeeds) -/
  stability :
    ∀ (u v : Domain.Carrier DI) (d_in d_out : Metric.Distance M)
      (result_u result_v : Domain.Carrier DO),
      Domain.mem t.input_domain u →
      Domain.mem t.input_domain v →
      MetricOn.dist t.input_metric u v ≤ d_in →
      t.stability_map d_in = some d_out →
      t.function u = some result_u →
      t.function v = some result_v →
      MetricOn.dist t.output_metric result_u result_v ≤ d_out

-- ============================================================================
-- 3. Lemma f-sim (standalone, for documentation)
-- ============================================================================

/--
  **Lemma f-sim** (from the proof document).

  Let `f` be a deterministic, side-effect-free row function.
  For any datasets `u, v` and any `DatasetMetric` `M`:
    d_M(map f u, map f v) ≤ d_M(u, v)

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
