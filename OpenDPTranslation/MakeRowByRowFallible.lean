/-
  Lean 4 formalization of `make_row_by_row_fallible` from OpenDP.

  Proves soundness: the returned Transformation has a valid stability map,
  i.e., if inputs are d_in-close then outputs are d_out-close whenever
  stability_map(d_in) succeeds with some d_out.

  FAITHFULNESS NOTES (vs. prior version):
  - The stability map is now fallible, matching `new_stability_map_from_constant(1)`.
    In Rust, this computes `TO.one().inf_mul(&TO.inf_cast(d_in)?)` which can
    fail if either `inf_cast` or `inf_mul` fails.
  - `InfCast` and `InfMul` are fallible, matching their Rust signatures.
-/

import OpenDPTranslation.OpenDPCore

-- ============================================================================
-- 1. InfCast and InfMul (fallible, matching Rust)
-- ============================================================================

/--
  `InfCast` mirrors the Rust `InfCast` trait.
  Provides a **fallible** cast from one distance type to another that rounds
  toward infinity (i.e., never underestimates).

  In Rust: `fn inf_cast(v: TI) -> Fallible<Self>`
  The cast can fail (e.g., overflow), returning `none`.
-/
class InfCast (α β : Type*) [Preorder α] [Preorder β] where
  inf_cast : α → Option β
  /-- inf_cast is monotone when it succeeds on both inputs -/
  monotone : ∀ {a b : α} {ra rb : β},
    a ≤ b → inf_cast a = some ra → inf_cast b = some rb → ra ≤ rb
  /-- inf_cast is downward-closed: if it succeeds on `b`, it succeeds on any `a ≤ b`.
      This is a natural property: if a larger value can be represented, so can a
      smaller one. Holds for all standard numeric casts in OpenDP. -/
  downward_closed : ∀ {a b : α},
    a ≤ b → inf_cast b ≠ none → inf_cast a ≠ none

/-- Extract the value from a successful `inf_cast`, given proof it doesn't fail. -/
theorem InfCast.exists_of_ne_none {α β : Type*} [Preorder α] [Preorder β]
    [inst : InfCast α β] {a : α} (h : inst.inf_cast a ≠ none)
    : ∃ v, inst.inf_cast a = some v := by
  cases h_eq : inst.inf_cast a with
  | none => exact absurd h_eq h
  | some v => exact ⟨v, rfl⟩

/--
  `InfMul` mirrors the Rust `InfMul` trait.
  Provides a **fallible** multiplication that rounds toward infinity.

  In Rust: `fn inf_mul(&self, v: &Self) -> Fallible<Self>`
-/
class InfMul (α : Type*) [Preorder α] where
  inf_mul : α → α → Option α
  /-- inf_mul is monotone in its second argument when it succeeds -/
  monotone_right : ∀ {c a b : α} {ra rb : α},
    a ≤ b → inf_mul c a = some ra → inf_mul c b = some rb → ra ≤ rb

/--
  `HasOne` provides the unit element for `InfMul`.
  Separate from Mathlib's `One` to keep our types self-contained.
-/
class HasOne (α : Type*) where
  one : α

-- ============================================================================
-- 2. new_stability_map_from_constant
-- ============================================================================

/--
  `new_stability_map_from_constant c` constructs a fallible stability map
  that computes `c.inf_mul(MO.inf_cast(d_in)?)`.

  This matches the Rust code:
  ```rust
  StabilityMap::new_from_constant(c) = |d_in| c.inf_mul(&MO::inf_cast(*d_in)?)
  ```
-/
def new_stability_map_from_constant
    {α β : Type*} [Preorder α] [Preorder β]
    [InfCast α β] [InfMul β]
    (c : β) (d_in : α) : Option β :=
  match InfCast.inf_cast d_in with
  | none => none
  | some casted => InfMul.inf_mul c casted

/--
  Key property: `new_stability_map_from_constant c` is monotone when it succeeds.
-/
theorem new_stability_map_from_constant_monotone
    {α β : Type*} [Preorder α] [Preorder β]
    [InfCast α β] [InfMul β]
    (c : β) {a b : α} {ra rb : β}
    (h_le : a ≤ b)
    (h_a : new_stability_map_from_constant c a = some ra)
    (h_b : new_stability_map_from_constant c b = some rb)
    : ra ≤ rb := by
  unfold new_stability_map_from_constant at h_a h_b
  cases h_ca : InfCast.inf_cast (α := α) (β := β) a with
  | none => simp [h_ca] at h_a
  | some ca =>
    rw [h_ca] at h_a
    cases h_cb : InfCast.inf_cast (α := α) (β := β) b with
    | none => simp [h_cb] at h_b
    | some cb =>
      rw [h_cb] at h_b
      have h_cast_mono := InfCast.monotone h_le h_ca h_cb
      exact InfMul.monotone_right h_cast_mono h_a h_b

-- ============================================================================
-- 3. make_row_by_row_fallible
-- ============================================================================

-- We use a section with `variable` to introduce InfCast/InfMul/HasOne on
-- `Metric.Distance M`. This avoids the "invalid binder annotation" error
-- that occurs when using `[InfCast (Metric.Distance M) ...]` directly in
-- a def/theorem signature, because `Metric.Distance M` is a dependent
-- projection that Lean cannot use in instance binder position.

section MakeRowByRowFallible

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

/--
  Construct the transformation corresponding to `make_row_by_row_fallible`.
  The stability map is `new_stability_map_from_constant(1)`, matching
  the Rust pseudocode.
-/
def make_row_by_row_fallible
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
    -- Faithfully matches: new_stability_map_from_constant(1)
    -- i.e. d_in → TO.one().inf_mul(TO.inf_cast(d_in)?)
    stability_map := new_stability_map_from_constant (HasOne.one)
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

  The `h_one_mul` assumption captures that `1.inf_mul(inf_cast(d_in)) ≥ d_in`
  whenever it succeeds. This is the property that the old formalization silently
  assumed by using `id` as the stability map.
-/
theorem make_row_by_row_fallible_is_valid
    (input_domain : DI)
    (input_metric : M)
    (output_row_domain : DatasetDomain.ElementDomain DO)
    (row_function : DatasetDomain.RowCarrier DI → Option (DatasetDomain.RowCarrier DO))
    -- Precondition: row_function maps valid rows to output_row_domain (or errors)
    (h_row_fn : ∀ r, Domain.mem (DatasetDomain.elementDomain input_domain) r →
      ∃ r', row_function r = some r' ∧ Domain.mem output_row_domain r')
    -- Precondition: 1.inf_mul(inf_cast(d_in)) ≥ d_in whenever it succeeds.
    (h_one_mul : ∀ (d_in d_out : Metric.Distance M),
      new_stability_map_from_constant (HasOne.one) d_in = some d_out →
      d_in ≤ d_out)
    : (make_row_by_row_fallible input_domain input_metric output_row_domain row_function).IsValid :=
  { -- Part 1: appropriate output domain
    output_mem := by
      intro data h_data
      simp [make_row_by_row_fallible]
      exact RowByRowDomain.apply_rows_mem input_domain output_row_domain
        row_function data h_data h_row_fn

    -- Part 2: stability map (uses Lemma f-sim)
    stability := by
      intro u v d_in d_out result_u result_v h_u_mem h_v_mem h_close h_stab h_fu h_fv
      simp [make_row_by_row_fallible] at h_fu h_fv h_stab ⊢
      have h_non_exp := DatasetMetric.map_non_expansive input_metric row_function
        u v result_u result_v h_fu h_fv
      have h_expand := h_one_mul d_in d_out h_stab
      exact le_trans (le_trans h_non_exp h_close) h_expand
  }

end MakeRowByRowFallible
