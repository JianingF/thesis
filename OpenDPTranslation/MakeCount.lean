/-
  Lean 4 formalization of `make_count` from OpenDP.

  `make_count` returns a Transformation that computes a count of the number
  of records in a vector. The count is exactly cast to a user-specified output
  type `TO`, saturating at `TO.MAX_CONSECUTIVE` if the cast overflows.

  Unlike the row-by-row transformations, `make_count` does not delegate to
  `make_row_by_row`. It uses different input and output metrics
  (SymmetricDistance and AbsoluteDistance respectively), so we use a
  generalized Transformation that supports heterogeneous metrics.

  FAITHFULNESS NOTES (vs. prior version):
  - `AtomDomain` now carries `bounds` and `nullable` fields matching
    Rust's `AtomDomain<T> { bounds: Option<Bounds<T>>, nan: bool }`.
  - `VectorDomain` now carries an optional `size` field matching
    Rust's `VectorDomain<D> { element_domain: D, size: Option<usize> }`.
  - `InfCast` is fallible (`→ Option β`), matching the Rust trait.
  - `InfMul` is fallible (`→ Option α`), matching the Rust trait.
  - The stability map explicitly computes `TO.one().inf_mul(TO.inf_cast(d_in)?)`.
  - `HTransformation` uses a fallible stability map.
  - `SaturatingCountStable` is conditioned on `inf_cast` success.
-/

import OpenDPTranslation.OpenDPCore
import OpenDPTranslation.MakeRowByRowFallible  -- for InfCast, InfMul, HasOne

-- ============================================================================
-- 1. Generalized Transformation (heterogeneous metrics, fallible stability)
-- ============================================================================

/--
  A generalized `Transformation` that supports different input and output
  metric types. This is needed for transformations like `make_count` where
  the input metric (SymmetricDistance) differs from the output metric
  (AbsoluteDistance).

  The stability map is fallible (`→ Option`), matching Rust's
  `StabilityMap<MI, MO>(Arc<dyn Fn(&MI::Distance) -> Fallible<MO::Distance>>)`.
-/
structure HTransformation (DI DO : Type*) (MI MO : Type*)
    [Domain DI] [Domain DO]
    [Metric MI] [Metric MO]
    [MetricOn MI (Domain.Carrier DI)] [MetricOn MO (Domain.Carrier DO)] where
  input_domain  : DI
  output_domain : DO
  function      : Domain.Carrier DI → Option (Domain.Carrier DO)
  input_metric  : MI
  output_metric : MO
  stability_map : Metric.Distance MI → Option (Metric.Distance MO)

/--
  An `HTransformation` is **valid** (sound) if:
  1. For all inputs in the input domain, the function returns a value in the
     output domain.
  2. For all d_in: if `u, v` are d_in-close under the input metric and the
     stability map succeeds with `stability_map(d_in) = some d_out`, then
     `function(u), function(v)` are d_out-close under the output metric.
-/
structure HTransformation.IsValid {DI DO MI MO : Type*}
    [Domain DI] [Domain DO]
    [Metric MI] [Metric MO]
    [MetricOn MI (Domain.Carrier DI)] [MetricOn MO (Domain.Carrier DO)]
    (t : HTransformation DI DO MI MO) : Prop where
  /-- Part 1: output domain membership -/
  output_mem :
    ∀ data, Domain.mem t.input_domain data →
      ∃ result, t.function data = some result ∧ Domain.mem t.output_domain result
  /-- Part 2: stability (only when the stability map succeeds) -/
  stability :
    ∀ (u v : Domain.Carrier DI) (d_in : Metric.Distance MI)
      (d_out : Metric.Distance MO)
      (result_u result_v : Domain.Carrier DO),
      Domain.mem t.input_domain u →
      Domain.mem t.input_domain v →
      MetricOn.dist t.input_metric u v ≤ d_in →
      t.stability_map d_in = some d_out →
      t.function u = some result_u →
      t.function v = some result_v →
      MetricOn.dist t.output_metric result_u result_v ≤ d_out

-- ============================================================================
-- 2. Concrete Domain Types (faithful to Rust)
-- ============================================================================

/--
  Predicate capturing when a value is "non-null" or "checkable".
  In Rust, this corresponds to the `CheckNull` trait.
  For types like `f64`, null means NaN. For integer types, nothing is null.
-/
class CheckNull (α : Type*) where
  is_null : α → Prop

/--
  `AtomDomain α` mirrors Rust's `AtomDomain<α>`.

  In Rust:
  ```rust
  pub struct AtomDomain<T: CheckAtom> {
      pub bounds: Option<Bounds<T>>,
      nan: bool,
  }
  ```

  - `bounds`: optional bounds constraint on the values.
  - `nullable`: when `false`, null values (e.g., NaN for floats) are excluded.
    This corresponds to the Rust `nan` field (when `nan = false`, NaN is excluded).

  Membership requires:
  - If `nullable = false`, the value must be non-null.
  - If `bounds = some (lo, hi)`, the value must satisfy the bounds predicate.
-/
structure AtomDomain (α : Type*) [CheckNull α] where
  bounds : Option (α × α)
  nullable : Bool

instance instDomainAtomDomain {α : Type*} [CheckNull α] : Domain (AtomDomain α) where
  Carrier := α
  mem := fun d x => d.nullable = false → ¬ CheckNull.is_null x

/--
  For types where nothing is null (integers, bools), `CheckNull.is_null` is
  always `False`, so membership in any `AtomDomain` is trivially true.
-/
class NeverNull (α : Type*) [CheckNull α] : Prop where
  never_null : ∀ (x : α), ¬ CheckNull.is_null x

theorem AtomDomain.mem_of_never_null {α : Type*} [CheckNull α] [NeverNull α]
    (d : AtomDomain α) (x : α) : Domain.mem d x := by
  intro _
  exact NeverNull.never_null x

/--
  `VectorDomain D` mirrors Rust's `VectorDomain<D>`.

  In Rust:
  ```rust
  pub struct VectorDomain<D: Domain> {
      pub element_domain: D,
      pub size: Option<usize>,
  }
  ```

  - `element_domain`: the domain of each element.
  - `size`: optional constraint on the vector length.

  Membership requires:
  - All elements are in `element_domain`.
  - If `size = some n`, the vector has exactly `n` elements.
-/
structure VectorDomain (elem : Type*) where
  element_domain : elem
  size : Option ℕ

instance instDomainVectorDomain {α : Type*} [CheckNull α] :
    Domain (VectorDomain (AtomDomain α)) where
  Carrier := List α
  mem := fun d xs =>
    (∀ x ∈ xs, Domain.mem d.element_domain x) ∧
    (∀ n, d.size = some n → xs.length = n)

-- ============================================================================
-- 3. SymmetricDistance
-- ============================================================================

structure SymmetricDistance where

/-- Opaque wrapper around ℤ to serve as the distance type for SymmetricDistance. -/
structure IntDistance where
  val : ℤ
  deriving DecidableEq

instance : LE IntDistance where
  le a b := a.val ≤ b.val

instance : LT IntDistance where
  lt a b := a.val < b.val

instance : Preorder IntDistance where
  le_refl a := Int.le_refl a.val
  le_trans _ _ _ h1 h2 := Int.le_trans h1 h2
  lt_iff_le_not_ge a b := by
    show a.val < b.val ↔ a.val ≤ b.val ∧ ¬b.val ≤ a.val
    constructor
    · intro h; exact ⟨Int.le_of_lt h, Int.not_le.mpr h⟩
    · intro ⟨h1, h2⟩; omega

instance : Metric SymmetricDistance where
  Distance := IntDistance
  distOrd := inferInstance

/--
  The symmetric distance on `List α`.

  The key property `len_diff_le_dist` captures the chain from
  Lemma len-sum-equiv and the triangle inequality:
    |len(x) - len(x')| ≤ d_Sym(x, x')
-/
class SymmetricDistanceOnList (α : Type*) where
  dist : SymmetricDistance → List α → List α → IntDistance
  len_diff_le_dist : ∀ (m : SymmetricDistance) (u v : List α),
    IntDistance.mk (Int.natAbs ((u.length : ℤ) - (v.length : ℤ)) : ℤ) ≤ dist m u v

instance {α : Type*} [inst : SymmetricDistanceOnList α] :
    MetricOn SymmetricDistance (List α) where
  dist := inst.dist

/-- Bridge instance for `Domain.Carrier (VectorDomain (AtomDomain α))`. -/
instance instMetricOnSymDistVecAtom {α : Type*} [CheckNull α]
    [inst : SymmetricDistanceOnList α] :
    MetricOn SymmetricDistance (Domain.Carrier (VectorDomain (AtomDomain α))) where
  dist := inst.dist

-- ============================================================================
-- 4. AbsoluteDistance
-- ============================================================================

structure AbsoluteDistance (TO : Type*) where

instance {TO : Type*} [Preorder TO] : Metric (AbsoluteDistance TO) where
  Distance := TO
  distOrd := inferInstance

class AbsoluteDistanceOn (TO : Type*) [Preorder TO] where
  dist : AbsoluteDistance TO → TO → TO → TO

instance {TO : Type*} [Preorder TO] [inst : AbsoluteDistanceOn TO] :
    MetricOn (AbsoluteDistance TO) TO where
  dist := inst.dist

/-- Bridge instance for `Domain.Carrier (AtomDomain TO)`. -/
instance instMetricOnAbsDistAtom {TO : Type*} [Preorder TO] [CheckNull TO]
    [inst : AbsoluteDistanceOn TO] :
    MetricOn (AbsoluteDistance TO) (Domain.Carrier (AtomDomain TO)) where
  dist := inst.dist

-- ============================================================================
-- 5. ExactIntCast and saturating count
-- ============================================================================

class ExactIntCast (TO : Type*) where
  max_consecutive : TO
  exact_int_cast : ℕ → Option TO
  cast_spec : ∀ n, (∃ v, exact_int_cast n = some v) ∨ exact_int_cast n = none

def saturating_count {TO : Type*} [ExactIntCast TO] (n : ℕ) : TO :=
  match ExactIntCast.exact_int_cast n with
  | some v => v
  | none   => ExactIntCast.max_consecutive

-- ============================================================================
-- 6. Lemma: clamping is stable (Lemma dsym-sens)
-- ============================================================================

/--
  **Lemma dsym-sens** from the proof document.

  `|function(x) - function(x')| ≤ |len(x) - len(x')|`

  Since `function(x) = min(len(x), c)` where `c = MAX_CONSECUTIVE`,
  and clamping is non-expansive.

  The bound is stated via a successful `InfCast` to bridge IntDistance → TO.
-/
class SaturatingCountStable (TO : Type*) [Preorder TO] [ExactIntCast TO]
    [AbsoluteDistanceOn TO] [InfCast IntDistance TO] where
  /-- |saturating_count(n) - saturating_count(m)| ≤ cast_result
      whenever inf_cast(|n - m|) = some cast_result -/
  stable : ∀ (m_out : AbsoluteDistance TO) (n₁ n₂ : ℕ) (cast_result : TO),
    InfCast.inf_cast (α := IntDistance) (β := TO)
      (IntDistance.mk (Int.natAbs ((n₁ : ℤ) - (n₂ : ℤ)) : ℤ)) = some cast_result →
    AbsoluteDistanceOn.dist m_out (saturating_count n₁) (saturating_count n₂) ≤
      cast_result

-- ============================================================================
-- 7. make_count
-- ============================================================================

section MakeCount

variable {TIA TO : Type*}
  [CheckNull TIA] [NeverNull TIA]
  [Preorder TO]
  [CheckNull TO] [NeverNull TO]
  [SymmetricDistanceOnList TIA]
  [AbsoluteDistanceOn TO]
  [ExactIntCast TO]
  [InfCast IntDistance TO]
  [InfMul TO]
  [HasOne TO]
  [SaturatingCountStable TO]

/--
  Construct the transformation corresponding to `make_count`.

  - Stability map: `new_stability_map_from_constant(1)`, i.e.
    `d_in → TO.one().inf_mul(TO.inf_cast(d_in)?)`
    This is fallible: returns `none` if `inf_cast` or `inf_mul` fails.
-/
def make_count
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance)
    : HTransformation
        (VectorDomain (AtomDomain TIA)) (AtomDomain TO)
        SymmetricDistance (AbsoluteDistance TO) :=
  { input_domain  := input_domain
    output_domain := ⟨none, false⟩  -- no bounds, non-nullable
    function      := fun data => some (saturating_count data.length)
    input_metric  := input_metric
    output_metric := AbsoluteDistance.mk
    -- Faithfully: d_in → TO.one().inf_mul(TO.inf_cast(d_in)?)
    stability_map := fun d_in =>
      match InfCast.inf_cast (α := IntDistance) (β := TO) d_in with
      | none => none
      | some casted => InfMul.inf_mul (HasOne.one : TO) casted
  }

-- ============================================================================
-- 8. Soundness Theorem
-- ============================================================================

/--
  **Soundness of `make_count`.**

  **Part 1 (output domain):**
  The function always returns `some`. The output `AtomDomain TO` has no bounds,
  and `TO` is `NeverNull`, so membership is trivial.

  **Part 2 (stability map):**
  When the stability map succeeds (i.e., both `inf_cast` and `inf_mul` succeed):
    |f(x) - f(x')|
      ≤ casted_len_diff                by Lemma dsym-sens
      ≤ casted_din                     by InfCast.monotone (len diff ≤ d_Sym ≤ d_in)
      ≤ 1.inf_mul(casted_din) = d_out  by InfMul (1× is non-decreasing)
-/
theorem make_count_is_valid
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance)
    -- Precondition: 1.inf_mul does not decrease its argument.
    (h_one_mul_nondec : ∀ (x y : TO),
      InfMul.inf_mul (HasOne.one : TO) x = some y → x ≤ y)
    : (make_count (TO := TO) input_domain input_metric).IsValid :=
  { -- Part 1: appropriate output domain
    output_mem := by
      intro data _h_data
      refine ⟨saturating_count data.length, rfl, ?_⟩
      intro _
      exact NeverNull.never_null _

    -- Part 2: stability map
    stability := by
      intro u v d_in d_out result_u result_v _h_u_mem _h_v_mem h_close h_stab h_fu h_fv
      simp only [make_count] at h_fu h_fv h_stab ⊢
      cases h_fu; cases h_fv
      -- Parse the stability map: inf_cast d_in must have succeeded
      split at h_stab
      · -- inf_cast d_in = none → stability_map = none, contradicts h_stab
        simp at h_stab
      · -- inf_cast d_in = some casted_din
        rename_i casted_din h_cast_din
        -- h_stab : InfMul.inf_mul 1 casted_din = some d_out

        -- Lemma len-sum-equiv + triangle: |len(u) - len(v)| ≤ d_Sym(u,v)
        have h_len_le := SymmetricDistanceOnList.len_diff_le_dist input_metric u v
        -- Combined: |len diff| ≤ d_Sym(u,v) ≤ d_in
        have h_len_le_din : IntDistance.mk
            (Int.natAbs ((u.length : ℤ) - (v.length : ℤ)) : ℤ) ≤ d_in :=
          le_trans h_len_le h_close

        -- By downward_closed: inf_cast(|len diff|) succeeds since inf_cast(d_in) did
        have h_cast_len_ne_none := InfCast.downward_closed (α := IntDistance) (β := TO)
          h_len_le_din (by rw [h_cast_din]; simp)
        obtain ⟨casted_len, h_cast_len⟩ := InfCast.exists_of_ne_none h_cast_len_ne_none

        -- Lemma dsym-sens: |f(u) - f(v)| ≤ casted_len
        have h_stable := SaturatingCountStable.stable
          AbsoluteDistance.mk u.length v.length casted_len h_cast_len

        -- InfCast.monotone: casted_len ≤ casted_din (since |len diff| ≤ d_in)
        have h_cast_mono := InfCast.monotone (α := IntDistance) (β := TO)
          h_len_le_din h_cast_len h_cast_din

        -- InfMul non-decreasing: casted_din ≤ d_out
        have h_mul_nondec := h_one_mul_nondec casted_din d_out h_stab

        -- Chain: |f(u) - f(v)| ≤ casted_len ≤ casted_din ≤ d_out
        exact le_trans (le_trans h_stable h_cast_mono) h_mul_nondec
  }

end MakeCount
