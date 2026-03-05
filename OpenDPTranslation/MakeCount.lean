/-
  Lean 4 formalization of `make_count` from OpenDP.

  `make_count` returns a Transformation that computes a count of the number
  of records in a vector. The count is exactly cast to a user-specified output
  type `TO`, saturating at `TO.MAX_CONSECUTIVE` if the cast overflows.

  Unlike the row-by-row transformations, `make_count` does not delegate to
  `make_row_by_row`. It uses different input and output metrics
  (SymmetricDistance and AbsoluteDistance respectively), so we use a
  generalized Transformation that supports heterogeneous metrics.

  CHANGES IN THIS VERSION:
  - `SymmetricDistanceOnList` now has a concrete definition of symmetric
    distance using `List.diff`, and `len_diff_le_dist` is **proved** rather
    than axiomatized. This corresponds to Lemma `len-sum-equiv` and the
    triangle inequality from the LaTeX proof.
  - `h_one_mul_nondec` hypothesis is eliminated in favor of the
    `OneInfMulNonDec` typeclass.
  - `NeverNull` assumption is removed. Instead, `ExactIntCast` now carries
    proof obligations that `max_consecutive` and successful casts produce
    non-null values, faithfully matching the LaTeX Part 1 argument.
    The intermediate `saturating_count_not_null` theorem mirrors the
    case analysis in the LaTeX proof.
  - `SaturatingCountStable` (Lemma dsym-sens) is now **proved** rather than
    axiomatized. `ExactIntCast` is enriched with the Rust proof definitions
    (`from_nat`, `exact_int_cast_spec`, `max_consecutive_eq`), and the proof
    factors through a pure ℕ clamping lemma (`nat_min_clamp_non_expansive`)
    and two bridge typeclasses (`AbsDistFromNat`, `InfCastFromNat`).
-/

import OpenDPTranslation.OpenDPCore
import OpenDPTranslation.MakeRowByRowFallible  -- for InfCast, InfMul, HasOne, OneInfMulNonDec

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
-- 3. SymmetricDistance (concrete definition + proved len_diff_le_dist)
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

-- ----------------------------------------------------------------------------
-- 3a. Concrete symmetric distance on lists
-- ----------------------------------------------------------------------------

/--
  The symmetric distance on `List α` using the multiset symmetric difference.

  For lists `u` and `v`, the symmetric distance is:
    d_Sym(u, v) = |u.diff v| + |v.diff u|

  where `List.diff` removes elements of the second list from the first
  (one occurrence at a time), computing the multiset difference.

  This equals the histogram-based definition from the LaTeX proof:
    d_Sym(u, v) = Σ_z |h_u(z) - h_v(z)|

  because for each value z:
  - `u.diff v` retains max(count(z,u) - count(z,v), 0) copies of z
  - `v.diff u` retains max(count(z,v) - count(z,u), 0) copies of z
  - Their sum of lengths gives Σ_z |count(z,u) - count(z,v)|
-/
def symmetric_distance_list {α : Type*} [DecidableEq α]
    (_m : SymmetricDistance) (u v : List α) : IntDistance :=
  ⟨((u.diff v).length + (v.diff u).length : ℕ)⟩

-- ----------------------------------------------------------------------------
-- 3b. Key lemmas for the len_diff_le_dist proof
-- ----------------------------------------------------------------------------

/-- Core identity: `u.length + (v.diff u).length = v.length + (u.diff v).length`.

    Proved via the Multiset bridge:
    - `List.diff` corresponds to `Multiset` subtraction (`Multiset.coe_sub`)
    - `List.length` corresponds to `Multiset.card` (`Multiset.card_coe`)
    - The identity then follows from `Multiset` algebra:
      `card(u) + card(v - u) = card(v) + card(u - v)`
      which is a consequence of `s - t + (s ∩ t) = s` and commutativity of `∩`.
-/
theorem list_diff_length_identity {α : Type*} [DecidableEq α]
    (u v : List α) :
    u.length + (v.diff u).length = v.length + (u.diff v).length := by
  -- Bridge to Multiset: (↑l : Multiset α).card = l.length
  -- and ↑(l₁.diff l₂) = ↑l₁ - ↑l₂
  have h1 : (v.diff u).length = ((↑v : Multiset α) - ↑u).card := by
    simp [Multiset.coe_sub]
  have h2 : (u.diff v).length = ((↑u : Multiset α) - ↑v).card := by
    simp [Multiset.coe_sub]
  rw [h1, h2]
  -- Now use Multiset.card_sub and the inf (intersection) to prove the identity.
  -- Key identity: for any multisets s, t:
  --   s = (s - t) + (s ∩ t)   and   t = (t - s) + (t ∩ s)
  -- Since (s ∩ t) = (t ∩ s), taking card:
  --   card(s) = card(s - t) + card(s ∩ t)
  --   card(t) = card(t - s) + card(t ∩ s)
  -- Rearranging: card(s) + card(t - s) = card(s - t) + card(s ∩ t) + card(t - s)
  --            = card(t - s) + card(t ∩ s) + card(s - t)
  --            = card(t) + card(s - t)
  have h1 : (↑(v.diff u) : Multiset α) = ↑v - ↑u := (Multiset.coe_sub v u).symm
  have h2 : (↑(u.diff v) : Multiset α) = ↑u - ↑v := (Multiset.coe_sub u v).symm
  have hs := congr_arg Multiset.card (Multiset.sub_add_inter (↑u : Multiset α) ↑v)
  have ht := congr_arg Multiset.card (Multiset.sub_add_inter (↑v : Multiset α) ↑u)
  have h_ic := congr_arg Multiset.card (Multiset.inter_comm (↑u : Multiset α) ↑v)
  simp only [Multiset.card_add] at hs ht
  -- Now rewrite card of coerced lists to length everywhere
  -- h1 says ↑(v.diff u) = ↑v - ↑u, so (↑v - ↑u).card = (v.diff u).length
  have hvu : (↑v - ↑u : Multiset α).card = (v.diff u).length := by
    rw [← h1]; simp
  have huv : (↑u - ↑v : Multiset α).card = (u.diff v).length := by
    rw [← h2]; simp
  have huc : (↑u : Multiset α).card = u.length := by simp
  have hvc : (↑v : Multiset α).card = v.length := by simp
  omega

theorem len_diff_le_symmetric_distance {α : Type*} [DecidableEq α]
    (m : SymmetricDistance) (u v : List α) :
    IntDistance.mk (Int.natAbs ((u.length : ℤ) - (v.length : ℤ)) : ℤ) ≤
      symmetric_distance_list m u v := by
  unfold symmetric_distance_list
  show (Int.natAbs ((u.length : ℤ) - (v.length : ℤ)) : ℤ) ≤
    ↑((u.diff v).length + (v.diff u).length)
  have h_id := list_diff_length_identity u v
  -- Reduce to: natAbs ≤ n, which is ↑(natAbs x) ≤ ↑n, i.e. natAbs x ≤ n in ℕ
  suffices Int.natAbs ((u.length : ℤ) - v.length) ≤
    (u.diff v).length + (v.diff u).length by exact_mod_cast this
  -- Now everything is in ℕ. Use that natAbs(a - b) = max(a,b) - min(a,b) for nat casts
  omega

-- ----------------------------------------------------------------------------
-- 3c. Concrete instance of SymmetricDistanceOnList
-- ----------------------------------------------------------------------------

/--
  The symmetric distance on `List α`, with `len_diff_le_dist` **proved**
  from the concrete definition rather than axiomatized.
-/
class SymmetricDistanceOnList (α : Type*) where
  dist : SymmetricDistance → List α → List α → IntDistance
  len_diff_le_dist : ∀ (m : SymmetricDistance) (u v : List α),
    IntDistance.mk (Int.natAbs ((u.length : ℤ) - (v.length : ℤ)) : ℤ) ≤ dist m u v

/--
  Concrete instance for any type with `DecidableEq`.
  The distance is defined via `List.diff` and `len_diff_le_dist` is proved
  by `len_diff_le_symmetric_distance`.
-/
instance instSymmetricDistanceOnListDecEq {α : Type*} [DecidableEq α] :
    SymmetricDistanceOnList α where
  dist := symmetric_distance_list
  len_diff_le_dist := len_diff_le_symmetric_distance

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

/--
  `ExactIntCast` mirrors the Rust `ExactIntCast` trait, enriched with
  the Rust proof definitions.

  The Rust proof definition of `exact_int_cast` states:
    For any `v` of type `TI`, `Self::exact_int_cast(v)` either returns
    `Err(e)` if `v < MIN_CONSECUTIVE` or `v > MAX_CONSECUTIVE`,
    or `Ok(out)` where `out = v`.

  The Rust proof definition of `ExactIntBounds` states:
    `MAX_CONSECUTIVE` is the largest integer-consecutive finite value
    that can be represented by `Self`.

  We capture this with:
  - `max_consecutive_nat`: the threshold as a natural number
  - `from_nat`: an order-preserving embedding `ℕ → TO` that represents
    exact integer values in `TO`
  - `exact_int_cast_spec`: the cast succeeds iff `n ≤ max_consecutive_nat`,
    and on success returns `from_nat n`
  - `max_consecutive_eq`: `max_consecutive = from_nat max_consecutive_nat`
-/
class ExactIntCast (TO : Type*) [CheckNull TO] [Preorder TO] where
  max_consecutive : TO
  max_consecutive_nat : ℕ
  from_nat : ℕ → TO
  exact_int_cast : ℕ → Option TO
  /-- `from_nat` is order-preserving. -/
  from_nat_mono : ∀ {a b : ℕ}, a ≤ b → from_nat a ≤ from_nat b
  /-- Exact cast spec: succeeds iff n ≤ max_consecutive_nat, returning from_nat n.
      Mirrors the Rust proof definition of `exact_int_cast`. -/
  exact_int_cast_spec : ∀ n,
    (n ≤ max_consecutive_nat ∧ exact_int_cast n = some (from_nat n)) ∨
    (¬ n ≤ max_consecutive_nat ∧ exact_int_cast n = none)
  /-- `max_consecutive = from_nat max_consecutive_nat`.
      Mirrors the Rust proof definition of `ExactIntBounds`. -/
  max_consecutive_eq : max_consecutive = from_nat max_consecutive_nat
  /-- `max_consecutive` is non-null (it is finite by the Rust proof definition). -/
  max_consecutive_not_null : ¬ CheckNull.is_null max_consecutive
  /-- Successful casts produce non-null values (the output is an exact integer). -/
  exact_int_cast_not_null : ∀ (n : ℕ) (v : TO),
    exact_int_cast n = some v → ¬ CheckNull.is_null v

def saturating_count {TO : Type*} [CheckNull TO] [Preorder TO] [ExactIntCast TO]
    (n : ℕ) : TO :=
  match ExactIntCast.exact_int_cast (TO := TO) n with
  | some v => v
  | none   => ExactIntCast.max_consecutive

/--
  `saturating_count` always produces a non-null value.
-/
theorem saturating_count_not_null {TO : Type*} [CheckNull TO] [Preorder TO] [ExactIntCast TO]
    (n : ℕ) : ¬ CheckNull.is_null (saturating_count (TO := TO) n) := by
  unfold saturating_count
  cases h : ExactIntCast.exact_int_cast (TO := TO) n with
  | none => exact ExactIntCast.max_consecutive_not_null
  | some v => exact ExactIntCast.exact_int_cast_not_null n v h

/--
  Key identity: `saturating_count n = from_nat (Nat.min n max_consecutive_nat)`.

  This is the formalization of the LaTeX claim that
  `function(x) = min(len(x), MAX_CONSECUTIVE)`.
-/
theorem saturating_count_eq_from_nat_min
    {TO : Type*} [CheckNull TO] [Preorder TO] [inst : ExactIntCast TO]
    (n : ℕ) : saturating_count (TO := TO) n =
      inst.from_nat (Nat.min n inst.max_consecutive_nat) := by
  unfold saturating_count
  rcases inst.exact_int_cast_spec n with ⟨h_le, h_eq⟩ | ⟨h_gt, h_eq⟩
  · -- Cast succeeds: n ≤ max_consecutive_nat, so min n c = n
    simp [h_eq, Nat.min_eq_left h_le]
  · -- Cast fails: n > max_consecutive_nat, so min n c = c
    have h_le : inst.max_consecutive_nat ≤ n := Nat.le_of_not_le h_gt
    simp [h_eq, inst.max_consecutive_eq, Nat.min_eq_right h_le]

-- ============================================================================
-- 6. Lemma: clamping is stable (Lemma dsym-sens)
-- ============================================================================

/--
  **Pure ℕ lemma**: clamping to a constant is non-expansive.

  `|min(a, c) - min(b, c)| ≤ |a - b|`

  This is the core mathematical fact behind Lemma dsym-sens.
-/
theorem nat_min_clamp_non_expansive (a b c : ℕ) :
    Int.natAbs ((Nat.min a c : ℤ) - (Nat.min b c : ℤ)) ≤
    Int.natAbs ((a : ℤ) - (b : ℤ)) := by
  simp only [Nat.min_def]
  split <;> split <;> omega

/--
  `AbsoluteDistanceOn` enriched with properties connecting it to `from_nat`.

  The absolute distance between `from_nat a` and `from_nat b` is at most
  `from_nat |a - b|`, whenever `|a - b| ≤ max_consecutive_nat` (so that
  `from_nat` can represent the difference).

  This captures the idea that `AbsoluteDistance` on `TO` behaves as
  expected on the image of `from_nat`.
-/
class AbsDistFromNat (TO : Type*) [CheckNull TO] [Preorder TO] [ExactIntCast TO]
    [AbsoluteDistanceOn TO] : Prop where
  dist_from_nat_le : ∀ (m : AbsoluteDistance TO) (a b : ℕ),
    Int.natAbs ((a : ℤ) - (b : ℤ)) ≤ ExactIntCast.max_consecutive_nat (TO := TO) →
    AbsoluteDistanceOn.dist m
      (ExactIntCast.from_nat (TO := TO) a)
      (ExactIntCast.from_nat (TO := TO) b) ≤
    ExactIntCast.from_nat (TO := TO) (Int.natAbs ((a : ℤ) - (b : ℤ)))

/--
  `InfCast` from `IntDistance` to `TO` is compatible with `from_nat`:
  when `inf_cast` succeeds on a non-negative value, the result is at least
  `from_nat n`.

  This captures the "rounds toward infinity" property of `InfCast`:
  the cast result is at least as large as the exact integer value.
-/
class InfCastFromNat (TO : Type*) [CheckNull TO] [Preorder TO] [ExactIntCast TO]
    [InfCast IntDistance TO] : Prop where
  inf_cast_from_nat_le : ∀ (n : ℕ) (v : TO),
    InfCast.inf_cast (β := TO) (IntDistance.mk (n : ℤ)) = some v →
      ExactIntCast.from_nat (TO := TO) n ≤ v

/--
  **Lemma dsym-sens** (proved).

  `|function(x) - function(x')| ≤ cast_result`

  where `cast_result` is the `InfCast` of `|len(x) - len(x')|` into `TO`.

  Proof (following the LaTeX):
  1. `saturating_count n = from_nat (min(n, c))` by `saturating_count_eq_from_nat_min`
  2. `|min(a,c) - min(b,c)| ≤ |a - b|` by `nat_min_clamp_non_expansive`
  3. `dist(from_nat(min(a,c)), from_nat(min(b,c))) ≤ from_nat(|min(a,c) - min(b,c)|)`
     by `AbsDistFromNat` (since the clamped difference is within range)
  4. `from_nat(|min(a,c) - min(b,c)|) ≤ from_nat(|a - b|)` by `from_nat_mono`
  5. `from_nat(|a - b|) ≤ cast_result` by `InfCastFromNat`
-/
theorem saturating_count_stable
    {TO : Type*} [CheckNull TO] [Preorder TO]
    [inst : ExactIntCast TO]
    [AbsoluteDistanceOn TO]
    [InfCast IntDistance TO]
    [AbsDistFromNat TO]
    [InfCastFromNat TO]
    (m_out : AbsoluteDistance TO) (n₁ n₂ : ℕ) (cast_result : TO)
    (h_cast : InfCast.inf_cast (α := IntDistance) (β := TO)
      (IntDistance.mk (Int.natAbs ((n₁ : ℤ) - (n₂ : ℤ)) : ℤ)) = some cast_result)
    : AbsoluteDistanceOn.dist m_out (saturating_count n₁) (saturating_count n₂) ≤
        cast_result := by
  -- Step 1: rewrite saturating_count in terms of from_nat ∘ min
  rw [saturating_count_eq_from_nat_min n₁, saturating_count_eq_from_nat_min n₂]
  set c := inst.max_consecutive_nat
  set a := Nat.min n₁ c
  set b := Nat.min n₂ c
  -- Step 2: |min(n₁,c) - min(n₂,c)| ≤ |n₁ - n₂| (pure ℕ)
  have h_clamp := nat_min_clamp_non_expansive n₁ n₂ c
  -- The clamped difference is within range (since a, b ≤ c)
  have h_a_le : a ≤ c := Nat.min_le_right n₁ c
  have h_b_le : b ≤ c := Nat.min_le_right n₂ c
  have h_diff_le_c : Int.natAbs ((a : ℤ) - (b : ℤ)) ≤ c := by omega
  -- Step 3: dist(from_nat a, from_nat b) ≤ from_nat(|a - b|)
  have h_dist := AbsDistFromNat.dist_from_nat_le (TO := TO) m_out a b h_diff_le_c
  -- Step 4: from_nat(|a - b|) ≤ from_nat(|n₁ - n₂|) by monotonicity
  have h_mono := inst.from_nat_mono h_clamp
  -- Step 5: from_nat(|n₁ - n₂|) ≤ cast_result by InfCastFromNat
  have h_inf := InfCastFromNat.inf_cast_from_nat_le
    (TO := TO) (Int.natAbs ((n₁ : ℤ) - (n₂ : ℤ))) cast_result h_cast
  -- Chain: dist ≤ from_nat(|a-b|) ≤ from_nat(|n₁-n₂|) ≤ cast_result
  exact le_trans (le_trans h_dist h_mono) h_inf

-- ============================================================================
-- 7. make_count
-- ============================================================================

section MakeCount

variable {TIA TO : Type*}
  [CheckNull TIA]
  [Preorder TO]
  [CheckNull TO]
  [SymmetricDistanceOnList TIA]
  [AbsoluteDistanceOn TO]
  [ExactIntCast TO]
  [InfCast IntDistance TO]
  [InfMul TO]
  [HasOne TO]
  [OneInfMulNonDec TO]
  [AbsDistFromNat TO]
  [InfCastFromNat TO]

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
  The function always returns `some`. The output `AtomDomain TO` has no bounds
  and is non-nullable. By `saturating_count_not_null`, the result is always
  non-null, so membership is satisfied.

  **Part 2 (stability map):**
  When the stability map succeeds (i.e., both `inf_cast` and `inf_mul` succeed):
    |f(x) - f(x')|
      ≤ casted_len_diff                by Lemma dsym-sens (now proved)
      ≤ casted_din                     by InfCast.monotone (len diff ≤ d_Sym ≤ d_in)
      ≤ 1.inf_mul(casted_din) = d_out  by OneInfMulNonDec
-/
theorem make_count_is_valid
    (input_domain : VectorDomain (AtomDomain TIA))
    (input_metric : SymmetricDistance)
    : (make_count (TO := TO) input_domain input_metric).IsValid :=
  { -- Part 1: appropriate output domain
    output_mem := by
      intro data _h_data
      refine ⟨saturating_count data.length, rfl, ?_⟩
      intro _
      exact saturating_count_not_null data.length

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
        -- This is now PROVED via len_diff_le_symmetric_distance
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
        have h_stable := saturating_count_stable (TO := TO)
          AbsoluteDistance.mk u.length v.length casted_len h_cast_len

        -- InfCast.monotone: casted_len ≤ casted_din (since |len diff| ≤ d_in)
        have h_cast_mono := InfCast.monotone (α := IntDistance) (β := TO)
          h_len_le_din h_cast_len h_cast_din

        -- OneInfMulNonDec: casted_din ≤ d_out
        have h_mul_nondec := OneInfMulNonDec.one_inf_mul_nondec casted_din d_out h_stab

        -- Chain: |f(u) - f(v)| ≤ casted_len ≤ casted_din ≤ d_out
        exact le_trans (le_trans h_stable h_cast_mono) h_mul_nondec
  }

end MakeCount
