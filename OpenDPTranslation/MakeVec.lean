/-
  Lean 4 formalization of `make_vec` from OpenDP.

  `make_vec` returns a Transformation that wraps an input scalar in a
  singleton vector. The input metric is `AbsoluteDistance<T>` and the
  output metric becomes an `LpDistance<Q>`.

  The transformation is 1-stable because for singleton vectors:
    d_Lp([x], [x']) = (|x - x'|^p)^(1/p) = |x - x'| = d_Abs(x, x')

  Like `make_count`, this uses heterogeneous metrics (AbsoluteDistance → LpDistance),
  so it uses the `HTransformation` structure.

  CHANGES IN THIS VERSION:
  - `h_one_mul_nondec` hypothesis eliminated in favor of `OneInfMulNonDec` typeclass.
-/

import OpenDPTranslation.OpenDPCore
import OpenDPTranslation.MakeRowByRowFallible  -- for InfCast, InfMul, HasOne, OneInfMulNonDec
import OpenDPTranslation.MakeCount  -- for HTransformation, AbsoluteDistance

-- ============================================================================
-- 1. LpDistance
-- ============================================================================

/--
  `LpDistance` measures the Lp distance between two vectors.
  Parameterized by the type `Q` used for the distance values.

  For singleton vectors `[x]` and `[x']`:
    d_Lp([x], [x']) = (|x - x'|^p)^(1/p) = |x - x'|
-/
structure LpDistance (Q : Type*) where

instance instMetricLpDistance {Q : Type*} [Preorder Q] : Metric (LpDistance Q) where
  Distance := Q
  distOrd := inferInstance

/--
  Properties of `LpDistance` on a carrier type.
-/
class LpDistanceOn (Q : Type*) (α : Type*) [Preorder Q] where
  dist : LpDistance Q → α → α → Q

instance instMetricOnLpDistance {Q α : Type*} [Preorder Q] [inst : LpDistanceOn Q α] :
    MetricOn (LpDistance Q) α where
  dist := inst.dist

-- ============================================================================
-- 2. make_vec
-- ============================================================================

section MakeVec

variable {DI DO : Type*} {T Q : Type*}
  [Domain DI] [Domain DO]
  [preT : Preorder T] [preQ : Preorder Q]
  [AbsoluteDistanceOn T]
  [MetricOn (AbsoluteDistance T) (Domain.Carrier DI)]
  [LpDistanceOn Q (Domain.Carrier DO)]
  [infCastTQ : InfCast T Q]
  [infMulQ : InfMul Q]
  [hasOneQ : HasOne Q]
  [oneInfMulQ : OneInfMulNonDec Q]

/--
  Construct the transformation corresponding to `make_vec`.

  - Stability map: `new_stability_map_from_constant(1)`, i.e.
    `d_in → Q.one().inf_mul(Q.inf_cast(d_in)?)`
    This is fallible.
-/
def make_vec
    (input_domain : DI)
    (output_domain : DO)
    (input_metric : AbsoluteDistance T)
    (output_metric : LpDistance Q)
    (to_T : Domain.Carrier DI → T)
    (wrap : T → Domain.Carrier DO)
    : HTransformation DI DO (AbsoluteDistance T) (LpDistance Q) :=
  { input_domain  := input_domain
    output_domain := output_domain
    function      := fun data => some (wrap (to_T data))
    input_metric  := input_metric
    output_metric := output_metric
    -- Faithfully: d_in → Q.one().inf_mul(Q.inf_cast(d_in)?)
    stability_map := fun d_in =>
      match infCastTQ.inf_cast d_in with
      | none => none
      | some casted => infMulQ.inf_mul hasOneQ.one casted
  }

-- ============================================================================
-- 3. Soundness Theorem
-- ============================================================================

/--
  **Soundness of `make_vec`.**

  **Part 1 (output domain):**
  The function is infallible. Wrapping any scalar from the input domain
  in a singleton vector produces a valid member of the output domain.

  **Part 2 (stability map):**
  When the stability map succeeds:
    d_Lp(f(x), f(x'))
      = d_Lp([x], [x'])
      ≤ Q.inf_cast(d_Abs(x, x'))       by h_wrap_stable + InfCast
      ≤ Q.inf_cast(d_in)               by InfCast.monotone
      ≤ Q.one().inf_mul(Q.inf_cast(d_in)) = d_out  by OneInfMulNonDec

  The `h_one_mul_nondec` hypothesis from the previous version is now provided
  by the `OneInfMulNonDec` typeclass instance.
-/
theorem make_vec_is_valid
    (input_domain : DI)
    (output_domain : DO)
    (input_metric : AbsoluteDistance T)
    (output_metric : LpDistance Q)
    (to_T : Domain.Carrier DI → T)
    (wrap : T → Domain.Carrier DO)
    -- Part 1 precondition: wrapping any T value produces a member of output_domain
    (h_output_mem : ∀ (t : T),
      Domain.mem output_domain (wrap t))
    -- Stability precondition:
    -- The Lp distance on wrapped values is bounded by inf_cast of the input distance,
    -- whenever inf_cast succeeds.
    (h_wrap_stable : ∀ (m_in : AbsoluteDistance T) (m_out : LpDistance Q)
      (u v : Domain.Carrier DI) (casted : Q),
      infCastTQ.inf_cast (MetricOn.dist m_in u v) = some casted →
      MetricOn.dist m_out (wrap (to_T u)) (wrap (to_T v)) ≤ casted)
    : (make_vec input_domain output_domain input_metric output_metric
        to_T wrap).IsValid :=
  { -- Part 1: appropriate output domain
    output_mem := by
      intro data _h_data
      exact ⟨wrap (to_T data), rfl, h_output_mem _⟩

    -- Part 2: stability map
    stability := by
      intro u v d_in d_out result_u result_v _h_u_mem _h_v_mem h_close h_stab h_fu h_fv
      simp only [make_vec] at h_fu h_fv h_stab ⊢
      cases h_fu; cases h_fv
      -- Parse stability map success
      split at h_stab
      · simp at h_stab
      · rename_i casted_din h_cast_din
        -- h_stab : inf_mul 1 casted_din = some d_out

        -- By downward_closed: inf_cast of d_Abs(u,v) succeeds since d_Abs(u,v) ≤ d_in
        have h_cast_dist_ne_none := InfCast.downward_closed (α := T) (β := Q)
          h_close (by rw [h_cast_din]; simp)
        obtain ⟨casted_dist, h_cast_dist⟩ := InfCast.exists_of_ne_none h_cast_dist_ne_none

        -- h_wrap_stable: d_Lp(wrap(to_T u), wrap(to_T v)) ≤ casted_dist
        have h_ws := h_wrap_stable input_metric output_metric u v casted_dist h_cast_dist

        -- InfCast.monotone: casted_dist ≤ casted_din
        have h_cast_mono := InfCast.monotone (α := T) (β := Q)
          h_close h_cast_dist h_cast_din

        -- OneInfMulNonDec: casted_din ≤ d_out
        have h_mul_nondec := OneInfMulNonDec.one_inf_mul_nondec casted_din d_out h_stab

        exact le_trans (le_trans h_ws h_cast_mono) h_mul_nondec
  }

end MakeVec
