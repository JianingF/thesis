structure Bounds (TA : Type) [LE TA] where
  lower : TA
  upper : TA
  valid : lower ≤ upper

namespace Bounds
  def new_closed {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) : Except String (Bounds TA) :=
    if h : bounds.1 ≤ bounds.2 then
      Except.ok ⟨bounds.1, bounds.2, h⟩
    else
      Except.error "Invalid bounds: lower must be ≤ upper"

  theorem new_closed_valid {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) (b : Bounds TA) :
      new_closed bounds = Except.ok b → bounds.1 ≤ bounds.2 := by
    intro h
    simp [new_closed] at h
    split at h
    · case isTrue h_le => exact h_le
    · case isFalse => contradiction

  theorem new_closed_lower {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) (b : Bounds TA) :
      new_closed bounds = Except.ok b → b.lower = bounds.1 := by
    intro h
    simp [new_closed] at h
    split at h
    · case isTrue h_le => cases h; rfl
    · case isFalse => contradiction

  theorem new_closed_upper {TA : Type} [LE TA] [DecidableRel (α := TA) (· ≤ ·)]
      (bounds : TA × TA) (b : Bounds TA) :
      new_closed bounds = Except.ok b → b.upper = bounds.2 := by
    intro h
    simp [new_closed] at h
    split at h
    · case isTrue h_le => cases h; rfl
    · case isFalse => contradiction
end Bounds

structure AtomDomain (TA : Type) [LE TA] where
  bounds : Option (Bounds TA)
  is_non_null : Bool

namespace AtomDomain
  def contains {TA : Type} [LE TA] (domain : AtomDomain TA) (value : TA) : Prop :=
    match domain.bounds with
    | none => domain.is_non_null = true
    | some b => domain.is_non_null = true ∧ b.lower ≤ value ∧ value ≤ b.upper

  def default {TA : Type} [LE TA] : AtomDomain TA :=
    { bounds := none, is_non_null := true }
end AtomDomain

structure VectorDomain (RowDomain : Type) where
  element_domain : RowDomain
