import Mathlib.Order.CompleteLattice

variable {α ι : Type*} [CompleteLattice α] {κ : ι → Sort*} {f : ∀ i, κ i → α}

lemma iInf₂_eq_bot : ⨅ (i) (j), f i j = ⊥ ↔ ∀ b > ⊥, ∃ i j, f i j < b := by
  sorry
