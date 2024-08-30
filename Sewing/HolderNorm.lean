import Mathlib.Topology.MetricSpace.Holder
import Sewing.Mathlib.CompleteLattice
import Sewing.Mathlib.Holder

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

noncomputable
def eHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HolderWith C r f), C

noncomputable
def NNHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := (eHolderNorm r f).toNNReal

def MemHolder (r : ℝ≥0) (f : X → Y) : Prop := eHolderNorm r f ≠ ∞

variable (X) in
lemma eHolderNorm_const (r : ℝ≥0) (c : Y) : eHolderNorm r (Function.const X c) = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

lemma eHolderNorm_of_isEmpty {r : ℝ≥0} {f : X → Y} (hX : IsEmpty X) :
    eHolderNorm r f = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .isEmpty hX, hε⟩

end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] [EMetricSpace Y]

lemma eHolderNorm_eq_zero_iff {r : ℝ≥0} {f : X → Y} :
    eHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  constructor
  . refine fun h x₁ x₂ => ?_
    by_cases hx : x₁ = x₂
    . rw [hx]
    . rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero, ← le_zero_iff]
      refine le_of_forall_lt' fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : ℝ))
        (ENNReal.div_pos hb.ne.symm (ENNReal.rpow_lt_top_of_nonneg zero_le_coe
          (edist_lt_top x₁ x₂).ne).ne)
      exact lt_of_le_of_lt (hC x₁ x₂) <| ENNReal.mul_lt_of_lt_div hC'
  . intro h
    cases' isEmpty_or_nonempty X with hX hX
    . exact eHolderNorm_of_isEmpty hX
    . rw [← eHolderNorm_const X r (f hX.some)]
      congr
      simp [funext_iff, h _ hX.some]

lemma MemHolder.holderWith {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    HolderWith (NNHolderNorm r f) r f := by
  intros x₁ x₂
  rw [NNHolderNorm, eHolderNorm, coe_toNNReal]
  swap; exact hf
  sorry
  -- . rw [← ENNReal.iInf_mul_right]
  --   . refine le_iInf <| fun C => ?_
  --     -- by_cases htop : edist x₁ x₂ ^ (r : ℝ) = ∞
  --     -- . simp [htop]
  --     rw [← ENNReal.iInf_mul_right']
  --     . exact le_iInf <| fun hC => hC x₁ x₂
  --     . sorry
  --     . sorry
  --     -- . intros h₁ h₂
  --       -- rw [ENNReal.coe_eq_zero, exists_prop]
  --       -- rw [← ENNReal.bot_eq_zero, iInf_eq_bot] at h₂
  --   . sorry



end EMetricSpace
