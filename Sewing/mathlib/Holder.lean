import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Probability.Martingale.Basic

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

section Emetric

variable [PseudoEMetricSpace X]

section PseudoEMetricSpace

variable [PseudoEMetricSpace Y]

lemma HolderWith.const {C r : ℝ≥0} {c : Y} :
    HolderWith C r (Function.const X c) := fun x₁ x₂ => by
  simp only [Function.const_apply, edist_self, zero_le]

lemma HolderWith.zero [Zero Y] {C r : ℝ≥0} : HolderWith C r (0 : X → Y) :=
  .const

lemma HolderWith.isEmpty {C r : ℝ≥0} {f : X → Y} (hX : IsEmpty X) :
    HolderWith C r f := fun x₁ => False.elim <| hX.elim x₁

lemma HolderWith.mono {C C' r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) (h : C ≤ C') :
    HolderWith C' r f := fun x₁ x₂ => (hf x₁ x₂).trans (by
  by_cases hC : C = 0
  · simp only [hC, ENNReal.coe_zero, zero_mul, zero_le]
  by_cases hx : edist x₁ x₂ ^ (r : ℝ) = ∞
  · rw [hx, ENNReal.mul_top (coe_ne_zero.2 <| ne_of_gt <| lt_of_lt_of_le (by positivity) h)]
    exact le_top
  by_cases hx' : edist x₁ x₂ ^ (r : ℝ) = 0
  · rw [hx', mul_zero]
    exact zero_le _
  exact (ENNReal.mul_le_mul_right hx' hx).2 <| coe_le_coe.2 h)

end PseudoEMetricSpace

section SeminormedAddCommGroup

lemma HolderWith.add [SeminormedAddCommGroup Y]
    {C C' r : ℝ≥0} {f g : X → Y}
    (hf : HolderWith C r f) (hg : HolderWith C' r g) :
    HolderWith (C + C') r (f + g) := fun x₁ x₂ => by
  refine le_trans (edist_add_add_le _ _ _ _) <| le_trans (add_le_add (hf x₁ x₂) (hg x₁ x₂)) ?_
  rw [coe_add, add_mul]

lemma HolderWith.smul {α} [NormedDivisionRing α] [SeminormedAddCommGroup Y]
    [Module α Y] [BoundedSMul α Y] {C r : ℝ≥0} {f : X → Y} (c : α)
    (hf : HolderWith C r f) : HolderWith (C * ‖c‖₊) r (c • f) := fun x₁ x₂ => by
  specialize hf x₁ x₂
  rw [Pi.smul_apply, coe_mul, Pi.smul_apply, edist_smul₀, mul_comm (C : ℝ≥0∞),
    ENNReal.smul_def, smul_eq_mul, mul_assoc]
  gcongr

end SeminormedAddCommGroup

end Emetric
