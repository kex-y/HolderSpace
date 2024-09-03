import Mathlib.Topology.MetricSpace.Holder
import Sewing.Mathlib.Holder

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

noncomputable
def eHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HolderWith C r f), C

noncomputable
def HolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := (eHolderNorm r f).toNNReal

def MemHolder (r : ℝ≥0) (f : X → Y) : Prop := eHolderNorm r f ≠ ∞

lemma not_memHolder {r : ℝ≥0} {f : X → Y} : ¬ MemHolder r f ↔ eHolderNorm r f = ∞ := by
  rw [MemHolder, not_not]

variable (X) in
lemma eHolderNorm_const (r : ℝ≥0) (c : Y) : eHolderNorm r (Function.const X c) = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

variable (X) in
lemma eHolderNorm_zero [Zero Y] (r : ℝ≥0) : eHolderNorm r (0 : X → Y) = 0 :=
  eHolderNorm_const X r 0

attribute [simp] eHolderNorm_const eHolderNorm_zero

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
    HolderWith (HolderNorm r f) r f := by
  intros x₁ x₂
  by_cases hx : x₁ = x₂
  . simp only [hx, edist_self, zero_le]
  rw [HolderNorm, eHolderNorm, coe_toNNReal]
  swap; exact hf
  have h₁ : edist x₁ x₂ ^ (r : ℝ) ≠ 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hx) (edist_lt_top x₁ x₂).ne)
  have h₂ : edist x₁ x₂ ^ (r : ℝ) ≠ ∞ := by
    simp [(edist_lt_top x₁ x₂).ne]
  rw [← ENNReal.div_le_iff h₁ h₂]
  refine le_iInf₂ fun C hC => ?_
  rw [ENNReal.div_le_iff h₁ h₂]
  exact hC x₁ x₂

lemma coe_HolderNorm_le_eHolderNorm
    {r : ℝ≥0} {f : X → Y} :
    (HolderNorm r f : ℝ≥0∞) ≤ eHolderNorm r f :=
  coe_toNNReal_le_self

lemma HolderWith.eHolderNorm_le {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    eHolderNorm r f ≤ C :=
  iInf₂_le C hf

lemma HolderWith.coe_HolderNorm_eq_eHolderNorm
    {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    (HolderNorm r f : ℝ≥0∞) = eHolderNorm r f := by
  rw [HolderNorm, coe_toNNReal]
  exact ne_of_lt <| lt_of_le_of_lt hf.eHolderNorm_le <| coe_lt_top (r := C)

lemma MemHolder.coe_HolderNorm_eq_eHolderNorm
    {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    (HolderNorm r f : ℝ≥0∞) = eHolderNorm r f :=
  hf.holderWith.coe_HolderNorm_eq_eHolderNorm

lemma HolderWith.holderNorm_le {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    HolderNorm r f ≤ C := by
  rw [← ENNReal.coe_le_coe, hf.coe_HolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le

lemma HolderWith.memHolder {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    MemHolder r f :=
  ne_of_lt <| lt_of_le_of_lt hf.eHolderNorm_le <| coe_lt_top (r := C)

end MetricSpace

section SeminormedAddCommGroup

variable [MetricSpace X] [NormedAddCommGroup Y]
variable {C r : ℝ≥0} {f g : X → Y}

lemma MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f + g) := by
  refine (hf.holderWith.add hg.holderWith).memHolder

variable (r f g) in
lemma eHolderNorm_add :
    eHolderNorm r (f + g) ≤ eHolderNorm r f + eHolderNorm r g := by
  by_cases hfg : MemHolder r f  ∧ MemHolder r g
  . obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_HolderNorm_eq_eHolderNorm, ← hg.coe_HolderNorm_eq_eHolderNorm, ← coe_add]
    exact (hf.add hg).holderWith.eHolderNorm_le.trans <|
      coe_le_coe.2 (hf.holderWith.add hg.holderWith).holderNorm_le
  . rw [Classical.not_and_iff_or_not_not, not_memHolder, not_memHolder] at hfg
    obtain (h | h) := hfg
    all_goals simp [h]

lemma MemHolder.smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y]
    (c : α) (hf : MemHolder r f) : MemHolder r (c • f) :=
  (hf.holderWith.smul c).memHolder

lemma eHolderNorm_smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y] (c : α) :
    eHolderNorm r (c • f) ≤ ‖c‖₊ * eHolderNorm r f := by
  by_cases hf : MemHolder r f
  . refine (hf.holderWith.smul c).eHolderNorm_le.trans ?_
    rw [coe_mul, hf.coe_HolderNorm_eq_eHolderNorm]
  . by_cases hc : ‖c‖₊ = 0
    . rw [nnnorm_eq_zero] at hc
      simp [hc]
    . rw [not_memHolder] at hf
      simp [hf, mul_top <| coe_ne_zero.2 hc]

end SeminormedAddCommGroup
