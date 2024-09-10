import sewing.HolderSpace.HolderNorm

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [NNNorm Y] {r : ℝ≥0} {f : X → X → Y}

def HolderWith₂ (C r : ℝ≥0) (f : X → X → Y) : Prop :=
  ∀ x y, ‖f x y‖₊ ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

noncomputable
def eHolderNorm₂ (r : ℝ≥0) (f : X → X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HolderWith₂ C r f), C

noncomputable
def nnHolderNorm₂ (r : ℝ≥0) (f : X → X → Y) : ℝ≥0 := (eHolderNorm₂ r f).toNNReal

def MemHolder₂ (r : ℝ≥0) (f : X → X → Y) : Prop := eHolderNorm₂ r f ≠ ∞

lemma not_memHolder₂ : ¬ MemHolder₂ r f ↔ eHolderNorm₂ r f = ∞ := by
  rw [MemHolder₂, not_not]

lemma MemHolder₂.ne_top (hf : MemHolder₂ r f) : eHolderNorm₂ r f ≠ ∞ :=
  hf

lemma MemHolder₂.lt_top (hf : MemHolder₂ r f) : eHolderNorm₂ r f < ∞ :=
  hf.ne_top.lt_top


#exit
variable (X) in
lemma eHolderNorm_zero [Zero Y] (r : ℝ≥0) : eHolderNorm₂ r (0 : X → X → Y) = 0 :=
  eHolderNorm_const X r 0

attribute [simp] eHolderNorm_const eHolderNorm_zero

lemma eHolderNorm_of_isEmpty (hX : IsEmpty X) :
    eHolderNorm r f = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .isEmpty hX, hε⟩

lemma HolderWith.eHolderNorm_le {C : ℝ≥0} (hf : HolderWith C r f) :
    eHolderNorm r f ≤ C :=
  iInf₂_le C hf

lemma HolderWith.memHolder {C : ℝ≥0} (hf : HolderWith C r f) :
    MemHolder r f :=
  ne_of_lt <| lt_of_le_of_lt hf.eHolderNorm_le <| coe_lt_top (r := C)

variable (X) in
lemma memHolder_const {c : Y} : MemHolder r (Function.const X c) :=
  (HolderWith.const X 0).memHolder

variable (X) in
lemma memHolder_zero [Zero Y] : MemHolder r (0 : X → Y) :=
  memHolder_const X

end PseudoEMetricSpace
