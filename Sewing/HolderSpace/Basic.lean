import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Probability.Martingale.Basic
import Sewing.HolderSpace.HolderNorm

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

variable (X Y) in
/-- Holder Space -/
structure HolderSpace (r : ℝ≥0) where
  toFun : X → Y
  HolderWith' : MemHolder r toFun

scoped[Topology]
  notation "C^" r "(" X "; " Y ")" => HolderSpace X Y r

variable {r : ℝ≥0}

instance : FunLike C^r(X; Y) X Y where
  coe := HolderSpace.toFun
  coe_injective' f g h := by cases f; cases g; congr

initialize_simps_projections HolderSpace (toFun → apply)

namespace HolderSpace

lemma memHolder (f : C^r(X; Y)) :
  MemHolder r f := f.2

instance [Zero Y] : Zero C^r(X; Y) where zero := ⟨0, memHolder_zero _⟩

end HolderSpace

end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] {r : ℝ≥0}

namespace HolderSpace

lemma holderWith [EMetricSpace Y] (f : C^r(X; Y)) : HolderWith (nnHolderNorm r f) r f :=
  f.memHolder.holderWith

instance [NormedAddCommGroup Y]: Add C^r(X; Y) where
  add f g := ⟨f + g, f.memHolder.add g.memHolder⟩

instance {α} [NormedDivisionRing α] [NormedAddCommGroup Y]
    [Module α Y] [BoundedSMul α Y] : SMul α C^r(X; Y) where
  smul c f := ⟨c • f, f.memHolder.smul c⟩

def comp {Z : Type*} [MetricSpace Z] [EMetricSpace Y]
    (f : C^r(Z; X)) (g : C^r(X; Y)) : C^(r * r)(Z; Y) :=
  ⟨g ∘ f, f.memHolder.comp g.memHolder⟩

end HolderSpace

end MetricSpace


-- def Embedding {r s : ℝ≥0} (h : r ≤ s) :
--   HolderSpace X Y s → HolderSpace X Y r :=
