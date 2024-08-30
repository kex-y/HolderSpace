import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Probability.Martingale.Basic
import Sewing.Mathlib.Holder

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

variable [PseudoEMetricSpace X]

variable (X Y) in
/-- Holder Space -/
structure HolderSpace [PseudoEMetricSpace Y] (r : ℝ≥0) where
  toFun : X → Y
  HolderWith' : ∃ C, HolderWith C r toFun

scoped[Topology]
  notation "C^" r "(" X "; " Y ")" => HolderSpace X Y r

variable {r : ℝ≥0}

instance [PseudoEMetricSpace Y] : FunLike C^r(X; Y) X Y where
  coe := HolderSpace.toFun
  coe_injective' f g h := by cases f; cases g; congr

initialize_simps_projections HolderSpace (toFun → apply)

namespace HolderSpace

lemma HolderWith [PseudoEMetricSpace Y] (f : C^r(X; Y)) :
  ∃ C, HolderWith C r f := f.2

instance [SeminormedAddCommGroup Y] :
  Add C^r(X; Y) where
  add f g := ⟨f + g, _, f.HolderWith.choose_spec.add g.HolderWith.choose_spec⟩

instance [PseudoEMetricSpace Y] [Zero Y] : Zero C^r(X; Y) where
  zero := ⟨0, _, HolderWith.zero 0 _⟩

instance {α} [NormedDivisionRing α] [SeminormedAddCommGroup Y]
    [Module α Y] [BoundedSMul α Y] : SMul α C^r(X; Y) where
  smul c f := ⟨c • f, _, f.HolderWith.choose_spec.smul c⟩

def comp [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    (g : C^r(Y; Z)) (f : C^r(X; Y)) : C^(r * r)(X; Z) :=
  ⟨g ∘ f, _, g.HolderWith.choose_spec.comp f.HolderWith.choose_spec⟩

-- def Embedding {r s : ℝ≥0} (h : r ≤ s) :
--   HolderSpace X Y s → HolderSpace X Y r :=

end HolderSpace
