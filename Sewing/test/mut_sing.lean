import Mathlib

namespace MeasureTheory

open ENNReal Set Filter NNReal
open scoped Filter

variable {α} {_ : MeasurableSpace α} {μ ν : Measure α}

lemma Measure.inf_apply {s : Set α} (hs : MeasurableSet s) :
    (μ ⊓ ν) s = sInf {m | ∃ t, m = μ (t ∩ s) + ν (tᶜ ∩ s)} := by
  rw [← sInf_pair, Measure.sInf_apply hs, OuterMeasure.sInf_apply
    (image_nonempty.2 <| insert_nonempty μ {ν})]
  refine le_antisymm ?_ ?_
  · refine le_sInf fun m ⟨t, ht₁⟩ ↦ ?_
    subst ht₁
    set t' : ℕ → Set α := fun n ↦ if n = 0 then t ∩ s else if n = 1 then tᶜ ∩ s else ∅ with ht'
    refine (iInf₂_le t' fun x hx ↦ ?_).trans ?_
    · by_cases hxt : x ∈ t
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp [hx, hxt]
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp [hx, hxt]
    · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
      rw [tsum_eq_add_tsum_ite 0, tsum_eq_add_tsum_ite 1, if_neg zero_ne_one.symm,
        (tsum_eq_zero_iff ENNReal.summable).2 _, add_zero]
      · exact add_le_add (inf_le_left.trans <| by simp [ht']) (inf_le_right.trans <| by simp [ht'])
      · simp only [ite_eq_then]
        intro n hn₁ hn₀
        simp only [ht', if_neg hn₀, if_neg hn₁, measure_empty, iInf_pair, le_refl, inf_of_le_left]
  · refine le_iInf₂ fun t' ht' ↦ ?_
    simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
    set t := ⋃ n ∈ {k : ℕ | μ (t' k) ≤ ν (t' k)}, t' n with ht
    suffices : μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n)
    · refine le_trans (sInf_le ⟨t, rfl⟩) this
    have hle₁ : μ (t ∩ s) ≤ ∑' (n : {k | μ (t' k) ≤ ν (t' k)}), μ (t' n) :=
      (measure_mono inter_subset_left).trans <| measure_biUnion_le _ (to_countable _) _
    have hcap : tᶜ ∩ s ⊆ ⋃ n ∈ {k : ℕ | ν (t' k) < μ (t' k)}, t' n
    · simp_rw [ht, compl_iUnion]
      refine fun x ⟨hx₁, hx₂⟩ ↦ mem_iUnion₂.2 ?_
      rw [mem_iInter₂] at hx₁
      obtain ⟨i, hi⟩ := mem_iUnion.1 <| ht' hx₂
      refine ⟨i, ?_, hi⟩
      by_contra h
      simp only [mem_setOf_eq, not_lt] at h
      exact hx₁ i h hi
    have hle₂ : ν (tᶜ ∩ s) ≤ ∑' (n : {k | ν (t' k) < μ (t' k)}), ν (t' n) :=
      (measure_mono hcap).trans (measure_biUnion_le ν (to_countable {k | ν (t' k) < μ (t' k)}) _)
    refine (add_le_add hle₁ hle₂).trans ?_
    have heq : {k | μ (t' k) ≤ ν (t' k)} ∪ {k | ν (t' k) < μ (t' k)} = univ
    · ext k
      simp [le_or_lt]
    conv in ∑' (n : ℕ), μ (t' n) ⊓ ν (t' n) => rw [← tsum_univ, ← heq]
    rw [tsum_union_disjoint (f := fun n ↦ μ (t' n) ⊓ ν (t' n)) ?_ ENNReal.summable ENNReal.summable]
    · refine add_le_add (tsum_congr ?_).le (tsum_congr ?_).le
      · rw [Subtype.forall]
        intro n hn; simpa
      · rw [Subtype.forall]
        intro n hn
        rw [mem_setOf_eq] at hn
        simp [le_of_lt hn]
    · rw [Set.disjoint_iff]
      rintro k ⟨hk₁, hk₂⟩
      rw [mem_setOf_eq] at hk₁ hk₂
      exact False.elim <| hk₂.not_le hk₁

lemma aux₁ {s : Set ℝ≥0∞} (h : s.Nonempty) (hs : sInf s = 0) (n : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ x ∈ s, x < ε * (1 / 2 : ℝ≥0∞) ^ n := by
  refine exists_lt_of_csInf_lt h <| hs ▸ ENNReal.mul_pos ?_ (by simp)
  norm_cast
  exact hε.ne.symm

lemma aux₂ {x : ℝ≥0∞} {ε : ℝ≥0}
    (h : ∀ n : ℕ, x ≤ ε * (1 / 2) ^ n) : x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine ge_of_tendsto' (f := fun (n : ℕ) ↦ ε * (1 / 2 : ℝ≥0∞) ^ n) (x := atTop) ?_ h
  rw [← mul_zero (M₀ := ℝ≥0∞) (a := ε)]
  exact Tendsto.const_mul (tendsto_pow_atTop_nhds_zero_of_lt_one <| by norm_num) (Or.inr coe_ne_top)

lemma foo : ∑' (n : ℕ), (1 / 2 : ℝ≥0∞) ^ n = 2 := by
  simp only [one_div, tsum_geometric, one_sub_inv_two, inv_inv]

lemma aux₃ {ε : ℝ≥0∞} : ∑' (n : ℕ), ε * (1 / 2) ^ n = 2 * ε := by
  conv in 2 * ε => rw [← foo]
  rw [mul_comm]
  exact ENNReal.tsum_mul_left

lemma Disjoint.mutuallySingular' (h : Disjoint μ ν) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ s, μ s = 0 ∧ ν sᶜ ≤ 2 * ε := by
  have h₁ : (μ ⊓ ν) univ = 0 := le_bot_iff.1 (h (inf_le_left (b := ν)) inf_le_right) ▸ rfl
  simp_rw [Measure.inf_apply MeasurableSet.univ, inter_univ] at h₁
  have h₂ : ∀ n : ℕ, ∃ t, μ t + ν tᶜ < ε * (1 / 2) ^ n := by
    intro n
    have hn : {m | ∃ t, m = μ t + ν tᶜ}.Nonempty := ⟨ν univ, ∅, by simp⟩
    obtain ⟨m, ⟨t, ht₁, rfl⟩, hm₂⟩ := aux₁ hn h₁ n hε
    exact ⟨t, hm₂⟩
  choose t ht₂ using h₂
  refine ⟨⋂ n, t n, ?_, ?_⟩
  · refine aux₂ <| fun n ↦ ((measure_mono <| iInter_subset_of_subset n fun _ ht ↦ ht).trans
      (le_add_right le_rfl)).trans (ht₂ n).le
  · rw [compl_iInter]
    refine (measure_iUnion_le _).trans (aux₃ ▸ ?_)
    exact tsum_le_tsum (fun n ↦ (le_add_left le_rfl).trans (ht₂ n).le)
      ENNReal.summable ENNReal.summable

lemma Disjoint.mutuallySingular'' (h : Disjoint μ ν) (n : ℕ) :
    ∃ s, μ s = 0 ∧ ν sᶜ ≤ (1 / 2) ^ n := by
  have := Disjoint.mutuallySingular' h ((1 / 2) ^ (n + 1)) <| pow_pos (by simp) (n + 1)
  convert this
  push_cast
  rw [pow_succ, ← mul_assoc, mul_comm, ← mul_assoc]
  norm_cast
  rw [div_mul_cancel₀, one_mul]
  · push_cast
    simp
  · simp

lemma Disjoint.mutuallySingular (h : Disjoint μ ν) : μ ⟂ₘ ν := by
  choose s hs₂ hs₃ using Disjoint.mutuallySingular'' h
  refine Measure.MutuallySingular.mk (t := (⋃ n, s n)ᶜ) (measure_iUnion_null hs₂) ?_ ?_
  · rw [compl_iUnion]
    refine aux₂ (ε := 1) <| fun n ↦ ?_
    rw [ENNReal.coe_one, one_mul]
    exact (measure_mono <| iInter_subset_of_subset n fun _ ht ↦ ht).trans (hs₃ n)
  · rw [union_compl_self]

end MeasureTheory
