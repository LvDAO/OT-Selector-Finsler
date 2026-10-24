import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-! Averaging the actual iid finite optimizer gives a coupling of the original
populations. The proof keeps both complete empirical marginals and the exact
physical energy readout, before any local root or core restriction. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Ω] {n : ℕ}

/-- Correct individual sample marginals suffice for the exact empirical mean;
no independence premise is necessary at this intermediate step. -/
theorem lintegral_originalEmpiricalMeasure_mean [NeZero n]
    (P : Measure Ω) (μ : Measure X) (x : Ω → Fin n → X)
    (hx : ∀ i, MeasurePreserving (fun w ↦ x w i) P μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, ∫⁻ z, f z ∂empiricalMeasure (x w) ∂P) = ∫⁻ z, f z ∂μ := by
  simp_rw [lintegral_originalEmpiricalMeasure _ f hf]
  have hsum : Measurable (fun w : Ω ↦ ∑ i, f (x w i)) :=
    Finset.measurable_sum _ (fun i _ ↦ hf.comp (hx i).measurable)
  rw [lintegral_const_mul _ hsum, lintegral_finsetSum]
  · simp_rw [(hx _).lintegral_comp hf]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, ENNReal.inv_mul_cancel
      (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n), one_mul]
  · intro i _
    exact hf.comp (hx i).measurable

/-- The actual mean physical plan of the unchanged two-color iid experiment. -/
def originalIIDOptimalMeanPlan (μ : Measure X) (ν : Measure Y)
    (cost : X → Y → ℝ) (scale : ℝ) (n : ℕ) : Measure (X × Y) :=
  ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))).bind
    (originalIIDOptimalPhysicalPlan cost scale)

/-- Nonnegative physical readouts keep the full original sample expectation. -/
theorem lintegral_originalIIDOptimalMeanPlan
    (μ : Measure X) (ν : Measure Y)
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℝ) (n : ℕ) (e : X × Y → ℝ≥0∞) (he : Measurable e) :
    (∫⁻ p, e p ∂originalIIDOptimalMeanPlan μ ν cost scale n) =
      ∫⁻ ξ, ∫⁻ p, e p ∂originalIIDOptimalPhysicalPlan cost scale ξ
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)) :=
  Measure.lintegral_bind (measurable_originalIIDOptimalPhysicalPlan cost hcost scale).aemeasurable
    he.aemeasurable

/-- The original physical source population is the exact mean source
marginal. No deletion or selected-window conditioning is performed. -/
theorem originalIIDOptimalMeanPlan_source [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) (scale : ℝ) :
    (originalIIDOptimalMeanPlan μ ν cost scale n).map Prod.fst = μ := by
  apply Measure.ext
  intro H hH
  let f : X → ℝ≥0∞ := H.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hH
  have hread (ξ : (Fin n → X) × (Fin n → Y)) :
      (originalIIDOptimalPhysicalPlan cost scale ξ) (Prod.fst ⁻¹' H) =
        ∫⁻ x, f x ∂empiricalMeasure ξ.1 := by
    have hm := congrArg (fun σ : Measure X ↦ σ H)
      (originalIIDOptimalPhysicalPlan_source cost scale ξ)
    rw [Measure.map_apply measurable_fst hH] at hm
    exact hm.trans (lintegral_indicator_one hH).symm
  rw [Measure.map_apply measurable_fst hH]
  change (((Measure.pi (fun _ : Fin n ↦ μ)).prod
    (Measure.pi (fun _ : Fin n ↦ ν))).bind
    (originalIIDOptimalPhysicalPlan cost scale)) (Prod.fst ⁻¹' H) = μ H
  rw [Measure.bind_apply (hH.preimage measurable_fst)
    (measurable_originalIIDOptimalPhysicalPlan cost hcost scale).aemeasurable]
  simp_rw [hread]
  exact (lintegral_originalEmpiricalMeasure_mean (n := n)
    ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) μ
    (fun ξ : (Fin n → X) × (Fin n → Y) ↦ ξ.1)
    (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).comp measurePreserving_fst) f hf).trans
      (lintegral_indicator_one hH)

/-- The original physical target population is the exact mean target
marginal, including all ties of the chosen optimal finite matching. -/
theorem originalIIDOptimalMeanPlan_target [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) (scale : ℝ) :
    (originalIIDOptimalMeanPlan μ ν cost scale n).map Prod.snd = ν := by
  apply Measure.ext
  intro H hH
  let f : Y → ℝ≥0∞ := H.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hH
  have hread (ξ : (Fin n → X) × (Fin n → Y)) :
      (originalIIDOptimalPhysicalPlan cost scale ξ) (Prod.snd ⁻¹' H) =
        ∫⁻ y, f y ∂empiricalMeasure ξ.2 := by
    have hm := congrArg (fun σ : Measure Y ↦ σ H)
      (originalIIDOptimalPhysicalPlan_target cost scale ξ)
    rw [Measure.map_apply measurable_snd hH] at hm
    exact hm.trans (lintegral_indicator_one hH).symm
  rw [Measure.map_apply measurable_snd hH]
  change (((Measure.pi (fun _ : Fin n ↦ μ)).prod
    (Measure.pi (fun _ : Fin n ↦ ν))).bind
    (originalIIDOptimalPhysicalPlan cost scale)) (Prod.snd ⁻¹' H) = ν H
  rw [Measure.bind_apply (hH.preimage measurable_snd)
    (measurable_originalIIDOptimalPhysicalPlan cost hcost scale).aemeasurable]
  simp_rw [hread]
  exact (lintegral_originalEmpiricalMeasure_mean (n := n)
    ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ν
    (fun ξ : (Fin n → X) × (Fin n → Y) ↦ ξ.2)
    (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ ν) i).comp measurePreserving_snd) f hf).trans
      (lintegral_indicator_one hH)

end OTSelector.Reconstruction
