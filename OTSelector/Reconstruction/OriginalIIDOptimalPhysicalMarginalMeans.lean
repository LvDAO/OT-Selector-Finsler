import OTSelector.Reconstruction.OriginalIIDOptimalMeanPlan

/-!
# Exact expected marginal readouts of the full original iid physical optimizer

The complete finite plan retains its two empirical marginals for every cost,
scale and tied optimizer. Correct individual sample marginals therefore give
exact population expectations; the literal independent product experiment
supplies these marginals internally through its coordinate projections.
-/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Ω] {n : ℕ}

/-- Source readouts of the unchanged optimizer have the exact original mean
whenever the individual source observations have their original marginal law. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_source_mean_of_marginals [NeZero n]
    (P : Measure Ω) (μ : Measure X)
    (x : Ω → Fin n → X) (y : Ω → Fin n → Y)
    (hx : ∀ i, MeasurePreserving (fun w ↦ x w i) P μ)
    (cost : X → Y → ℝ) (scale : ℝ) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, ∫⁻ p, f p.1 ∂originalIIDOptimalPhysicalPlan cost scale (x w, y w) ∂P) =
      ∫⁻ z, f z ∂μ := by
  have hread (w : Ω) :
      (∫⁻ p, f p.1 ∂originalIIDOptimalPhysicalPlan cost scale (x w, y w)) =
        ∫⁻ z, f z ∂empiricalMeasure (x w) := by
    rw [← lintegral_map hf measurable_fst, originalIIDOptimalPhysicalPlan_source]
  simp_rw [hread]
  exact lintegral_originalEmpiricalMeasure_mean P μ x hx f hf

/-- Target readouts retain their original mean even though the optimal
permutation depends on the whole sample and the cost can have arbitrary ties. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_target_mean_of_marginals [NeZero n]
    (P : Measure Ω) (ν : Measure Y)
    (x : Ω → Fin n → X) (y : Ω → Fin n → Y)
    (hy : ∀ i, MeasurePreserving (fun w ↦ y w i) P ν)
    (cost : X → Y → ℝ) (scale : ℝ) (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, ∫⁻ p, f p.2 ∂originalIIDOptimalPhysicalPlan cost scale (x w, y w) ∂P) =
      ∫⁻ z, f z ∂ν := by
  have hread (w : Ω) :
      (∫⁻ p, f p.2 ∂originalIIDOptimalPhysicalPlan cost scale (x w, y w)) =
        ∫⁻ z, f z ∂empiricalMeasure (y w) := by
    rw [← lintegral_map hf measurable_snd, originalIIDOptimalPhysicalPlan_target]
  simp_rw [hread]
  exact lintegral_originalEmpiricalMeasure_mean P ν y hy f hf

/-- The literal full independent two-color iid law gives the original source
expectation for every nonnegative measurable marginal readout. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_source_mean [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (scale : ℝ) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ξ, ∫⁻ p, f p.1 ∂originalIIDOptimalPhysicalPlan cost scale ξ
      ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) =
        ∫⁻ z, f z ∂μ :=
  lintegral_originalIIDOptimalPhysicalPlan_source_mean_of_marginals
    ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)))
    μ Prod.fst Prod.snd
    (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).comp measurePreserving_fst)
    cost scale f hf

/-- The original target expectation is exact on the same full iid experiment;
matching and optimal partner selection introduce no marginal bias. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_target_mean [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (scale : ℝ) (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ξ, ∫⁻ p, f p.2 ∂originalIIDOptimalPhysicalPlan cost scale ξ
      ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) =
        ∫⁻ z, f z ∂ν :=
  lintegral_originalIIDOptimalPhysicalPlan_target_mean_of_marginals
    ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)))
    ν Prod.fst Prod.snd
    (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ ν) i).comp measurePreserving_snd)
    cost scale f hf

/-- The expected mass of all original edges with source in a measurable set is
exactly its original source probability. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_source_event [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (scale : ℝ) {H : Set X} (hH : MeasurableSet H) :
    (∫⁻ ξ, originalIIDOptimalPhysicalPlan cost scale ξ (Prod.fst ⁻¹' H)
      ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) = μ H := by
  have hread (ξ : (Fin n → X) × (Fin n → Y)) :
      (originalIIDOptimalPhysicalPlan cost scale ξ) (Prod.fst ⁻¹' H) =
        ∫⁻ p, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.1
          ∂originalIIDOptimalPhysicalPlan cost scale ξ := by
    rw [← lintegral_map (measurable_const.indicator hH) measurable_fst]
    exact (Measure.map_apply measurable_fst hH).symm.trans (lintegral_indicator_one hH).symm
  simp_rw [hread]
  exact (lintegral_originalIIDOptimalPhysicalPlan_source_mean μ ν cost scale
    (H.indicator (fun _ ↦ 1)) (measurable_const.indicator hH)).trans
      (lintegral_indicator_one hH)

/-- The expected mass of all original edges with target in a measurable set is
exactly its original target probability, uniformly over costs and tie outcomes. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_target_event [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (scale : ℝ) {H : Set Y} (hH : MeasurableSet H) :
    (∫⁻ ξ, originalIIDOptimalPhysicalPlan cost scale ξ (Prod.snd ⁻¹' H)
      ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) = ν H := by
  have hread (ξ : (Fin n → X) × (Fin n → Y)) :
      (originalIIDOptimalPhysicalPlan cost scale ξ) (Prod.snd ⁻¹' H) =
        ∫⁻ p, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2
          ∂originalIIDOptimalPhysicalPlan cost scale ξ := by
    rw [← lintegral_map (measurable_const.indicator hH) measurable_snd]
    exact (Measure.map_apply measurable_snd hH).symm.trans (lintegral_indicator_one hH).symm
  simp_rw [hread]
  exact (lintegral_originalIIDOptimalPhysicalPlan_target_mean μ ν cost scale
    (H.indicator (fun _ ↦ 1)) (measurable_const.indicator hH)).trans
      (lintegral_indicator_one hH)

end OTSelector.Reconstruction
