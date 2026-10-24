import OTSelector.Reconstruction.OriginalReserveMainExperimentCapacitySubset

/-! Actual reserve deletion capacities fail only with quadratically negligible probability at every positive intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The actual summed full-block discrepancy exceeds any positive block's
true quarter-mean reserve margin with quadratically negligible probability. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalMainReservePositiveBlockDiscrepancyFailure
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ : ℝ} (hθ : 0 < θ) (G : OriginalStageClockGrid)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ R^2 * (originalMainReserveExperimentLaw Q
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        (originalMainReservePositiveBlockDiscrepancyFailure α β b θ R G)) atTop (𝓝 0) := by
  let B := ↥(G.positiveSlabBlocks α β)
  let P : ℝ → Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) := fun R ↦
    originalMainReserveExperimentLaw Q
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)
  let bad : B → ℝ → Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :=
    fun item R ↦ {p |
      (θ * min (α.real (G.sourceCell (G.firstBlockClass item.val)))
        (β.real (G.targetCell (G.lastBlockClass item.val))) / 4) *
          volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
            originalFullClockSlabDiscrepancy (α := α) (β := β) G
              (originalCenteredPhysicalCubeRegion b (2 * R)) p}
  have hi (item : B) : Tendsto (fun R ↦ R^2 * (P R).real (bad item R)) atTop (𝓝 0) := by
    have hm := G.positiveSlabBlock_extreme_class_masses hmono hH item.val item.property
    have hh := Q.tendsto_originalFullClockSlabDiscrepancy_budgetFailure_quadratic_probability_zero
      hq b (Real.toNNReal θ) G
      (r := θ * min (α.real (G.sourceCell (G.firstBlockClass item.val)))
        (β.real (G.targetCell (G.lastBlockClass item.val))) / 4)
      (div_pos (mul_pos hθ (lt_min hm.1 hm.2)) (by norm_num))
    simpa only [P, bad] using hh
  have hu := tendsto_quadratic_finite_union_measureReal_zero P bad hi
  convert hu using 1
  funext R
  apply congrArg (fun A : Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) ↦
    R^2 * (P R).real A)
  ext p
  constructor
  · rintro ⟨block, hb, hp⟩
    exact ⟨⟨block, hb⟩, hp⟩
  · rintro ⟨item, hp⟩
    exact ⟨item.val, item.property, hp⟩

/-- All genuine source and target deletion capacities hold simultaneously
on the original unit-main plus theta-volume reserve law. Every theta greater
than zero is allowed. Counts, class positivity, zero blocks and fluctuation
rates are produced internally from the original experiment. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalMainReserveClockSlabCapacityFailure
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ : ℝ} (hθ : 0 < θ) (G : OriginalStageClockGrid)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ R^2 * (originalMainReserveExperimentLaw Q
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        (originalMainReserveClockSlabCapacityFailure α β b R G)) atTop (𝓝 0) := by
  have hs := tendsto_originalRawReservePositiveBlockExtremeFailure_prod
    hq α β b hθ G hmono hH (fun _ ↦ Q.law)
  have ht := Q.tendsto_originalMainReservePositiveBlockDiscrepancyFailure hq b hθ G hmono hH
  have hu := hs.add ht
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall fun R ↦
    mul_nonneg (sq_nonneg R) measureReal_nonneg) (Eventually.of_forall fun R ↦ ?_) hu
  let P : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :=
    originalMainReserveExperimentLaw Q
    (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)
  have : IsProbabilityMeasure P := by unfold P originalMainReserveExperimentLaw; infer_instance
  have hm : P (originalMainReserveClockSlabCapacityFailure α β b R G) ≤
      P ({p | p.2 ∈ originalRawReservePositiveBlockExtremeFailure α β b θ R G} ∪
        originalMainReservePositiveBlockDiscrepancyFailure α β b θ R G) :=
    measure_mono_ae (Q.ae_originalMainReserve_capacityFailure_subset b hθ.le G)
  have hp := (ENNReal.toReal_mono (measure_ne_top P _) hm).trans
    (measureReal_union_le (μ := P)
      {p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ |
        p.2 ∈ originalRawReservePositiveBlockExtremeFailure α β b θ R G}
      (originalMainReservePositiveBlockDiscrepancyFailure α β b θ R G))
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg R)).trans_eq (by rw [mul_add]; rfl)

end OTSelector.Reconstruction
