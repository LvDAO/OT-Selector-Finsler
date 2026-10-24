import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawActualExcess

/-! One actual join of the original main scene and both independent reserve colors. -/
open Set Function MeasureTheory
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- One joint experiment retaining the same original main scene and both independently
sampled original reserve observations. The parameter is each actual reserve mean count. -/
def originalMainReserveExperimentLaw
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0) :
    Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :=
  (Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (twoMarkedCloudLaw q ℝ ℝ α β rate)

/-- Reorder the same three observations for source-reserve factorization. -/
def originalSourceReserveExperimentSplice
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :
    (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ :=
  ((p.1, p.2.2), p.2.1)

/-- Reorder the same observations for target-reserve factorization. -/
def originalTargetReserveExperimentSplice
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :
    (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ :=
  ((p.1, p.2.1), p.2.2)

/-- The source view is the actual same join experiment, with the unchanged original main
scene and target reserve as auxiliary data independent of the source reserve observation. -/
theorem map_originalSourceReserveExperimentSplice
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0) :
    (originalMainReserveExperimentLaw Q rate).map originalSourceReserveExperimentSplice =
      (((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (markedPoissonLaw q ℝ β rate)).prod (markedPoissonLaw q ℝ α rate)) := by
  unfold originalMainReserveExperimentLaw twoMarkedCloudLaw
  rw [show originalSourceReserveExperimentSplice =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap from rfl,
    ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      (measurable_id.prodMap measurable_swap),
    ← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id, Measure.prod_swap]
  have h := Measure.prodAssoc_prod (μ := (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (ν := markedPoissonLaw q ℝ β rate) (τ := markedPoissonLaw q ℝ α rate)
  conv_lhs => rw [← h]
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable MeasurableEquiv.prodAssoc.measurable]
  simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]

/-- The target view is the same join experiment with the unchanged main and source reserve
retained as auxiliary data. No second scene or alternative reserve experiment is introduced. -/
theorem map_originalTargetReserveExperimentSplice
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0) :
    (originalMainReserveExperimentLaw Q rate).map originalTargetReserveExperimentSplice =
      (((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (markedPoissonLaw q ℝ α rate)).prod (markedPoissonLaw q ℝ β rate)) := by
  have h := Measure.prodAssoc_prod (μ := (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (ν := markedPoissonLaw q ℝ α rate) (τ := markedPoissonLaw q ℝ β rate)
  unfold originalMainReserveExperimentLaw twoMarkedCloudLaw
  have hm : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  rw [← h, Measure.map_map hm MeasurableEquiv.prodAssoc.measurable]
  change Measure.map id (((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod
    (markedPoissonLaw q ℝ α rate)).prod (markedPoissonLaw q ℝ β rate)) = _
  exact Measure.map_id

end OTSelector.Reconstruction
