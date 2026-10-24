import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockCounts
import OTSelector.Reconstruction.OriginalReserveUnitInputClockBlockCounts
import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockSelection
import OTSelector.Probability.MarkedTilePressureLimit

/-! Zero law blocks have zero actual main/reserve populations and zero deletion requests. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- Actual zero-mass blocks have zero original populations and zero requested
excess on the same full joining; no positive reserve capacity is needed. -/
theorem ae_zeroMass_blockCounts (hq : 0 < q) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hα : α S = 0) (hβ : β T = 0) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 = 0 ∧
      originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
          (originalReserveMainSamplerReadout q θ hθ1 p.1).1 = 0 ∧
      originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) S = 0 ∧
      originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) T = 0 ∧
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1 S T
        (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) = 0 ∧
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0 T S
        (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p)) = 0 := by
  have hlaw := X.hasLaw_unitBlockCount_pair hq (isCompact_originalStagePhysicalCube b (2 * R)) hS hT
  simp only [hα, hβ, ENNReal.toNNReal_zero, mul_zero, ProbabilityTheory.poissonMeasure_zero, Measure.dirac_prod, Measure.map_dirac] at hlaw
  have hz := hlaw.ae_eq_of_dirac
  filter_upwards [hz, X.ae_clockBlock_counts hS, X.ae_clockBlock_counts hT] with p hp hs ht
  have hsU := congrArg Prod.fst hp
  have htU := congrArg Prod.snd hp
  have hs' := (hs 0).2
  have ht' := (ht 1).2
  simp only [↓reduceIte] at hs'
  simp only [one_ne_zero, ↓reduceIte] at ht'
  obtain ⟨hsM, hsR⟩ := Nat.add_eq_zero_iff.mp (hs'.symm.trans hsU)
  obtain ⟨htM, htR⟩ := Nat.add_eq_zero_iff.mp (ht'.symm.trans htU)
  refine ⟨hsM, htM, hsR, htR, ?_, ?_⟩
  · change (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
        (originalReserveMainSamplerReadout q θ hθ1 p.1).1 +
      originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) S) -
      (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
        (originalReserveMainSamplerReadout q θ hθ1 p.1).1 +
      originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) T) = 0
    simp only [hsM, htM, hsR, htR, zero_add, Nat.sub_self]
  · change (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) T 1
        (originalReserveMainSamplerReadout q θ hθ1 p.1).1 +
      originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) T) -
      (originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2 * R)) S 0
        (originalReserveMainSamplerReadout q θ hθ1 p.1).1 +
      originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) S) = 0
    simp only [hsM, htM, hsR, htR, zero_add, Nat.sub_self]

/-- The discarded actual Hall blocks supply both zero law masses internally,
so every actual requested deletion is zero, without a positive extreme class. -/
theorem ae_zeroClockSlabBlock_excess (hq : 0 < q) (G : OriginalStageClockGrid)
    (block : G.ClockSlabBlock α β) (hb : block ∉ G.positiveSlabBlocks α β) :
    ∀ᵐ p ∂(X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 0 1
        (G.sourceBlockCell α β block) (G.targetBlockCell α β block)
        (originalReserveExcessInputAux (originalReserveUnitSourceSamplerView q θ hθ1 p)) = 0 ∧
      originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2 * R)) 1 0
        (G.targetBlockCell α β block) (G.sourceBlockCell α β block)
        (originalReserveExcessInputAux (originalReserveUnitTargetSamplerView q θ hθ1 p)) = 0 := by
  filter_upwards [X.ae_zeroMass_blockCounts hq (G.blockCells_measurable block).1
    (G.blockCells_measurable block).2
    (Measure.restrict_eq_zero.mp (G.zeroSlabBlock_restrict block hb).1)
    (Measure.restrict_eq_zero.mp (G.zeroSlabBlock_restrict block hb).2)] with p hp
  exact hp.2.2.2.2

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
