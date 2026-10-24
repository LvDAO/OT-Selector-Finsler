import OTSelector.Reconstruction.FinslerOriginalCanonicalPositiveTrafficTube
import OTSelector.Reconstruction.MarkedStationaryValuePhysicalPairAnchorReadout
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching

/-! Actual occupied traffic contributors retain the original source and target
counting marginals in physical pair coordinates. -/
open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The actual positive occupied edges, expressed by their unchanged source
anchor, original two clocks and full displacement. -/
def occupiedPairTrafficContributors (q : ℕ)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (s : LegalMarkedOptimalInputScene q) : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) :=
  (physicalPairAnchorHomeomorph q).symm ⁻¹'
    occupiedCompletePathTrafficContributors q d η f s

theorem measurableSet_occupiedPairTrafficContributors {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q) :
    MeasurableSet (occupiedPairTrafficContributors q d η f s) := by
  exact ((Measure.isClosed_support).measurableSet.inter
    (measurableSet_legalMarkedCompletePathContributors d hd hη hf)).preimage
      (physicalPairAnchorHomeomorph q).symm.measurable

/-- Removing unoccupied potential pairs loses no part of the literal actual
traffic. The conclusion is relative to the actual original pair kernel. -/
theorem ae_occupiedPairTrafficContributors_outside_zero {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (s : LegalMarkedOptimalInputScene q) :
    ∀ᵐ a ∂physicalScenePairKernel s.1, a ∉ occupiedPairTrafficContributors q d η f s →
      (∫⁻ r : ℝ, η (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0 := by
  rw [physicalScenePairKernel_apply]
  change ∀ᵐ a ∂Measure.map (physicalPairAnchorHomeomorph q).toMeasurableEquiv
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
    a ∉ occupiedPairTrafficContributors q d η f s →
      (∫⁻ r : ℝ, η (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0
  rw [← (physicalPairAnchorHomeomorph q).toMeasurableEquiv.map_ae]
  change ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
    physicalPairAnchor e ∉ occupiedPairTrafficContributors q d η f s → _ = 0
  filter_upwards [(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support_mem_ae] with e he hn
  have hn' : e ∉ legalMarkedCompletePathContributors q d η f := by
    intro hp
    apply hn
    change (physicalPairAnchorHomeomorph q).symm ((physicalPairAnchorHomeomorph q) e) ∈
      occupiedCompletePathTrafficContributors q d η f s
    simpa only [Homeomorph.symm_apply_apply, occupiedCompletePathTrafficContributors,
      mem_inter_iff] using And.intro he hp
  exact legalMarkedCompletePathContributors_outside_zero d η f e hn'

/-- The actual occupied contributor count is bounded by the same scene's
original source input count, using fullness of the original matching. -/
theorem occupiedPairTrafficContributors_source_count_le {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q)
    (hs : IsFullOriginalInputMatching q s)
    {W : Set (LegalMarkedPhysicalPoint q)} (hW : MeasurableSet W)
    (hsource : ∀ e ∈ occupiedCompletePathTrafficContributors q d η f s, e.1 ∈ W) :
    physicalScenePairKernel s.1 (occupiedPairTrafficContributors q d η f s) ≤
      (s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {(0 : Fin 2)}) := by
  rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
    (measurableSet_occupiedPairTrafficContributors d hd hη hf s)]
  have hpre : physicalPairAnchor ⁻¹' occupiedPairTrafficContributors q d η f s =
      occupiedCompletePathTrafficContributors q d η f s := by
    ext e
    change (physicalPairAnchorHomeomorph q).symm ((physicalPairAnchorHomeomorph q) e) ∈
      occupiedCompletePathTrafficContributors q d η f s ↔
        e ∈ occupiedCompletePathTrafficContributors q d η f s
    rw [Homeomorph.symm_apply_apply]
  rw [hpre]
  calc
    _ ≤ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.fst ⁻¹' W) := measure_mono hsource
    _ = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst W := by
      rw [Measure.fst, Measure.map_apply measurable_fst hW]
    _ = legalInputColorMeasure q s.2 0 W := by rw [hs.source_marginal]
    _ = _ := by
      rw [legalInputColorMeasure, Measure.map_apply measurable_fst hW,
        Measure.restrict_apply (hW.preimage measurable_fst)]
      congr 1

/-- The target version uses the original target input and preserves the
actual endpoint, without forcing a source confinement condition. -/
theorem occupiedPairTrafficContributors_target_count_le {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f) (s : LegalMarkedOptimalInputScene q)
    (hs : IsFullOriginalInputMatching q s)
    {W : Set (LegalMarkedPhysicalPoint q)} (hW : MeasurableSet W)
    (htarget : ∀ e ∈ occupiedCompletePathTrafficContributors q d η f s, e.2 ∈ W) :
    physicalScenePairKernel s.1 (occupiedPairTrafficContributors q d η f s) ≤
      (s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {(1 : Fin 2)}) := by
  rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
    (measurableSet_occupiedPairTrafficContributors d hd hη hf s)]
  have hpre : physicalPairAnchor ⁻¹' occupiedPairTrafficContributors q d η f s =
      occupiedCompletePathTrafficContributors q d η f s := by
    ext e
    change (physicalPairAnchorHomeomorph q).symm ((physicalPairAnchorHomeomorph q) e) ∈
      occupiedCompletePathTrafficContributors q d η f s ↔
        e ∈ occupiedCompletePathTrafficContributors q d η f s
    rw [Homeomorph.symm_apply_apply]
  rw [hpre]
  calc
    _ ≤ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.snd ⁻¹' W) := measure_mono htarget
    _ = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd W := by
      rw [Measure.snd, Measure.map_apply measurable_snd hW]
    _ = legalInputColorMeasure q s.2 1 W := by rw [hs.target_marginal]
    _ = _ := by
      rw [legalInputColorMeasure, Measure.map_apply measurable_fst hW,
        Measure.restrict_apply (hW.preimage measurable_fst)]
      congr 1

end OTSelector.Reconstruction
