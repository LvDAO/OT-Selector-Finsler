import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell

/-!
# Exact original Campbell counts for fixed source, target, and path windows

The displacement of the observation window may depend on the entire original
paired mark. The law of selected ports is never treated as a Poisson law.
-/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The mean of the actual unchanged pair kernel is exactly the original Haar/Palm measure. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_original_pairKernel_apply
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A) :
    (∫⁻ s, physicalScenePairKernel s.1 A ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
      ((volume : Measure (Fin q → ℝ)).prod (legalMarkedJointPalm q Q.law)) A := by
  let P := legalMarkedInputPairLaw q Q.law
  have hmap := lintegral_map (Kernel.measurable_coe physicalScenePairKernel hA)
    (measurable_fst : Measurable (Prod.fst : LegalMarkedOptimalInputScene q → _))
    (μ := (Q.law : Measure (LegalMarkedOptimalInputScene q)))
  calc
    _ = ∫⁻ s, physicalScenePairKernel s A ∂(P : Measure _) := hmap.symm
    _ = physicalScenePairCampbell (P : Measure _) A := by
      rw [physicalScenePairCampbell, Measure.bind_apply hA (Kernel.measurable _).aemeasurable]
    _ = _ := by rw [Q.campbell_eq_volume_prod_palm]

/-- Every fixed original marked window has its exact actual expected count, even
when its position is the target or a point on the same marked complete path. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_original_markedWindow_count
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (hd : Measurable d)
    {W : Set (Fin q → ℝ)} {B : Set (PhysicalPairPalmMark (Fin q))}
    (hW : MeasurableSet W) (hB : MeasurableSet B) :
    (∫⁻ s, physicalScenePairKernel s.1 {a | a.1 + d a.2 ∈ W ∧ a.2 ∈ B}
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
      volume W * legalMarkedJointPalm q Q.law B := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  have hmp := measurePreserving_markDependentAnchorTranslation (legalMarkedJointPalm q Q.law) d hd
  have hA := (hW.prod hB).preimage hmp.measurable
  have hA' : MeasurableSet {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) |
      a.1 + d a.2 ∈ W ∧ a.2 ∈ B} := by
    convert hA using 1
    ext a
    rfl
  rw [Q.lintegral_original_pairKernel_apply hA']
  change ((volume : Measure (Fin q → ℝ)).prod (legalMarkedJointPalm q Q.law))
    ((fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦ (a.1 + d a.2, a.2)) ⁻¹' (W ×ˢ B)) = _
  rw [← Measure.map_apply hmp.measurable (hW.prod hB), hmp.map_eq, Measure.prod_prod]

/-- Any actual true-Palm full-mark property holds on the same original pair kernel
for almost every scene; no conditioning of the Palm measure is asserted. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_original_pairKernel_of_palm
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    (hae : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m ∈ B) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ a ∂physicalScenePairKernel s.1, a.2 ∈ B := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  have hz : legalMarkedJointPalm q Q.law Bᶜ = 0 := by
    change legalMarkedJointPalm q Q.law {m | ¬m ∈ B} = 0
    exact ae_iff.mp hae
  have hzero : (∫⁻ s, physicalScenePairKernel s.1 (univ ×ˢ Bᶜ)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) = 0 := by
    rw [Q.lintegral_original_pairKernel_apply (MeasurableSet.univ.prod hB.compl),
      Measure.prod_prod, hz, mul_zero]
  have hs := (lintegral_eq_zero_iff
    ((Kernel.measurable_coe physicalScenePairKernel (MeasurableSet.univ.prod hB.compl)).comp
      measurable_fst)).mp hzero
  filter_upwards [hs] with s hs
  apply ae_iff.mpr
  have heq : {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) | ¬a.2 ∈ B} = univ ×ˢ Bᶜ := by
    ext a
    simp
  rwa [heq]

end OTSelector.Reconstruction
