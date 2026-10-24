import OTSelector.MeasureTheory.MarkDependentHaarTranslation
import OTSelector.Reconstruction.MarkedStationaryValuePhysicalPairAnchorReadout
import OTSelector.Reconstruction.MarkedStationaryValueLegalScenePalmReadout

/-!
# Actual path-position windows have the same mean as source-position windows

The complete original edge mark determines its own spatial offset.  Campbell factorization
and Haar translation move the observation window to that path position without changing the
original scene, edge, paired clocks, displacement, or Palm law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The actual first-edge kernel readout, localized at a position displaced from its physical
source by a measurable function of its same complete original mark. -/
def legalMarkedPathWindowReadout {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q : ℕ) (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ)
    (h : (Fin q → ℝ) → ℝ) (f : PhysicalPairPalmMark (Fin q) → V)
    (s : LegalMarkedOptimalInputScene q) : V :=
  ∫ p, h (p.1 + d p.2) • f p.2 ∂physicalScenePairKernel s.1

/-- Vector-valued kernel Fubini for the actual measure bind. -/
theorem integral_bind_kernel_vector_eq_integral_integral
    {X Y V : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Measure X) (κ : Kernel X Y) {f : Y → V} (hi : Integrable f (P.bind κ)) :
    (∫ y, f y ∂P.bind κ) = ∫ x, ∫ y, f y ∂κ x ∂P := by
  change Integrable f (κ ∘ₘ P) at hi
  rw [Measure.comp_eq_comp_const_apply] at hi
  simpa only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply] using Kernel.integral_comp hi

/-- Every genuine original matching has an integrable actual displaced-window readout, whose
exact expectation is the spatial window mass times its own unchanged Palm readout. -/
theorem LegalWeightedStationaryPoissonMatching.pathWindowReadout_integrable_and_integral
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ} {f : PhysicalPairPalmMark (Fin q) → V}
    (hh : Integrable h (volume : Measure (Fin q → ℝ)))
    (hf : Integrable f (legalMarkedJointPalm q M.law)) :
    Integrable (legalMarkedPathWindowReadout q d h f)
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, legalMarkedPathWindowReadout q d h f s
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
        (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) •
          ∫ m, f m ∂legalMarkedJointPalm q M.law := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)) :=
    legalMarkedInputPairLaw q M.law
  let G : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → V :=
    fun p ↦ h (p.1 + d p.2) • f p.2
  have hi : Integrable G (P.bind physicalScenePairKernel) := by
    change Integrable G (physicalScenePairCampbell P)
    rw [M.campbell_eq_volume_prod_palm]
    exact integrable_markDependentAnchorTranslation _ d hd hh hf
  have hki : Integrable (fun s ↦ ∫ p, G p ∂physicalScenePairKernel s) P := by
    change Integrable G (physicalScenePairKernel ∘ₘ P) at hi
    rw [Measure.comp_eq_comp_const_apply] at hi
    simpa only [Kernel.const_apply] using hi.integral_comp
  have hscene := hki.comp_measurable measurable_fst
  have hmap := integral_map
    (μ := (M.law : Measure (LegalMarkedOptimalInputScene q))) measurable_fst.aemeasurable
    hki.aestronglyMeasurable
  have hFubini := integral_bind_kernel_vector_eq_integral_integral P physicalScenePairKernel hi
  have hvalue : (∫ p, G p ∂P.bind physicalScenePairKernel) =
      (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) •
        ∫ m, f m ∂legalMarkedJointPalm q M.law := by
    change (∫ p, G p ∂physicalScenePairCampbell P) = _
    rw [M.campbell_eq_volume_prod_palm]
    exact integral_markDependentAnchorTranslation _ d hd hh hf
  refine ⟨hscene, ?_⟩
  exact hmap.symm.trans (hFubini.symm.trans hvalue)

/-- The literal original path-position unit-window weight; its integral is one. -/
def legalMarkedUnitWindowWeight (q : ℕ) : (Fin q → ℝ) → ℝ :=
  (palmUnitCube (Fin q)).indicator (fun _ ↦ (1 : ℝ))

theorem integrable_legalMarkedUnitWindowWeight (q : ℕ) :
    Integrable (legalMarkedUnitWindowWeight q) (volume : Measure (Fin q → ℝ)) := by
  apply IntegrableOn.integrable_indicator
    (integrableOn_const (by rw [volume_palmUnitCube]; norm_num))
    (measurableSet_palmUnitCube (Fin q))

@[simp] theorem integral_legalMarkedUnitWindowWeight (q : ℕ) :
    (∫ x, legalMarkedUnitWindowWeight q x ∂(volume : Measure (Fin q → ℝ))) = 1 := by
  rw [legalMarkedUnitWindowWeight, integral_indicator (measurableSet_palmUnitCube (Fin q)),
    setIntegral_const, measureReal_def, volume_palmUnitCube]
  simp

/-- For each genuine original law, moving the source unit window to the actual marked path
position preserves exactly the whole vector mean of the same Palm observable. -/
theorem LegalWeightedStationaryPoissonMatching.pathUnitWindowReadout_integrable_and_integral
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (hd : Measurable d)
    {f : PhysicalPairPalmMark (Fin q) → V} (hf : Integrable f (legalMarkedJointPalm q M.law)) :
    Integrable (legalMarkedPathWindowReadout q d (legalMarkedUnitWindowWeight q) f)
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, legalMarkedPathWindowReadout q d (legalMarkedUnitWindowWeight q) f s
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ s, legalMarkedScenePalmReadout q f s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨hi, he⟩ := M.pathWindowReadout_integrable_and_integral d hd
    (integrable_legalMarkedUnitWindowWeight q) hf
  exact ⟨hi, by simpa only [integral_legalMarkedUnitWindowWeight, one_smul,
    integral_legalMarkedScenePalmReadout M.law hf] using he⟩

end OTSelector.Reconstruction
