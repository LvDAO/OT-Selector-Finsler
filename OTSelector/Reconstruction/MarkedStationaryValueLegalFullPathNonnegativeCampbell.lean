import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalPathWindowReadout
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Complete-path absolute traffic under the actual Campbell law

Tonelli and the actual marked-anchor translation identify the first moment of complete-path
traffic. No selected cloud law or displacement second moment is used.
-/

open Set Function Filter MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Nonnegative marked localization has the same exact Haar/Palm factorization after the
window is displaced by its own complete mark. -/
theorem lintegral_markDependentAnchorTranslation
    {q : ℕ} {Z : Type*} [MeasurableSpace Z] (η : Measure Z) [SFinite η]
    (d : Z → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : Z → ℝ≥0∞} (hh : Measurable h) (hf : Measurable f) :
    (∫⁻ p : (Fin q → ℝ) × Z, h (p.1 + d p.2) * f p.2
      ∂(volume : Measure (Fin q → ℝ)).prod η) =
      (∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) * ∫⁻ z, f z ∂η := by
  have hmp := measurePreserving_markDependentAnchorTranslation η d hd
  have hbase : Measurable (fun p : (Fin q → ℝ) × Z ↦ h p.1 * f p.2) :=
    (hh.comp measurable_fst).mul (hf.comp measurable_snd)
  have hi := lintegral_map (μ := (volume : Measure (Fin q → ℝ)).prod η)
    hbase hmp.measurable
  rw [hmp.map_eq] at hi
  exact hi.symm.trans (lintegral_prod_mul hh.aemeasurable hf.aemeasurable)

/-- Integrating each complete marked path in its original physical clock retains the exact
Haar/Palm factorization, for arbitrary jointly measurable original path offsets. -/
theorem lintegral_markDependentCompletePathTraffic
    {q : ℕ} {Z : Type*} [MeasurableSpace Z] (η : Measure Z) [SFinite η]
    (d : Z × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : Z × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) :
    (∫⁻ p : (Fin q → ℝ) × Z, ∫⁻ c : ℝ, h (p.1 + d (p.2, c)) * f (p.2, c)
      ∂volume ∂(volume : Measure (Fin q → ℝ)).prod η) =
      (∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂η := by
  have hG : Measurable (fun z : ((Fin q → ℝ) × Z) × ℝ ↦
      h (z.1.1 + d (z.1.2, z.2)) * f (z.1.2, z.2)) :=
    (hh.comp (measurable_fst.fst.add
      (hd.comp (measurable_fst.snd.prodMk measurable_snd)))).mul
      (hf.comp (measurable_fst.snd.prodMk measurable_snd))
  have hG' : Measurable (fun z : (Fin q → ℝ) × (Z × ℝ) ↦
      h (z.1 + d z.2) * f z.2) :=
    (hh.comp (measurable_fst.add (hd.comp measurable_snd))).mul
      (hf.comp measurable_snd)
  calc
    _ = ∫⁻ z : (Fin q → ℝ) × (Z × ℝ), h (z.1 + d z.2) * f z.2
        ∂(volume : Measure (Fin q → ℝ)).prod (η.prod volume) := by
      rw [lintegral_prod _ hG.lintegral_prod_right'.aemeasurable,
        lintegral_prod _ hG'.aemeasurable]
      apply lintegral_congr_ae
      filter_upwards [] with x
      exact (lintegral_prod _ (hG'.comp measurable_prodMk_left).aemeasurable).symm
    _ = _ := by
      rw [lintegral_markDependentAnchorTranslation (η.prod volume) d hd hh hf,
        lintegral_prod _ hf.aemeasurable]

/-- The literal complete-path nonnegative traffic in the actual same-scene first-edge kernel. -/
def legalMarkedCompletePathTraffic (q : ℕ)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (h : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (s : LegalMarkedOptimalInputScene q) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ c : ℝ, h (p.1 + d (p.2, c)) * f (p.2, c) ∂volume
    ∂physicalScenePairKernel s.1

/-- Complete-path traffic is a measurable actual scene observable. -/
theorem measurable_legalMarkedCompletePathTraffic {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) :
    Measurable (legalMarkedCompletePathTraffic q d h f) := by
  have hG : Measurable (fun z : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) × ℝ ↦
      h (z.1.1 + d (z.1.2, z.2)) * f (z.1.2, z.2)) :=
    (hh.comp (measurable_fst.fst.add
      (hd.comp (measurable_fst.snd.prodMk measurable_snd)))).mul
      (hf.comp (measurable_fst.snd.prodMk measurable_snd))
  exact hG.lintegral_prod_right'.lintegral_kernel.comp measurable_fst

/-- The full actual original scene traffic has exactly the same first moment as complete
original Palm occupation, times the physical kernel's spatial mass. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_completePathTraffic
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) :
    (∫⁻ s, legalMarkedCompletePathTraffic q d h f s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      (∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q M.law := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)) :=
    legalMarkedInputPairLaw q M.law
  let G : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞ :=
    fun p ↦ ∫⁻ c : ℝ, h (p.1 + d (p.2, c)) * f (p.2, c) ∂volume
  have hG : Measurable G := by
    have H : Measurable (fun z : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) × ℝ ↦
        h (z.1.1 + d (z.1.2, z.2)) * f (z.1.2, z.2)) :=
      (hh.comp (measurable_fst.fst.add
        (hd.comp (measurable_fst.snd.prodMk measurable_snd)))).mul
        (hf.comp (measurable_fst.snd.prodMk measurable_snd))
    exact H.lintegral_prod_right'
  have hi := Measure.lintegral_bind (m := P)
    (Kernel.measurable (physicalScenePairKernel : Kernel
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))).aemeasurable hG.aemeasurable
  have hm := lintegral_map (hG.lintegral_kernel (κ := physicalScenePairKernel))
    (measurable_fst : Measurable (Prod.fst : LegalMarkedOptimalInputScene q → _))
    (μ := (M.law : Measure (LegalMarkedOptimalInputScene q)))
  change (∫⁻ p, G p ∂physicalScenePairCampbell P) = _ at hi
  rw [M.campbell_eq_volume_prod_palm] at hi
  exact hm.symm.trans (hi.symm.trans
    (lintegral_markDependentCompletePathTraffic _ d hd hh hf))

end OTSelector.Reconstruction
