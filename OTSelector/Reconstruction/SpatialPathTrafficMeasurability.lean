import OTSelector.Reconstruction.CompletePathTrafficReroot

/-! # Spatially observed original path traffic is jointly measurable -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The literal traffic restricted to the same original anchor set is jointly
Borel in observation point and original scene. -/
theorem measurable_restricted_pairClockTraffic_shift_joint {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A) :
    Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      ∫⁻ a in A, ∫⁻ c : ℝ, h (a.1 + d (a.2, c) - p.1) * f (a.2, c) ∂volume
        ∂physicalScenePairKernel p.2.1) := by
  classical
  let κ : Kernel ((Fin q → ℝ) × LegalMarkedOptimalInputScene q)
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) := physicalScenePairKernel.comap
    (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦ p.2.1) measurable_snd.fst
  let H := fun z : ((Fin q → ℝ) × LegalMarkedOptimalInputScene q) ×
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) ↦
    ∫⁻ c : ℝ, h (z.2.1 + d (z.2.2, c) - z.1.1) * f (z.2.2, c) ∂volume
  have hH : Measurable H := by
    have hm : Measurable (fun b : (((Fin q → ℝ) × LegalMarkedOptimalInputScene q) ×
        ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) × ℝ ↦
      h (b.1.2.1 + d (b.1.2.2, b.2) - b.1.1.1) * f (b.1.2.2, b.2)) := (hh.comp ((measurable_fst.snd.fst.add
      (hd.comp (measurable_fst.snd.snd.prodMk measurable_snd))).sub
        measurable_fst.fst.fst)).mul
      (hf.comp (measurable_fst.snd.snd.prodMk measurable_snd))
    exact hm.lintegral_prod_right'
  let B : Set (((Fin q → ℝ) × LegalMarkedOptimalInputScene q) ×
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) := Prod.snd ⁻¹' A
  have hmasked : Measurable (B.indicator H) := hH.indicator (hA.preimage measurable_snd)
  have hread := hmasked.lintegral_kernel_prod_right' (κ := κ)
  convert hread using 1
  ext p
  rw [← lintegral_indicator hA]
  apply lintegral_congr_ae
  filter_upwards [] with a
  by_cases ha : a ∈ A <;> simp [B, Set.indicator, ha, H]

/-- The full original traffic is jointly measurable in the same physical
observation point and same joint original scene. -/
theorem measurable_legalMarkedCompletePathTraffic_shift_joint {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) :
    Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      legalMarkedCompletePathTraffic q d (fun x ↦ h (x - p.1)) f p.2) := by
  simpa only [Measure.restrict_univ, legalMarkedCompletePathTraffic] using
    measurable_restricted_pairClockTraffic_shift_joint d hd hh hf MeasurableSet.univ

end OTSelector.Reconstruction
