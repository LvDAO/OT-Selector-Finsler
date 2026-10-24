import OTSelector.Reconstruction.OriginalCountTailCompletePathAELtwo
import OTSelector.MeasureTheory.Lp.NonnegativeSquareReadout

/-! The actual count-good event converts a physical per-edge occupation bound
and the same original Campbell first moment into a true traffic L2 bound. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Actual contributor count and bounded original one-edge occupation control
the good-event traffic square by its own first moment. AE zero outside the
contributors is enough; unused potential pairs carry no restriction. -/
theorem LegalWeightedStationaryPoissonMatching.goodEvent_completePath_traffic_memLp_two_of_count_ae
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (hfinite : (∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q M.law) ≠ ∞)
    {Bad : Set (LegalMarkedOptimalInputScene q)} (hBad : MeasurableSet Bad)
    (V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    (hV : ∀ s, MeasurableSet (V s)) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hdata : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ Bad →
      (∀ᵐ a ∂physicalScenePairKernel s.1, a ∉ V s →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
      (∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B) ∧
      physicalScenePairKernel s.1 (V s) ≤ ENNReal.ofReal K) :
    MemLp (Badᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic q d h f s).toReal)) 2
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, (Badᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic q d h f z).toReal) s) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ (B * K) *
      ((∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q M.law)).toReal := by
  have hm := measurable_legalMarkedCompletePathTraffic d hd hh hf
  have hsq : (∫⁻ s, Badᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic q d h f z) ^ 2) s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      (ENNReal.ofReal B * ENNReal.ofReal K) *
        ((∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
          (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q M.law)) := by
    calc
      _ ≤ ∫⁻ s, (ENNReal.ofReal B * ENNReal.ofReal K) * legalMarkedCompletePathTraffic q d h f s
          ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
        apply lintegral_mono_ae
        filter_upwards [hdata] with s hs
        by_cases hbad : s ∈ Bad
        · rw [indicator_of_notMem (show s ∉ Badᶜ from fun h ↦ h hbad)]
          exact bot_le
        · rw [indicator_of_mem (show s ∈ Badᶜ from hbad)]
          obtain ⟨hz, hu, hn⟩ := hs hbad
          have hb := originalCompletePath_traffic_le_of_count_ae s d h f (V s) (hV s) hz hu hn
          simpa only [pow_two, mul_comm] using mul_le_mul_right hb (legalMarkedCompletePathTraffic q d h f s)
      _ = _ := by rw [lintegral_const_mul _ hm, M.lintegral_completePathTraffic d hd hh hf]
  have hright := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (ENNReal.ofReal_ne_top (r := K))) hfinite
  have hL2 := OTSelector.Probability.memLp_two_of_goodEvent_lintegral_sq_le
    (M.law : Measure (LegalMarkedOptimalInputScene q)) hm hBad hright hsq
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, ENNReal.toReal_ofReal hK] using hL2

end OTSelector.Reconstruction
