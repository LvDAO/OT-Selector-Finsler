import OTSelector.Reconstruction.OriginalInputCountTailTrafficLtwo
import OTSelector.MeasureTheory.Integral.AERestriction
import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell

/-! The literal complete-path traffic has an exponential original-count-tail
L2 bound. Both the traffic and its contributor count use the same original scene. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Bounded original per-edge occupation and the actual scene contributor count
control the complete-path readout before any expectation or conditioning. -/
theorem originalCompletePath_traffic_le_of_count_ae
    {q : ℕ} (s : LegalMarkedOptimalInputScene q)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (h : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (V : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (hV : MeasurableSet V) {B N : ℝ≥0∞}
    (hzero : ∀ᵐ a ∂physicalScenePairKernel s.1, a ∉ V →
      (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0)
    (hsingle : ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict V,
      (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ B)
    (hcount : physicalScenePairKernel s.1 V ≤ N) :
    legalMarkedCompletePathTraffic q d h f s ≤ B * N := by
  calc
    _ = ∫⁻ a in V, (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume)
        ∂physicalScenePairKernel s.1 := (OTSelector.Probability.setLIntegral_eq_of_ae_zero_outside hV hzero).symm
    _ ≤ ∫⁻ _a in V, B ∂physicalScenePairKernel s.1 := lintegral_mono_ae hsingle
    _ = B * physicalScenePairKernel s.1 V := setLIntegral_const V B
    _ ≤ B * N := mul_le_mul_right hcount B

/-- The actual complete-path readout restricted to a large original source
count event has explicit exponential L2 decay. Only literal same-scene support,
per-edge occupation and count domination are used. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_countTail_completePath_ltwo_ae
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    {W : Set (LegalMarkedPhysicalPoint q)} (hW : MeasurableSet W)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hmass : ((volume : Measure (Fin q → ℝ)).prod α) W ≤ ENNReal.ofReal Λ)
    (V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    (hV : ∀ s, MeasurableSet (V s)) {B K : ℝ} (hB : 0 ≤ B)
    (hdata : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      K < ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal →
      (∀ᵐ a ∂physicalScenePairKernel s.1, a ∉ V s →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
      (∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B) ∧
      physicalScenePairKernel s.1 (V s) ≤
        (s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})) :
    let N := fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal
    let T := fun s : LegalMarkedOptimalInputScene q ↦
      (legalMarkedCompletePathTraffic q d h f s).toReal
    MemLp ({s | K < N s}.indicator T) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ({z | K < N z}.indicator T s) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        8 * B ^ 2 * Real.exp (Λ * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({s | K < N s}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B *
          Real.exp (Λ * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hNfin := (M.original_source_exp_moment_of_finite_intensity hW hfin
    (t := 0) (by norm_num)).1
  apply M.original_source_countTail_traffic_ltwo hW hΛ hmass
    (measurable_legalMarkedCompletePathTraffic d hd hh hf).ennreal_toReal.aestronglyMeasurable hB
  filter_upwards [hdata, hNfin] with s hs hn
  intro hK
  obtain ⟨hsupp, hsingle, hcount⟩ := hs hK
  have hb := originalCompletePath_traffic_le_of_count_ae s d h f (V s) (hV s) hsupp hsingle hcount
  have hpfin : ENNReal.ofReal B *
      (s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0}) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn.ne
  have hr := ENNReal.toReal_mono hpfin hb
  simpa only [abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB] using hr

/-- The actual complete-path readout restricted to a large original target
count event has explicit exponential L2 decay. Only literal same-scene support,
per-edge occupation and count domination are used. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_countTail_completePath_ltwo_ae
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    {W : Set (LegalMarkedPhysicalPoint q)} (hW : MeasurableSet W)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hmass : ((volume : Measure (Fin q → ℝ)).prod β) W ≤ ENNReal.ofReal Λ)
    (V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    (hV : ∀ s, MeasurableSet (V s)) {B K : ℝ} (hB : 0 ≤ B)
    (hdata : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      K < ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal →
      (∀ᵐ a ∂physicalScenePairKernel s.1, a ∉ V s →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
      (∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B) ∧
      physicalScenePairKernel s.1 (V s) ≤
        (s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})) :
    let N := fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal
    let T := fun s : LegalMarkedOptimalInputScene q ↦
      (legalMarkedCompletePathTraffic q d h f s).toReal
    MemLp ({s | K < N s}.indicator T) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ({z | K < N z}.indicator T s) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        8 * B ^ 2 * Real.exp (Λ * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({s | K < N s}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B *
          Real.exp (Λ * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hNfin := (M.original_target_exp_moment_of_finite_intensity hW hfin
    (t := 0) (by norm_num)).1
  apply M.original_target_countTail_traffic_ltwo hW hΛ hmass
    (measurable_legalMarkedCompletePathTraffic d hd hh hf).ennreal_toReal.aestronglyMeasurable hB
  filter_upwards [hdata, hNfin] with s hs hn
  intro hK
  obtain ⟨hsupp, hsingle, hcount⟩ := hs hK
  have hb := originalCompletePath_traffic_le_of_count_ae s d h f (V s) (hV s) hsupp hsingle hcount
  have hpfin : ENNReal.ofReal B *
      (s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1}) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hn.ne
  have hr := ENNReal.toReal_mono hpfin hb
  simpa only [abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB] using hr

end OTSelector.Reconstruction
