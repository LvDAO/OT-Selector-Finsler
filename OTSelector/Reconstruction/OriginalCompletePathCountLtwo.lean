import OTSelector.Reconstruction.OriginalCompletePathCountSquare
import OTSelector.Reconstruction.OriginalCompletePathGoodEventLtwo

/-! Actual contributor-count bounds yield the original full-path good-event L2
bound after Campbell/Tonelli; no pre-assumed traffic-square oracle is used. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The count, single-edge bound and actual momentum weight give the true
Palm occupation bound for the original complete-path traffic on the good event. -/
theorem LegalWeightedStationaryPoissonMatching.goodEvent_completePath_traffic_memLp_two_of_count
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ≥0∞) (hp : Measurable p) (hpfin : ∀ m, p m ≠ ∞)
    (hfinite : (∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, p m * f (m, c) ∂volume ∂legalMarkedJointPalm q M.law) ≠ ∞)
    {A : Set (LegalMarkedOptimalInputScene q)} (hA : MeasurableSet A)
    (V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    (W : LegalMarkedOptimalInputScene q → ℝ≥0∞) (hW : ∀ s, W s ≠ ∞)
    {B K C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsupport : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ A →
      (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
        ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume).support ⊆ V s)
    (huB : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ A →
      ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B)
    (hcount : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ A →
      physicalScenePairKernel s.1 (V s) ≤ ENNReal.ofReal K * W s)
    (hweight : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ A →
      ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s), W s ≤ ENNReal.ofReal C * p a.2) :
    MemLp (Aᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic q d h f s).toReal)) 2
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, (Aᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic q d h f s).toReal) s) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ (B * K * C) *
        ((∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
          (∫⁻ m, ∫⁻ c : ℝ, p m * f (m, c) ∂volume ∂legalMarkedJointPalm q M.law)).toReal := by
  have hpf : Measurable (fun m : PhysicalPairPalmMark (Fin q) × ℝ ↦ p m.1 * f m) :=
    (hp.comp measurable_fst).mul hf
  have hm := measurable_legalMarkedCompletePathTraffic d hd hh hpf
  have hmean : (∫⁻ s, legalMarkedCompletePathTraffic q d h (fun m ↦ p m.1 * f m) s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≠ ∞ := by
    rwa [M.lintegral_completePathTraffic d hd hh hpf]
  apply M.goodEvent_completePath_traffic_memLp_two d hd hh hpf hfinite
    (measurable_legalMarkedCompletePathTraffic d hd hh hf).ennreal_toReal.aestronglyMeasurable
    hA (mul_nonneg (mul_nonneg hB hK) hC)
  filter_upwards [ae_lt_top hm hmean, hsupport, huB, hcount, hweight] with s hsfin hsupp hsingle hnum hw
  intro hsA
  have hsq := originalCompletePath_traffic_sq_le_of_count s d h f p hpfin (V s)
    (hW s) ENNReal.ofReal_ne_top (hsupp hsA) (hsingle hsA) (hnum hsA) (hw hsA)
  have hrightfin : ENNReal.ofReal B * ENNReal.ofReal K * ENNReal.ofReal C *
      legalMarkedCompletePathTraffic q d h (fun m ↦ p m.1 * f m) s ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) hsfin.ne
  have hreal := ENNReal.toReal_mono hrightfin hsq
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal hK, ENNReal.toReal_ofReal hC] using hreal

end OTSelector.Reconstruction
