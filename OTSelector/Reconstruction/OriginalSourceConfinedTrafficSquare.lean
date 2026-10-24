import OTSelector.Reconstruction.OriginalSourceWindowNonnegativeMoment
import OTSelector.MeasureTheory.Integral.CountSquareMoment

/-! Bounded-phase complete-path traffic squares use the same original finite
contributor count and deterministic physical source-window quadratic moment. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Actual same-scene contributors confined to a deterministic original source
window yield the quadratic source-window bound, retaining complete original marks. -/
theorem originalCompletePath_sourceConfined_traffic_sq_le
    {q : ℕ} (s : LegalMarkedOptimalInputScene q)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ≥0∞) (hp : Measurable p)
    {V : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hV : MeasurableSet V)
    {W : Set (Fin q → ℝ)} {B : Set (PhysicalPairPalmMark (Fin q))}
    (hsource : ∀ a ∈ V, a.1 ∈ W ∧ a.2 ∈ B)
    {K M : ℝ≥0∞} (hcount : physicalScenePairKernel s.1 V ≤ K)
    (hsupport : (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume).support ⊆ V)
    (hsingle : ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict V,
      (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ M * p a.2) :
    (legalMarkedCompletePathTraffic q d h f s) ^ 2 ≤ K * M ^ 2 *
      legalMarkedSourceWindowMoment q (W.indicator (fun _ ↦ 1))
        (B.indicator (fun m ↦ p m ^ 2)) s := by
  have hu : Measurable (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) := by
    have hG : Measurable (fun z : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) × ℝ ↦
        h (z.1.1 + d (z.1.2, z.2)) * f (z.1.2, z.2)) :=
      (hh.comp (measurable_fst.fst.add
        (hd.comp (measurable_fst.snd.prodMk measurable_snd)))).mul
        (hf.comp (measurable_fst.snd.prodMk measurable_snd))
    exact hG.lintegral_prod_right'
  have hsq := OTSelector.Probability.setLIntegral_sq_le_count_mul_momentumSquare
    (physicalScenePairKernel s.1) hu (hp.comp measurable_snd) hcount hsingle
  rw [setLIntegral_eq_of_support_subset hsupport] at hsq
  have hmoment : (∫⁻ a in V, p a.2 ^ 2 ∂physicalScenePairKernel s.1) ≤
      legalMarkedSourceWindowMoment q (W.indicator (fun _ ↦ 1))
        (B.indicator (fun m ↦ p m ^ 2)) s := by
    rw [← lintegral_indicator hV]
    apply lintegral_mono
    intro a
    by_cases ha : a ∈ V
    · obtain ⟨hw, hb⟩ := hsource a ha
      simp only [indicator_of_mem ha, indicator_of_mem hw, indicator_of_mem hb, one_mul, le_refl]
    · simp only [indicator_of_notMem ha]
      exact bot_le
  exact hsq.trans (mul_le_mul_right hmoment _)

/-- On the actual original good event, the same bounded-phase random traffic
has mean square controlled by the physical source volume and true Palm momentum
second moment, without assigning any Poisson law to selected edges. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_goodEvent_sourceConfined_traffic_sq_le
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ≥0∞) (hp : Measurable p)
    {A : Set (LegalMarkedOptimalInputScene q)}
    {W : Set (Fin q → ℝ)} (hW : MeasurableSet W)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    (V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    (hV : ∀ s, MeasurableSet (V s)) {K C : ℝ≥0∞}
    (hdata : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ A →
      (∀ a ∈ V s, a.1 ∈ W ∧ a.2 ∈ B) ∧ physicalScenePairKernel s.1 (V s) ≤ K ∧
      (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
        ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume).support ⊆ V s ∧
      (∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ C * p a.2)) :
    (∫⁻ s, Aᶜ.indicator (fun z ↦ (legalMarkedCompletePathTraffic q d h f z) ^ 2) s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      K * C ^ 2 * volume W * (∫⁻ m in B, p m ^ 2 ∂legalMarkedJointPalm q M.law) := by
  have hwin : Measurable (W.indicator (fun _ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hW
  have hmark : Measurable (B.indicator (fun m ↦ p m ^ (2 : ℕ))) :=
    (hp.pow_const (2 : ℕ)).indicator hB
  calc
    _ ≤ ∫⁻ s, K * C ^ 2 * legalMarkedSourceWindowMoment q (W.indicator (fun _ ↦ 1))
        (B.indicator (fun m ↦ p m ^ 2)) s
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
      apply lintegral_mono_ae
      filter_upwards [hdata] with s hs
      by_cases hsA : s ∈ A
      · rw [indicator_of_notMem (show s ∉ Aᶜ from fun hc ↦ hc hsA)]
        exact bot_le
      · rw [indicator_of_mem (show s ∈ Aᶜ from hsA)]
        obtain ⟨hsource, hcount, hsupp, hsingle⟩ := hs hsA
        exact originalCompletePath_sourceConfined_traffic_sq_le s d hd hh hf p hp (hV s)
          hsource hcount hsupp hsingle
    _ = _ := by
      rw [lintegral_const_mul (K * C ^ 2) (measurable_legalMarkedSourceWindowMoment hwin hmark),
        M.lintegral_sourceWindowMoment hwin hmark, lintegral_indicator_const hW,
        lintegral_indicator hB, one_mul]
      ring

end OTSelector.Reconstruction
