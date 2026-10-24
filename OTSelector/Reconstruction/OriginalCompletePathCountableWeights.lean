import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell
import OTSelector.MeasureTheory.Lp.SummableSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Countable nonnegative weights are read against the unchanged original
matching and clock. Actual true-Palm equality identifies the scene readout,
so summable component L2 bounds concern the literal complete-path traffic. -/
open Set Function MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Tonelli decomposes the literal original complete-path traffic, for every scene. -/
theorem legalMarkedCompletePathTraffic_tsum_weights {q : ℕ} {I : Type*} [Countable I]
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} (hη : Measurable η)
    (f : I → PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (s : LegalMarkedOptimalInputScene q) :
    legalMarkedCompletePathTraffic q d η (fun z ↦ ∑' i, f i z) s =
      ∑' i, legalMarkedCompletePathTraffic q d η (f i) s := by
  have hG (i : I) : Measurable
      (fun z : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) × ℝ ↦
        η (z.1.1 + d (z.1.2, z.2)) * f i (z.1.2, z.2)) :=
    (hη.comp (measurable_fst.fst.add
      (hd.comp (measurable_fst.snd.prodMk measurable_snd)))).mul
      ((hf i).comp (measurable_fst.snd.prodMk measurable_snd))
  unfold legalMarkedCompletePathTraffic
  calc
    _ = ∫⁻ p, ∑' i, ∫⁻ c : ℝ, η (p.1 + d (p.2, c)) * f i (p.2, c)
        ∂volume ∂physicalScenePairKernel s.1 := by
      apply lintegral_congr_ae
      filter_upwards [] with p
      simp_rw [← ENNReal.tsum_mul_left]
      exact lintegral_tsum (fun i ↦ ((hG i).comp measurable_prodMk_left).aemeasurable)
    _ = _ := lintegral_tsum (fun i ↦ (hG i).lintegral_prod_right'.aemeasurable)

/-- Weight domination is retained by the actual original complete-path readout. -/
theorem legalMarkedCompletePathTraffic_mono_weights {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞)
    {f g : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hfg : ∀ z, f z ≤ g z) (s : LegalMarkedOptimalInputScene q) :
    legalMarkedCompletePathTraffic q d η f s ≤ legalMarkedCompletePathTraffic q d η g s := by
  apply lintegral_mono
  intro p
  apply lintegral_mono
  intro c
  exact mul_le_mul_right (hfg (p.2, c)) _

/-- Equality on the actual original true-Palm/clock law gives equality of
actual scene traffic, provided its original first moment is finite. -/
theorem LegalWeightedStationaryPoissonMatching.ae_completePathTraffic_congr_weights
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} (hη : Measurable η)
    {f₁ f₂ : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (heq : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, ∀ᵐ c : ℝ ∂volume, f₁ (m, c) = f₂ (m, c))
    (hfinite : (∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f₂ (m, c) ∂volume ∂legalMarkedJointPalm q Q.law) ≠ ∞) :
    (fun s ↦ legalMarkedCompletePathTraffic q d η f₁ s) =ᵐ[
      (Q.law : Measure (LegalMarkedOptimalInputScene q))]
      fun s ↦ legalMarkedCompletePathTraffic q d η f₂ s := by
  let v := fun z ↦ min (f₁ z) (f₂ z)
  have hv : Measurable v := hf₁.min hf₂
  have hPalm (u : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
      (hu : Measurable u)
      (hueq : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, ∀ᵐ c : ℝ ∂volume, u (m, c) = f₂ (m, c)) :
      (∫⁻ s, legalMarkedCompletePathTraffic q d η u s
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
      (∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f₂ (m, c) ∂volume ∂legalMarkedJointPalm q Q.law) := by
    rw [Q.lintegral_completePathTraffic d hd hη hu]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hueq] with m hm
    exact lintegral_congr_ae hm
  have hveq : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, ∀ᵐ c : ℝ ∂volume, v (m, c) = f₂ (m, c) := by
    filter_upwards [heq] with m hm
    filter_upwards [hm] with c hc
    simp only [v, hc, min_self]
  have hvm := hPalm v hv hveq
  have h₁ := hPalm f₁ hf₁ heq
  have h₂ := Q.lintegral_completePathTraffic d hd hη hf₂
  have hVfinite : (∫⁻ s, legalMarkedCompletePathTraffic q d η v s
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≠ ∞ := by rwa [hvm]
  have hV₁ : (fun s ↦ legalMarkedCompletePathTraffic q d η v s) =ᵐ[
      (Q.law : Measure (LegalMarkedOptimalInputScene q))]
      fun s ↦ legalMarkedCompletePathTraffic q d η f₁ s :=
    ae_eq_of_ae_le_of_lintegral_le
      (.of_forall fun s ↦ legalMarkedCompletePathTraffic_mono_weights d η (fun z ↦ min_le_left _ _) s)
      hVfinite (measurable_legalMarkedCompletePathTraffic d hd hη hf₁).aemeasurable
      (by rw [h₁, hvm])
  have hV₂ : (fun s ↦ legalMarkedCompletePathTraffic q d η v s) =ᵐ[
      (Q.law : Measure (LegalMarkedOptimalInputScene q))]
      fun s ↦ legalMarkedCompletePathTraffic q d η f₂ s :=
    ae_eq_of_ae_le_of_lintegral_le
      (.of_forall fun s ↦ legalMarkedCompletePathTraffic_mono_weights d η (fun z ↦ min_le_right _ _) s)
      hVfinite (measurable_legalMarkedCompletePathTraffic d hd hη hf₂).aemeasurable
      (by rw [h₂, hvm])
  exact hV₁.symm.trans hV₂

/-- Actual countably split original weights reconstruct the literal full
traffic in L2 from the component norm bounds. The original true-Palm split
is turned into an actual-scene sum identity internally. -/
theorem LegalWeightedStationaryPoissonMatching.memLp_completePathTraffic_of_countable_weights
    {q : ℕ} {I : Type*} [Countable I] {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} (hη : Measurable η)
    (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞) (hf : Measurable f)
    (parts : I → PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (hparts : ∀ i, Measurable (parts i))
    (hsplit : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, ∀ᵐ c : ℝ ∂volume,
      (∑' i, parts i (m, c)) = f (m, c))
    (hfinite : (∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q Q.law) ≠ ∞)
    (hLtwo : ∀ i, MemLp (fun s ↦ (legalMarkedCompletePathTraffic q d η (parts i) s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (A : I → ℝ) (hA : Summable A) (hA0 : ∀ i, 0 ≤ A i)
    (hbound : ∀ i, eLpNorm (fun s ↦ (legalMarkedCompletePathTraffic q d η (parts i) s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤ ENNReal.ofReal (A i)) :
    MemLp (fun s ↦ (legalMarkedCompletePathTraffic q d η f s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (eLpNorm (fun s ↦ (legalMarkedCompletePathTraffic q d η f s).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q))).toReal ≤ ∑' i, A i ∧
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      (legalMarkedCompletePathTraffic q d η f s).toReal =
        ∑' i, (legalMarkedCompletePathTraffic q d η (parts i) s).toReal ∧
      Summable (fun i ↦ ‖(legalMarkedCompletePathTraffic q d η (parts i) s).toReal‖) := by
  have hsumMeas : Measurable (fun z ↦ ∑' i, parts i z) := Measurable.tsum hparts
  have hscene := Q.ae_completePathTraffic_congr_weights d hd hη hsumMeas hf hsplit hfinite
  have hmeanFinite : (∫⁻ s, legalMarkedCompletePathTraffic q d η f s
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≠ ∞ := by
    rwa [Q.lintegral_completePathTraffic d hd hη hf]
  have hreal : (fun s ↦ (legalMarkedCompletePathTraffic q d η f s).toReal) =ᵐ[
      (Q.law : Measure (LegalMarkedOptimalInputScene q))]
      fun s ↦ ∑' i, (legalMarkedCompletePathTraffic q d η (parts i) s).toReal := by
    filter_upwards [hscene, ae_lt_top
      (measurable_legalMarkedCompletePathTraffic d hd hη hf) hmeanFinite] with s hs hsfinite
    have hsum := legalMarkedCompletePathTraffic_tsum_weights d hd hη parts hparts s
    have hsumFinite : (∑' i, legalMarkedCompletePathTraffic q d η (parts i) s) ≠ ∞ := by
      rw [← hsum, hs]
      exact hsfinite.ne
    rw [← hs, hsum, ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hsumFinite)]
  have hLp := memLp_tsum_of_summable_level_bound
    (Q.law : Measure (LegalMarkedOptimalInputScene q))
    (fun i s ↦ (legalMarkedCompletePathTraffic q d η (parts i) s).toReal)
    hLtwo A hA hA0 hbound
  refine ⟨hLp.1.ae_eq hreal.symm, ?_, ?_⟩
  · rw [eLpNorm_congr_ae hreal]
    exact hLp.2.1
  · filter_upwards [hreal, hLp.2.2] with s hs hsum
    exact ⟨hs, hsum⟩

end OTSelector.Reconstruction
