import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutClipping

/-!
# Absolute readout differences under the same two weak limits

The difference readout uses twice the common clip level. Its clipping error is
bounded by the two original clipping errors, so their accuracy and sample
budgets pass to the difference without a new integrability assumption.
-/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {S : Type*} [MeasurableSpace S] [TopologicalSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- The absolute difference at twice the clip level loses at most the sum of
the original component clipping errors. -/
theorem abs_sub_clipping_error_abs_sub_le (K : ℝ) (hK : 0 ≤ K)
    (Hp Hm : S → ℝ) (s : S) :
    |(|Hp s - Hm s|) - continuousReadoutClip (2 * K) (fun t ↦ |Hp t - Hm t|) s| ≤
      |Hp s - continuousReadoutClip K Hp s| + |Hm s - continuousReadoutClip K Hm s| := by
  have hy : |(|continuousReadoutClip K Hp s - continuousReadoutClip K Hm s|)| ≤ 2 * K := by
    rw [abs_abs]
    exact (abs_sub _ _).trans (by
      linarith [abs_continuousReadoutClip_le K hK Hp s,
        abs_continuousReadoutClip_le K hK Hm s])
  calc
    _ ≤ |(|Hp s - Hm s|) - (|continuousReadoutClip K Hp s - continuousReadoutClip K Hm s|)| :=
      abs_sub_continuousReadoutClip_le (2 * K) (fun t ↦ |Hp t - Hm t|) s _ hy
    _ ≤ |(Hp s - Hm s) -
        (continuousReadoutClip K Hp s - continuousReadoutClip K Hm s)| :=
      abs_abs_sub_abs_le _ _
    _ = |(Hp s - continuousReadoutClip K Hp s) -
        (Hm s - continuousReadoutClip K Hm s)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _

/-- The pointwise estimate controls the expected difference clipping error
without any finiteness assumption on the component error integrals. -/
theorem lintegral_abs_sub_clipping_error_le_add
    (μ : Measure S) (Hp Hm : S → ℝ) (hp : Continuous Hp) (_hm : Continuous Hm)
    (K : ℝ) (hK : 0 ≤ K) :
    (∫⁻ s, ENNReal.ofReal |(|Hp s - Hm s|) -
      continuousReadoutClip (2 * K) (fun t ↦ |Hp t - Hm t|) s| ∂μ) ≤
      (∫⁻ s, ENNReal.ofReal |Hp s - continuousReadoutClip K Hp s| ∂μ) +
        ∫⁻ s, ENNReal.ofReal |Hm s - continuousReadoutClip K Hm s| ∂μ := by
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal |Hp s - continuousReadoutClip K Hp s| +
        ENNReal.ofReal |Hm s - continuousReadoutClip K Hm s| ∂μ := by
      apply lintegral_mono
      intro s
      dsimp only
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub_clipping_error_abs_sub_le K hK Hp Hm s)
    _ = _ := lintegral_add_left
      ((hp.sub (continuous_continuousReadoutClip K hp)).abs.measurable.ennreal_ofReal) _

/-- Both component budgets apply to the same weak laws and accuracy indices.
Their absolute difference is integrable and passes through the separate weak stages. -/
theorem integrable_and_tendsto_integral_abs_sub_of_iterated_weak_clipping_errors
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S) (φ : ℕ → ℕ → ℕ)
    (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (Hp Hm : S → ℝ) (hp : Continuous Hp) (hm : Continuous Hm)
    (K : ℕ → ℝ) (hK : ∀ m, 0 ≤ K m)
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (sample : ℕ → ℕ → ℕ → ℝ≥0∞)
    (hsample : ∀ m ℓ, Tendsto (sample m ℓ) atTop (𝓝 0))
    (hbp : ∀ m ℓ, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal |Hp s - continuousReadoutClip (K m) Hp s|
        ∂(Pn ℓ n : Measure S)) ≤ δ m + sample m ℓ n)
    (hbm : ∀ m ℓ, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal |Hm s - continuousReadoutClip (K m) Hm s|
        ∂(Pn ℓ n : Measure S)) ≤ δ m + sample m ℓ n) :
    (∀ ℓ, Integrable (fun s ↦ |Hp s - Hm s|) (Q ℓ : Measure S) ∧
      (∀ᶠ n in atTop, Integrable (fun s ↦ |Hp s - Hm s|) (Pn ℓ (φ ℓ n) : Measure S)) ∧
      Tendsto (fun n ↦ ∫ s, |Hp s - Hm s| ∂(Pn ℓ (φ ℓ n) : Measure S)) atTop
        (𝓝 (∫ s, |Hp s - Hm s| ∂(Q ℓ : Measure S)))) ∧
    Integrable (fun s ↦ |Hp s - Hm s|) (R : Measure S) ∧
    Tendsto (fun ℓ ↦ ∫ s, |Hp s - Hm s| ∂(Q (ψ ℓ) : Measure S)) atTop
      (𝓝 (∫ s, |Hp s - Hm s| ∂(R : Measure S))) := by
  have hδsum : Tendsto (fun m ↦ δ m + δ m) atTop (𝓝 0) := by
    simpa only [add_zero] using hδ.add hδ
  have hsampleSum (m ℓ : ℕ) :
      Tendsto (fun n ↦ sample m ℓ n + sample m ℓ n) atTop (𝓝 0) := by
    simpa only [add_zero] using (hsample m ℓ).add (hsample m ℓ)
  have hgapBound (m ℓ : ℕ) : ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal |(|Hp s - Hm s|) -
        continuousReadoutClip (2 * K m) (fun t ↦ |Hp t - Hm t|) s|
        ∂(Pn ℓ n : Measure S)) ≤
          (δ m + δ m) + (sample m ℓ n + sample m ℓ n) := by
    filter_upwards [hbp m ℓ, hbm m ℓ] with n hnp hnm
    apply (lintegral_abs_sub_clipping_error_le_add (Pn ℓ n : Measure S)
      Hp Hm hp hm (K m) (hK m)).trans
    exact (add_le_add hnp hnm).trans_eq (by ac_rfl)
  have h := integrable_and_tendsto_integral_of_iterated_weak_vanishing_clipping_errors
    Pn Q R φ hφ ψ hinner houter (fun s ↦ |Hp s - Hm s|) (hp.sub hm).abs
    (fun m ↦ 2 * K m) (fun m ↦ mul_nonneg (by norm_num) (hK m)) (fun m ↦ δ m + δ m) hδsum
    (fun m ℓ n ↦ sample m ℓ n + sample m ℓ n) hsampleSum hgapBound
  exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Agreement under the terminal law makes the outer expected absolute gap
vanish, with the same separate sample and tilt limits. -/
theorem tendsto_integral_abs_sub_zero_of_iterated_weak_clipping_errors
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S) (φ : ℕ → ℕ → ℕ)
    (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (Hp Hm : S → ℝ) (hp : Continuous Hp) (hm : Continuous Hm)
    (K : ℕ → ℝ) (hK : ∀ m, 0 ≤ K m)
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (sample : ℕ → ℕ → ℕ → ℝ≥0∞)
    (hsample : ∀ m ℓ, Tendsto (sample m ℓ) atTop (𝓝 0))
    (hbp : ∀ m ℓ, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal |Hp s - continuousReadoutClip (K m) Hp s|
        ∂(Pn ℓ n : Measure S)) ≤ δ m + sample m ℓ n)
    (hbm : ∀ m ℓ, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal |Hm s - continuousReadoutClip (K m) Hm s|
        ∂(Pn ℓ n : Measure S)) ≤ δ m + sample m ℓ n)
    (hagreement : ∀ᵐ s ∂(R : Measure S), Hp s = Hm s) :
    Tendsto (fun ℓ ↦ ∫ s, |Hp s - Hm s| ∂(Q (ψ ℓ) : Measure S)) atTop (𝓝 0) := by
  have h := integrable_and_tendsto_integral_abs_sub_of_iterated_weak_clipping_errors
    Pn Q R φ hφ ψ hinner houter Hp Hm hp hm K hK δ hδ sample hsample hbp hbm
  have hzero : (∫ s, |Hp s - Hm s| ∂(R : Measure S)) = 0 :=
    integral_eq_zero_of_ae (hagreement.mono fun s hs ↦ by
      change |Hp s - Hm s| = 0
      rw [hs, sub_self, abs_zero])
  simpa only [hzero] using h.2.2

end OTSelector.Reconstruction
