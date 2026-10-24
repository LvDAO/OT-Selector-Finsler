import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSourceProbeWeakExpectation

/-!
# Fixed-source actual readout expectations through two weak stages

The sample limit is taken at each fixed tilt, and only then is the outer tilt
subsequence passed to the same limiting law. There is no sample/tilt diagonal.
-/
open Set Function MeasureTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000

/-- Integrable nonnegative readout convergence also gives convergence of the
actual extended nonnegative expectations. -/
theorem tendsto_lintegral_ofReal_of_integral_tendsto_of_nonneg
    {S : Type*} [MeasurableSpace S] (Pn : ℕ → Measure S) (R : Measure S)
    (f : S → ℝ) (hf : ∀ s, 0 ≤ f s)
    (hIntN : ∀ n, Integrable f (Pn n)) (hIntR : Integrable f R)
    (hreal : Tendsto (fun n ↦ ∫ s, f s ∂Pn n) atTop (𝓝 (∫ s, f s ∂R))) :
    Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (f s) ∂Pn n) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (f s) ∂R)) := by
  have h := (ENNReal.continuous_ofReal.tendsto (∫ s, f s ∂R)).comp hreal
  rw [ofReal_integral_eq_lintegral_ofReal hIntR (Eventually.of_forall hf)] at h
  exact h.congr' (Eventually.of_forall fun n ↦
    ofReal_integral_eq_lintegral_ofReal (hIntN n) (Eventually.of_forall hf))

/-- Both given weak stages preserve the same actual source and actual complete
probe readouts, with real and extended nonnegative expectation convergence. -/
theorem fixed_source_probe_gap_expectation_limits_of_iterated_weak
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] [HasOuterApproxClosed S]
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (Pn ℓ) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (π₀ π₁ : S → ProbabilityMeasure (X × Y))
    (hπ₀ : Continuous π₀) (hπ₁ : Continuous π₁)
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X × Y → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hfBound : ∀ p, |f p| ≤ B)
    (happrox : ∀ ε > 0, ∃ G : (X × Y) →ᵇ ℝ,
      ∀ π : ProbabilityMeasure (X × Y), (π : Measure (X × Y)).fst = μ →
        |(∫ p, f p ∂(π : Measure (X × Y))) - ∫ p, G p ∂(π : Measure (X × Y))| ≤ ε)
    (hsource₀ : ∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₀ s : Measure (X × Y)).fst = μ)
    (hsource₁ : ∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₁ s : Measure (X × Y)).fst = μ) :
    let obs : S → ℝ := fun s ↦ |(∫ p, f p ∂(π₀ s : Measure (X × Y))) -
      ∫ p, f p ∂(π₁ s : Measure (X × Y))|
    (∀ᵐ s ∂(R : Measure S), (π₀ s : Measure (X × Y)).fst = μ ∧
      (π₁ s : Measure (X × Y)).fst = μ) ∧
    (∀ ℓ n, Integrable obs (Pn ℓ n : Measure S)) ∧
    (∀ ℓ, Integrable obs (Q ℓ : Measure S)) ∧ Integrable obs (R : Measure S) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫ s, obs s ∂(Pn ℓ n : Measure S)) atTop
      (𝓝 (∫ s, obs s ∂(Q ℓ : Measure S)))) ∧
    Tendsto (fun ℓ ↦ ∫ s, obs s ∂(Q (ψ ℓ) : Measure S)) atTop
      (𝓝 (∫ s, obs s ∂(R : Measure S))) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Pn ℓ n : Measure S)) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (obs s) ∂(Q ℓ : Measure S)))) ∧
    Tendsto (fun ℓ ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Q (ψ ℓ) : Measure S)) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S))) := by
  let obs : S → ℝ := fun s ↦ |(∫ p, f p ∂(π₀ s : Measure (X × Y))) -
    ∫ p, f p ∂(π₁ s : Measure (X × Y))|
  have hI (ℓ : ℕ) := fixed_source_probe_gap_expectation_tendsto_of_weak
    (Q ℓ) (Pn ℓ) (hinner ℓ) π₀ π₁ hπ₀ hπ₁ μ f hB hfBound happrox
      (hsource₀ ℓ) (hsource₁ ℓ)
  have hO := fixed_source_probe_gap_expectation_tendsto_of_weak
    R (fun ℓ ↦ Q (ψ ℓ)) houter π₀ π₁ hπ₀ hπ₁ μ f hB hfBound happrox
      (fun ℓ ↦ (hI (ψ ℓ)).1.mono fun s hs ↦ hs.1)
      (fun ℓ ↦ (hI (ψ ℓ)).1.mono fun s hs ↦ hs.2)
  refine ⟨hO.1, fun ℓ n ↦ (hI ℓ).2.1 n, fun ℓ ↦ (hI ℓ).2.2.1,
    hO.2.2.1, fun ℓ ↦ (hI ℓ).2.2.2, hO.2.2.2, ?_, ?_⟩
  · intro ℓ
    exact tendsto_lintegral_ofReal_of_integral_tendsto_of_nonneg
      (fun n ↦ (Pn ℓ n : Measure S)) (Q ℓ : Measure S) obs (fun _ ↦ abs_nonneg _)
      (hI ℓ).2.1 (hI ℓ).2.2.1 (hI ℓ).2.2.2
  · exact tendsto_lintegral_ofReal_of_integral_tendsto_of_nonneg
      (fun ℓ ↦ (Q (ψ ℓ) : Measure S)) (R : Measure S) obs (fun _ ↦ abs_nonneg _)
      hO.2.1 hO.2.2.1 hO.2.2.2

end OTSelector.Reconstruction
