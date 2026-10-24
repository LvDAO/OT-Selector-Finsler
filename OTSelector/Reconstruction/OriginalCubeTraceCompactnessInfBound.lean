import OTSelector.Reconstruction.OriginalCubeTraceCompactnessRandomBound

/-! One measurable common trace bound from all actual finite-rank scales. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- One literal common bound, using the countable infimum of all actual
dyadic approximation bounds. No test-function supremum is introduced. -/
def originalTraceDualInfBound {q : ℕ} (g : (Fin q → ℝ) → ℝ) : ℝ :=
  ⨅ n : ℕ, originalDyadicTraceDualBound g n

/-- All actual dyadic bounds have the common lower bound zero. -/
theorem originalTraceDualInfBound_nonneg
    {q : ℕ} (g : (Fin q → ℝ) → ℝ) : 0 ≤ originalTraceDualInfBound g :=
  le_ciInf (originalDyadicTraceDualBound_nonneg g)

/-- The common bound is at most any fixed actual finite-scale bound. -/
theorem originalTraceDualInfBound_le
    {q : ℕ} (g : (Fin q → ℝ) → ℝ) (n : ℕ) :
    originalTraceDualInfBound g ≤ originalDyadicTraceDualBound g n :=
  ciInf_le ⟨0, fun _ ⟨m, hm⟩ ↦ hm ▸ originalDyadicTraceDualBound_nonneg g m⟩ n

/-- Countably many literal cell-integral bounds give a measurable common bound. -/
theorem measurable_originalTraceDualInfBound
    {Ω : Type*} [MeasurableSpace Ω] {q : ℕ} {g : Ω → (Fin q → ℝ) → ℝ}
    (hg : Measurable (fun p : Ω × (Fin q → ℝ) ↦ g p.1 p.2)) :
    Measurable (fun ω ↦ originalTraceDualInfBound (g ω)) :=
  Measurable.iInf (fun n ↦ measurable_originalDyadicTraceDualBound hg n)

/-- The single common bound is integrable, dominated by the actual coarsest
finite-scale bound. Only original field second moments enter the hypotheses. -/
theorem integrable_originalTraceDualInfBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {q : ℕ}
    {g : Ω → (Fin q → ℝ) → ℝ}
    (hg : Measurable (fun p : Ω × (Fin q → ℝ) ↦ g p.1 p.2))
    (hg2 : Integrable (fun p : Ω × (Fin q → ℝ) ↦ (g p.1 p.2)^2)
      (μ.prod (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1)))))
    (hcell : ∀ J : (originalDyadicFacePartition (ι := Fin q) 0).boxes,
      Integrable (fun ω ↦ (∫ y in J.1.Icc, g ω y)^2) μ) :
    Integrable (fun ω ↦ originalTraceDualInfBound (g ω)) μ := by
  apply (integrable_originalDyadicTraceDualBound μ hg2 0 hcell).mono'
    (measurable_originalTraceDualInfBound hg).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (originalTraceDualInfBound_nonneg (g ω))]
  exact originalTraceDualInfBound_le (g ω) 0

/-- One full-measure scene set and one actual measurable common quantity
simultaneously control all smooth zero-mean unit-energy trace tests. -/
theorem ae_all_smooth_trace_pairing_sq_le_originalTraceDualInfBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {q : ℕ}
    {g : Ω → (Fin q → ℝ) → ℝ}
    (hg : Measurable (fun p : Ω × (Fin q → ℝ) ↦ g p.1 p.2))
    (hg2 : Integrable (fun p : Ω × (Fin q → ℝ) ↦ (g p.1 p.2)^2)
      (μ.prod (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1))))) :
    ∀ᵐ ω ∂μ, ∀ (f : (Fin q → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1, f p) = 0 →
      boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1 →
      (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g ω y * f (y, 0))^2 ≤
        originalTraceDualInfBound (g ω) := by
  filter_upwards [ae_all_iff.mpr (fun n ↦
    ae_all_smooth_trace_pairing_sq_le_originalDyadicTraceDualBound μ hg hg2 n)] with ω hω
  intro f hf hmean henergy
  exact le_ciInf (fun n ↦ hω n f hf hmean henergy)

/-- Fixed-cell second moments tending to zero and one uniform actual face
second-moment bound force the expectation of the single common measurable
trace bound to zero. The dyadic scale is eliminated by an actual countable
infimum; no mesh-selection rate or dual-norm convergence is assumed. -/
theorem tendsto_integral_originalTraceDualInfBound_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {q : ℕ}
    {g : ℝ → Ω → (Fin q → ℝ) → ℝ}
    (hg : ∀ R, Measurable (fun p : Ω × (Fin q → ℝ) ↦ g R p.1 p.2))
    (hg2 : ∀ R, Integrable (fun p : Ω × (Fin q → ℝ) ↦ (g R p.1 p.2)^2)
      (μ.prod (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1)))))
    (hcell : ∀ R n (J : (originalDyadicFacePartition (ι := Fin q) n).boxes),
      Integrable (fun ω ↦ (∫ y in J.1.Icc, g R ω y)^2) μ)
    {C : ℝ}
    (hbulk : ∀ R, (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
      ∫ ω, (g R ω y)^2 ∂μ) ≤ C)
    (hcellzero : ∀ n (J : (originalDyadicFacePartition (ι := Fin q) n).boxes),
      Tendsto (fun R : ℝ ↦ ∫ ω, (∫ y in J.1.Icc, g R ω y)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦ ∫ ω, originalTraceDualInfBound (g R ω) ∂μ) atTop (𝓝 0) := by
  classical
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro z hz
    exact Eventually.of_forall (fun R ↦ lt_of_lt_of_le hz
      (integral_nonneg (fun ω ↦ originalTraceDualInfBound_nonneg (g R ω))))
  · intro z hz
    have ht : Tendsto (fun n : ℕ ↦ 2 * ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n) * C)
        atTop (𝓝 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
      simpa only [div_pow, one_pow, mul_zero, zero_mul] using
        (hp.const_mul (2 * ((q + 2 : ℕ) : ℝ))).mul_const C
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (half_pos hz))).exists
    let β : ℝ := 2 * (Fintype.card (originalDyadicFacePartition (ι := Fin q) n).boxes : ℝ) *
      ((((1 : ℝ) / 2^n)^(q + 1))⁻¹ * (((q + 1 : ℕ) : ℝ) / 2))
    have hsum : Tendsto (fun R : ℝ ↦ β *
        (∑ J : (originalDyadicFacePartition (ι := Fin q) n).boxes,
          ∫ ω, (∫ y in J.1.Icc, g R ω y)^2 ∂μ)) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero, mul_zero] using
        (tendsto_finsetSum Finset.univ (fun J _ ↦ hcellzero n J)).const_mul β
    filter_upwards [hsum.eventually (gt_mem_nhds (half_pos hz))] with R hR
    have hI := integrable_originalTraceDualInfBound μ (hg R) (hg2 R) (hcell R 0)
    have hN := integrable_originalDyadicTraceDualBound μ (hg2 R) n (hcell R n)
    have hle := integral_mono hI hN (fun ω ↦ originalTraceDualInfBound_le (g R ω) n)
    rw [integral_originalDyadicTraceDualBound_eq μ (hg2 R) n (hcell R n)] at hle
    have hb := mul_le_mul_of_nonneg_left (hbulk R)
      (show 0 ≤ 2 * ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n) by positivity)
    dsimp only [β] at hR
    linarith

end OTSelector.Reconstruction
