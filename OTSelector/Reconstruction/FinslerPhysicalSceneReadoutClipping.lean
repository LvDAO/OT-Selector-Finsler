import OTSelector.MeasureTheory.IteratedWeakMarginalDefect
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedCompactReadout

/-!
# Weak expectations from vanishing continuous clipping errors

Clipping controls a fixed continuous readout under the unchanged weak laws.
The accuracy index may change both the clip level and its sample error. Each
sample error vanishes at fixed accuracy before accuracy tends to zero.
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

/-- Symmetric clipping of the same real readout at a finite level. -/
def continuousReadoutClip (K : ℝ) (H : S → ℝ) : S → ℝ :=
  fun s ↦ max (-K) (min K (H s))

theorem continuous_continuousReadoutClip (K : ℝ) {H : S → ℝ}
    (hH : Continuous H) : Continuous (continuousReadoutClip K H) :=
  continuous_const.max (continuous_const.min hH)

theorem abs_continuousReadoutClip_le (K : ℝ) (hK : 0 ≤ K) (H : S → ℝ) (s : S) :
    |continuousReadoutClip K H s| ≤ K := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clipping minimizes distance to any real value in the same interval. -/
theorem abs_sub_continuousReadoutClip_le (K : ℝ) (H : S → ℝ) (s : S)
    (y : ℝ) (hy : |y| ≤ K) :
    |H s - continuousReadoutClip K H s| ≤ |H s - y| := by
  obtain ⟨hylow, hyhigh⟩ := abs_le.mp hy
  have hK : 0 ≤ K := (abs_nonneg y).trans hy
  by_cases hl : H s ≤ -K
  · rw [continuousReadoutClip, min_eq_right (by linarith : H s ≤ K), max_eq_left hl,
      abs_of_nonpos (by linarith : H s - -K ≤ 0),
      abs_of_nonpos (by linarith : H s - y ≤ 0)]
    linarith
  · by_cases hh : K ≤ H s
    · rw [continuousReadoutClip, min_eq_left hh, max_eq_right (by linarith : -K ≤ K),
        abs_of_nonneg (by linarith : 0 ≤ H s - K),
        abs_of_nonneg (by linarith : 0 ≤ H s - y)]
      linarith
    · rw [continuousReadoutClip, min_eq_right (le_of_not_ge hh),
        max_eq_right (le_of_not_ge hl), sub_self, abs_zero]
      exact abs_nonneg _

/-- A finite clipping-error bound supplies integrability and controls the
ordinary expectation error; no integrability premise on the readout is needed. -/
theorem integrable_and_dist_integral_clip_le_of_error
    (μ : Measure S) [IsFiniteMeasure μ] (H : S → ℝ) (hH : Continuous H)
    (K : ℝ) (hK : 0 ≤ K) (ε : ℝ) (hε : 0 ≤ ε)
    (herror : (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip K H s| ∂μ) ≤
      ENNReal.ofReal ε) :
    Integrable H μ ∧ dist (∫ s, H s ∂μ) (∫ s, continuousReadoutClip K H s ∂μ) ≤ ε := by
  have hclip := continuous_continuousReadoutClip K hH
  have hiclip : Integrable (continuousReadoutClip K H) μ :=
    Integrable.of_bound hclip.aestronglyMeasurable K
      (Eventually.of_forall fun s ↦ by
        simpa only [Real.norm_eq_abs] using abs_continuousReadoutClip_le K hK H s)
  have hierror : Integrable (fun s ↦ H s - continuousReadoutClip K H s) μ := by
    refine ⟨(hH.sub hclip).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs] using lt_of_le_of_lt herror ENNReal.ofReal_lt_top
  have hiH : Integrable H μ := by
    exact (hierror.add hiclip).congr (Eventually.of_forall fun s ↦ sub_add_cancel _ _)
  refine ⟨hiH, ?_⟩
  rw [Real.dist_eq, ← integral_sub hiH hiclip, ← Real.norm_eq_abs]
  apply (norm_integral_le_lintegral_norm _).trans
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hε] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top herror

/-- Vanishing expected clipping errors turn weak convergence into ordinary
expectation convergence and supply all required integrability internally. -/
theorem integrable_and_tendsto_integral_of_weak_clipping_approximation
    (Pn : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 Q)) (H : S → ℝ) (hH : Continuous H)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n in atTop, (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip K H s|
        ∂(Pn n : Measure S)) ≤ ENNReal.ofReal ε) :
    Integrable H (Q : Measure S) ∧
      (∀ᶠ n in atTop, Integrable H (Pn n : Measure S)) ∧
      Tendsto (fun n ↦ ∫ s, H s ∂(Pn n : Measure S)) atTop
        (𝓝 (∫ s, H s ∂(Q : Measure S))) := by
  have hQerror (K : ℝ) (ε : ℝ)
      (hb : ∀ᶠ n in atTop, (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip K H s|
        ∂(Pn n : Measure S)) ≤ ENNReal.ofReal ε) :
      (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip K H s|
        ∂(Q : Measure S)) ≤ ENNReal.ofReal ε := by
    apply lintegral_abs_le_of_weak_eventual_bound_vanishing_defect Q Pn hweak
      (fun s ↦ H s - continuousReadoutClip K H s)
      (hH.sub (continuous_continuousReadoutClip K hH)) (ENNReal.ofReal ε)
      (fun _ ↦ 0) tendsto_const_nhds
    simpa only [add_zero] using hb
  obtain ⟨K₀, hK₀, hb₀⟩ := happrox 1 zero_lt_one
  have hiQ := (integrable_and_dist_integral_clip_le_of_error (Q : Measure S) H hH
    K₀ hK₀ 1 zero_le_one (hQerror K₀ 1 hb₀)).1
  refine ⟨hiQ, hb₀.mono (fun n hn ↦
    (integrable_and_dist_integral_clip_le_of_error (Pn n : Measure S) H hH
      K₀ hK₀ 1 zero_le_one hn).1), ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨K, hK, hb⟩ := happrox (ε / 4) hquarter
  have hQdist := (integrable_and_dist_integral_clip_le_of_error (Q : Measure S) H hH
    K hK (ε / 4) hquarter.le (hQerror K (ε / 4) hb)).2
  have hclipweak := (ae_bound_and_tendsto_integral_of_weak_uniform_bound Pn Q hweak
    (continuousReadoutClip K H) (continuous_continuousReadoutClip K hH) K hK
    (fun _ ↦ Eventually.of_forall fun s ↦ abs_continuousReadoutClip_le K hK H s)).2
  filter_upwards [hb, (Metric.tendsto_nhds.mp hclipweak) (ε / 4) hquarter] with n hn hnclip
  have hPdist := (integrable_and_dist_integral_clip_le_of_error (Pn n : Measure S) H hH
    K hK (ε / 4) hquarter.le hn).2
  have ht := dist_triangle (∫ s, H s ∂(Pn n : Measure S))
    (∫ s, continuousReadoutClip K H s ∂(Pn n : Measure S)) (∫ s, H s ∂(Q : Measure S))
  have ht' := dist_triangle (∫ s, continuousReadoutClip K H s ∂(Pn n : Measure S))
    (∫ s, continuousReadoutClip K H s ∂(Q : Measure S)) (∫ s, H s ∂(Q : Measure S))
  rw [dist_comm] at hQdist
  linarith

/-- Each accuracy level has its own sample error. The same continuous readout
and weak laws remain fixed while sample errors vanish and then accuracy does. -/
theorem integrable_and_tendsto_integral_of_weak_vanishing_clipping_errors
    (Pn : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 Q)) (H : S → ℝ) (hH : Continuous H)
    (K : ℕ → ℝ) (hK : ∀ m, 0 ≤ K m)
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (sample : ℕ → ℕ → ℝ≥0∞) (hsample : ∀ m, Tendsto (sample m) atTop (𝓝 0))
    (hbound : ∀ m, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip (K m) H s|
        ∂(Pn n : Measure S)) ≤ δ m + sample m n) :
    (∀ m, (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip (K m) H s|
      ∂(Q : Measure S)) ≤ δ m) ∧
    Integrable H (Q : Measure S) ∧
    (∀ᶠ n in atTop, Integrable H (Pn n : Measure S)) ∧
    Tendsto (fun n ↦ ∫ s, H s ∂(Pn n : Measure S)) atTop
      (𝓝 (∫ s, H s ∂(Q : Measure S))) := by
  refine ⟨fun m ↦ lintegral_abs_le_of_weak_eventual_bound_vanishing_defect Q Pn hweak
    (fun s ↦ H s - continuousReadoutClip (K m) H s)
    (hH.sub (continuous_continuousReadoutClip (K m) hH)) (δ m)
    (sample m) (hsample m) (hbound m), ?_⟩
  apply integrable_and_tendsto_integral_of_weak_clipping_approximation Pn Q hweak H hH
  intro ε hε
  have hh : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨m, hm⟩ := ((tendsto_order.mp hδ).2 _ hh).exists
  refine ⟨K m, hK m, ?_⟩
  filter_upwards [hbound m, (tendsto_order.mp (hsample m)).2 _ hh] with n hn hns
  apply hn.trans
  calc
    δ m + sample m n ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add hm.le hns.le
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 2) (by positivity : 0 ≤ ε / 2)]
      congr 1
      ring

/-- Inner sample limits remove their accuracy-dependent sample errors. The
outer tilt limit inherits the same clipping accuracy without a diagonal. -/
theorem integrable_and_tendsto_integral_of_iterated_weak_vanishing_clipping_errors
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S) (φ : ℕ → ℕ → ℕ)
    (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (H : S → ℝ) (hH : Continuous H) (K : ℕ → ℝ) (hK : ∀ m, 0 ≤ K m)
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (sample : ℕ → ℕ → ℕ → ℝ≥0∞)
    (hsample : ∀ m ℓ, Tendsto (sample m ℓ) atTop (𝓝 0))
    (hbound : ∀ m ℓ, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip (K m) H s|
        ∂(Pn ℓ n : Measure S)) ≤ δ m + sample m ℓ n) :
    (∀ m ℓ, (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip (K m) H s|
      ∂(Q ℓ : Measure S)) ≤ δ m) ∧
    (∀ ℓ, Integrable H (Q ℓ : Measure S) ∧
      (∀ᶠ n in atTop, Integrable H (Pn ℓ (φ ℓ n) : Measure S)) ∧
      Tendsto (fun n ↦ ∫ s, H s ∂(Pn ℓ (φ ℓ n) : Measure S)) atTop
        (𝓝 (∫ s, H s ∂(Q ℓ : Measure S)))) ∧
    (∀ m, (∫⁻ s, ENNReal.ofReal |H s - continuousReadoutClip (K m) H s|
      ∂(R : Measure S)) ≤ δ m) ∧
    Integrable H (R : Measure S) ∧
    Tendsto (fun ℓ ↦ ∫ s, H s ∂(Q (ψ ℓ) : Measure S)) atTop
      (𝓝 (∫ s, H s ∂(R : Measure S))) := by
  have hQ (ℓ : ℕ) :=
    integrable_and_tendsto_integral_of_weak_vanishing_clipping_errors
      (fun n ↦ Pn ℓ (φ ℓ n)) (Q ℓ) (hinner ℓ) H hH K hK δ hδ
      (fun m n ↦ sample m ℓ (φ ℓ n)) (fun m ↦ (hsample m ℓ).comp (hφ ℓ))
      (fun m ↦ (hφ ℓ).eventually (hbound m ℓ))
  have hR := integrable_and_tendsto_integral_of_weak_vanishing_clipping_errors
    (fun ℓ ↦ Q (ψ ℓ)) R houter H hH K hK δ hδ (fun _ _ ↦ 0)
    (fun _ ↦ tendsto_const_nhds) (fun m ↦ Eventually.of_forall fun ℓ ↦ by
      simpa only [add_zero] using (hQ (ψ ℓ)).1 m)
  exact ⟨fun m ℓ ↦ (hQ ℓ).1 m, fun ℓ ↦ (hQ ℓ).2,
    hR.1, hR.2.1, hR.2.2.2⟩

end OTSelector.Reconstruction
