import OTSelector.Reconstruction.FinslerRelativeLawClassCubeBinomialUniform

/-! Uniform normalization with an actual varying filling volume retained. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- Uniformly bounded multipliers preserve a vanishing uniform error, even
when the multipliers themselves have no limit. -/
theorem tendstoUniformlyOn_mul_zero_of_eventually_bounded {X : Type*}
    {T : Set X} {F w : ℕ → X → ℝ}
    (hF : TendstoUniformlyOn F (fun _ ↦ 0) atTop T)
    {B : ℝ} (hB : 0 ≤ B) (hw : ∀ᶠ N in atTop, ∀ x ∈ T, |w N x| ≤ B) :
    TendstoUniformlyOn (fun N x ↦ w N x * F N x) (fun _ ↦ 0) atTop T := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  have hBp : 0 < B + 1 := by linarith
  filter_upwards [hw, hF (ε / (B + 1)) (div_pos hε hBp)] with N hN hFN
  intro x hx
  simp only [Real.dist_eq, zero_sub, abs_neg] at hFN ⊢
  rw [abs_mul]
  calc
    _ ≤ (B + 1) * |F N x| := mul_le_mul_of_nonneg_right ((hN x hx).trans (by linarith)) (abs_nonneg _)
    _ < (B + 1) * (ε / (B + 1)) := mul_lt_mul_of_pos_left (hFN x hx) hBp
    _ = ε := by field_simp

/-- A changing finite family is normalized by its actual volume. Only bounded
filling volume is needed; no convergence to the full original cell is asserted. -/
theorem tendstoUniformlyOn_volume_weighted_normalization {X : Type*} {T : Set X}
    {F : ℕ → X → ℝ} {P : X → ℝ}
    (hF : TendstoUniformlyOn F P atTop T) {mass : ℕ → ℝ} {m : ℝ}
    (hm : Tendsto mass atTop (𝓝 m)) (hm0 : m ≠ 0)
    {weight : ℕ → ℝ} {V B : ℝ} (hV : 0 ≤ V) (hB : 0 ≤ B)
    (hw : ∀ᶠ N in atTop, |weight N| ≤ V) (hP : ∀ x ∈ T, |P x| ≤ B) :
    TendstoUniformlyOn
      (fun N x ↦ weight N * (F N x / mass N - P x / m)) (fun _ ↦ 0) atTop T := by
  have hinv := hm.inv₀ hm0
  have hinvb : ∀ᶠ N in atTop, |(mass N)⁻¹| ≤ |m⁻¹| + 1 := by
    have hevent := hinv.eventually (Metric.ball_mem_nhds (m⁻¹) (by norm_num : (0:ℝ) < 1))
    filter_upwards [hevent] with N hN
    have hdist : |(mass N)⁻¹ - m⁻¹| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hN
    calc
      |(mass N)⁻¹| = |((mass N)⁻¹ - m⁻¹) + m⁻¹| := by rw [sub_add_cancel]
      _ ≤ |(mass N)⁻¹ - m⁻¹| + |m⁻¹| := abs_add_le _ _
      _ ≤ |m⁻¹| + 1 := by linarith
  have hconst : TendstoUniformlyOn (fun _ : ℕ ↦ P) P atTop T := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall fun N x hx ↦ by simpa using hε
  have hdiff : TendstoUniformlyOn (fun N x ↦ F N x - P x) (fun _ ↦ 0) atTop T := by
    have hh := hF.sub hconst
    change TendstoUniformlyOn (fun N x ↦ F N x - P x) (fun x ↦ P x - P x) atTop T at hh
    simpa only [sub_self] using hh
  have hfirst := tendstoUniformlyOn_mul_zero_of_eventually_bounded hdiff
    (B := |m⁻¹| + 1) (by positivity)
    (hinvb.mono fun N hN x hx ↦ hN)
  have hscalar : Tendsto (fun N ↦ (mass N)⁻¹ - m⁻¹) atTop (𝓝 0) := by
    simpa only [sub_self] using hinv.sub (tendsto_const_nhds (x := m⁻¹))
  have hsecond := tendstoUniformlyOn_mul_zero_of_eventually_bounded
    (hscalar.tendstoUniformlyOn_const T) hB
    (Filter.Eventually.of_forall fun N x hx ↦ hP x hx)
  have hsum : TendstoUniformlyOn
      (fun N x ↦ F N x / mass N - P x / m) (fun _ ↦ 0) atTop T := by
    convert hfirst.add hsecond using 1
    · funext N x
      simp only [div_eq_mul_inv, Pi.add_apply]
      ring
    · funext x
      simp only [Pi.add_apply, add_zero]
  exact tendstoUniformlyOn_mul_zero_of_eventually_bounded hsum hV
    (hw.mono fun N hN x hx ↦ hN)


/-- Vanishing added original mass bounds every actual filling volume by the
finite original set mass plus one, eventually. No missing-mass limit is used. -/
theorem eventually_measureReal_le_of_added_mass_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s : Set X} (hs : μ s ≠ ∞) (U : ℕ → Set X)
    (hadded : Tendsto (fun N ↦ μ (U N \ s)) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, μ.real (U N) ≤ μ.real s + 1 := by
  filter_upwards [hadded.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))] with N hN
  have hsub : U N ⊆ s ∪ (U N \ s) := by
    intro x hx
    by_cases hxs : x ∈ s
    · exact Or.inl hxs
    · exact Or.inr ⟨hx, hxs⟩
  have hm : μ (U N) ≤ μ s + μ (U N \ s) := (measure_mono hsub).trans (measure_union_le _ _)
  have hfin : μ (U N \ s) ≠ ∞ := ne_top_of_lt hN
  calc
    μ.real (U N) ≤ (μ s + μ (U N \ s)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hs, hfin⟩) hm
    _ = μ.real s + μ.real (U N \ s) := ENNReal.toReal_add hs hfin
    _ ≤ μ.real s + 1 := add_le_add (le_refl _) (by
      simpa only [measureReal_def, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hN.le)


/-- Replacing actual filling volume by full original volume pays the literal
added and missing masses, including the sign of the pressure coefficient. -/
theorem measureReal_weighted_error_le_added_missing {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s U : Set X} (hs : MeasurableSet s) (hU : MeasurableSet U)
    (hsfin : μ s ≠ ∞) (hUfin : μ U ≠ ∞) (value model : ℝ) :
    |value - μ.real s * model| ≤ |value - μ.real U * model| +
      (μ.real (U \ s) + μ.real (s \ U)) * |model| := by
  have hgap := abs_measureReal_sub_le_measureReal_symmDiff' hU.nullMeasurableSet
    hs.nullMeasurableSet hUfin hsfin
  rw [measureReal_symmDiff_eq hU hs hUfin hsfin] at hgap
  calc
    _ = |(value - μ.real U * model) + (μ.real U - μ.real s) * model| := by
      congr 1
      ring
    _ ≤ |value - μ.real U * model| + |(μ.real U - μ.real s) * model| := abs_add_le _ _
    _ = |value - μ.real U * model| + |μ.real U - μ.real s| * |model| := by rw [abs_mul]
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hgap (abs_nonneg model))

end OTSelector.Reconstruction
