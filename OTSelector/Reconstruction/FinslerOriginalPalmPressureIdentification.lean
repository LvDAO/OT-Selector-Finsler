import OTSelector.Reconstruction.FinslerOriginalReservePalmIdentification

/-!
# Palm identification of the marked Poisson pressure limit

This module reduces the (Palm) hypothesis of
FinslerOriginalReservePalmIdentification to a marked pressure representation plus
a retained-core comparison, and proves the limiting Palm identification.

The (Palm) hypothesis is

  p t <= int x, lam^(-(2/q)) * I x (t lam^(2/q))
            d(mu.withDensity (S.indicator (fun _ => ofReal lam)))

with retained density lam = 1 - rho, mu the Palm law of the candidate weighted
stationary matching and mu.real S^c <= rho.

1. **Density elimination** (palmIdentificationRHS_eq_retainedIntegral): the
   retained-core density integral is exactly lam^(1-2/q) times the retained
   region integral.  So (Palm) is equivalent to
   p t <= lam^(1-2/q) * int_{S} I x (t lam^(2/q)) dmu.

2. **Reduction to a marked pressure representation**
   (palmIdentification_of_pointwiseRepresentation): if the marked pressure limit
   is the Palm integral of a local readout J and J is pointwise dominated by the
   retained readout, then (Palm) holds.

3. **Limiting Palm identification** (retainedCorePalm_tendsto): along a sequence
   of retained regions whose complements are eventually missed almost surely,
   the normalized retained Palm pressure converges to the Palm integral
   int x, I x t dmu.

4. **The (Palm) hypothesis implies the Palm identification in the limit**
   (palmIdentification_limit): if the finite-rho (Palm) inequality holds along
   the sequence, then the marked pressure limit is at most the Palm integral of
   the local pressure at tilt t.

## Remaining sub-gap

The marked pressure representation p t = int x, J x dmu (identifying the
finite-volume optimal cost limit with a Palm readout of the candidate law) and
the pointwise comparison J <= lam^(1-2/q) * 1_S * I(t lam^(2/q)) remain the deep
analytic inputs; they are exactly the frozen-core finite-domination / Campbell
identification of the paper.  All order, density and convergence arguments are
proved here.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X]

/-- **Density elimination.**  The retained-core density integral with retained
density lam on S is lam^(1 - 2/q) times the integral over S at the dilated tilt. -/
theorem palmIdentificationRHS_eq_retainedIntegral
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S)
    {q : ℕ} (I : X → ℝ → ℝ) (t : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (∫ x, lam ^ (-(2 / (q : ℝ))) * I x (t * lam ^ (2 / (q : ℝ)))
        ∂(μ.withDensity (S.indicator (fun _ => ENNReal.ofReal lam)))) =
      lam ^ (1 - 2 / (q : ℝ)) *
        (∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) :=
  retainedPressure_indicator_scale (μ := μ) (S := S) (q := q) hS I t hlam

/-- **Reduction of (Palm) to a marked pressure representation plus a pointwise
comparison.**  If the marked pressure limit is the Palm integral of a local
readout J, and J is pointwise dominated by the retained readout, then (Palm)
holds. -/
theorem palmIdentification_of_pointwiseRepresentation
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S)
    {q : ℕ} (I : X → ℝ → ℝ) (t : ℝ) {lam : ℝ} (hlam : 0 < lam) {p : ℝ}
    (J : X → ℝ)
    (hrepr : p = ∫ x, J x ∂μ)
    (hJint : Integrable J μ)
    (hIint : Integrable (fun x => I x (t * lam ^ (2 / (q : ℝ)))) μ)
    (hpt : ∀ᵐ x ∂μ,
      J x ≤ lam ^ (1 - 2 / (q : ℝ)) *
        (S.indicator (fun y => I y (t * lam ^ (2 / (q : ℝ))))) x) :
    p ≤ ∫ x, lam ^ (-(2 / (q : ℝ))) * I x (t * lam ^ (2 / (q : ℝ)))
      ∂(μ.withDensity (S.indicator (fun _ => ENNReal.ofReal lam))) := by
  have hrewrite := palmIdentificationRHS_eq_retainedIntegral (q := q) μ hS I t hlam
  rw [hrewrite, hrepr]
  have hind : Integrable (S.indicator (fun x => I x (t * lam ^ (2 / (q : ℝ))))) μ :=
    hIint.indicator hS
  have hrint : Integrable (fun x => lam ^ (1 - 2 / (q : ℝ)) *
      S.indicator (fun x => I x (t * lam ^ (2 / (q : ℝ)))) x) μ :=
    hind.const_mul _
  have hmono := integral_mono_ae hJint hrint hpt
  have hconst : (∫ x, lam ^ (1 - 2 / (q : ℝ)) *
      S.indicator (fun x => I x (t * lam ^ (2 / (q : ℝ)))) x ∂μ) =
      lam ^ (1 - 2 / (q : ℝ)) *
        (∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) := by
    rw [integral_const_mul, integral_indicator hS]
  linarith [hmono, hconst]

/-- **Limiting Palm identification.**  Along a sequence of retained regions whose
complements are eventually missed almost surely, the normalized retained Palm
pressure converges to the Palm integral of the local pressure at the fixed
tilt. -/
theorem retainedCorePalm_tendsto
    (μ : Measure X) [IsFiniteMeasure μ]
    {q : ℕ} (hq2 : (2 : ℝ) ≤ (q : ℝ))
    (I : X → ℝ → ℝ) (t B : ℝ) (hB0 : 0 ≤ B)
    (hIbound : ∀ x u, |I x u| ≤ B)
    (hIcont : ∀ᵐ x ∂μ, ContinuousAt (fun u => I x u) t)
    (hImeas : ∀ u : ℝ, AEStronglyMeasurable (fun x => I x u) μ)
    (rho : ℕ → ℝ) (hrho : ∀ n, 0 < rho n) (hrho1 : ∀ n, rho n < 1)
    (hrho0 : Tendsto rho atTop (𝓝 0))
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hSae : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ S n) :
    Tendsto (fun n => (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
        (∫ x in S n, I x (t * (1 - rho n) ^ (2 / (q : ℝ))) ∂μ))
      atTop (𝓝 (∫ x, I x t ∂μ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hexp0 : 0 ≤ 1 - 2 / (q : ℝ) := by
    have h : 2 / (q : ℝ) ≤ 1 := (div_le_one hq0).mpr hq2
    linarith
  have hlam : ∀ n, 0 < 1 - rho n := fun n => by linarith [hrho1 n]
  have hlam1 : ∀ n, 1 - rho n ≤ 1 := fun n => by linarith [hrho n]
  have hfacle : ∀ n, (1 - rho n) ^ (1 - 2 / (q : ℝ)) ≤ 1 := fun n =>
    Real.rpow_le_one (hlam n).le (hlam1 n) hexp0
  have hfac0 : ∀ n, 0 ≤ (1 - rho n) ^ (1 - 2 / (q : ℝ)) := fun n =>
    Real.rpow_nonneg (hlam n).le _
  have hshift : Tendsto (fun n => 1 - rho n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hrho0
    simpa using h
  have hfac_t : Tendsto (fun n => (1 - rho n) ^ (1 - 2 / (q : ℝ))) atTop (𝓝 1) := by
    have h := hshift.rpow_const (p := 1 - 2 / (q : ℝ)) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    simpa [Real.one_rpow] using h
  have hbase_t : Tendsto (fun n => (1 - rho n) ^ (2 / (q : ℝ))) atTop (𝓝 1) := by
    have h := hshift.rpow_const (p := 2 / (q : ℝ)) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    simpa [Real.one_rpow] using h
  have hc_t : Tendsto (fun n => t * (1 - rho n) ^ (2 / (q : ℝ))) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).mul hbase_t
  let F : ℕ → X → ℝ := fun n x =>
    (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
      (S n).indicator (fun x => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) x
  have hfn : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact (((hImeas _).indicator (hS n)).const_mul _)
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ B := by
    intro n
    filter_upwards with x
    have habs : |(S n).indicator (fun x => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) x| ≤ B := by
      by_cases hx : x ∈ S n
      · rw [Set.indicator_of_mem hx]
        exact hIbound x _
      · rw [show (S n).indicator (fun x => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) x = 0 by
          simp [Set.indicator, hx]]
        simpa using hB0
    have hfac_abs : |(1 - rho n) ^ (1 - 2 / (q : ℝ))| = (1 - rho n) ^ (1 - 2 / (q : ℝ)) :=
      abs_of_nonneg (hfac0 n)
    show ‖(1 - rho n) ^ (1 - 2 / (q : ℝ)) *
      (S n).indicator (fun x => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) x‖ ≤ B
    rw [Real.norm_eq_abs, abs_mul, hfac_abs]
    calc (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
          |(S n).indicator (fun x => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) x|
        ≤ 1 * B := mul_le_mul (hfacle n) habs (abs_nonneg _) (by norm_num)
      _ = B := one_mul B
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (I x t)) := by
    filter_upwards [hSae, hIcont] with x hmem hcont
    have harg : Tendsto (fun n => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) atTop (𝓝 (I x t)) :=
      hcont.tendsto.comp hc_t
    have hprod : Tendsto (fun n => (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
        I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) atTop (𝓝 (1 * I x t)) :=
      hfac_t.mul harg
    have heq : ∀ᶠ n in atTop, F n x = (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
        I x (t * (1 - rho n) ^ (2 / (q : ℝ))) := by
      filter_upwards [hmem] with n hn
      show (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
        (S n).indicator (fun x => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) x = _
      rw [Set.indicator_of_mem hn]
    simpa only [one_mul] using hprod.congr' (heq.mono fun n hn => hn.symm)
  have hmain := tendsto_integral_of_dominated_convergence (fun _ => B) hfn
    (integrable_const B) hbound hlim
  have hrewrite : ∀ n, (∫ x, F n x ∂μ) = (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
      (∫ x in S n, I x (t * (1 - rho n) ^ (2 / (q : ℝ))) ∂μ) := by
    intro n
    show (∫ x, (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
      (S n).indicator (fun x => I x (t * (1 - rho n) ^ (2 / (q : ℝ)))) x ∂μ) = _
    rw [integral_const_mul, integral_indicator (hS n)]
  simpa only [hrewrite] using hmain

/-- **The (Palm) hypothesis gives the Palm identification in the limit.**  If the
finite-rho (Palm) inequality holds along a sequence of retained regions, then
the marked pressure limit is at most the Palm integral of the local pressure at
the fixed tilt. -/
theorem palmIdentification_limit
    (μ : Measure X) [IsFiniteMeasure μ]
    {q : ℕ} (hq2 : (2 : ℝ) ≤ (q : ℝ))
    (I : X → ℝ → ℝ) (t B : ℝ) (hB0 : 0 ≤ B)
    (hIbound : ∀ x u, |I x u| ≤ B)
    (hIcont : ∀ᵐ x ∂μ, ContinuousAt (fun u => I x u) t)
    (hImeas : ∀ u : ℝ, AEStronglyMeasurable (fun x => I x u) μ)
    (rho : ℕ → ℝ) (hrho : ∀ n, 0 < rho n) (hrho1 : ∀ n, rho n < 1)
    (hrho0 : Tendsto rho atTop (𝓝 0))
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hSae : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ S n)
    {p : ℝ}
    (hpalm : ∀ n, p ≤ ∫ x, (1 - rho n) ^ (-(2 / (q : ℝ))) *
      I x (t * (1 - rho n) ^ (2 / (q : ℝ))) ∂(μ.withDensity ((S n).indicator (fun _ => ENNReal.ofReal (1 - rho n))))) :
    p ≤ ∫ x, I x t ∂μ := by
  have hlim := retainedCorePalm_tendsto μ hq2 I t B hB0 hIbound hIcont hImeas rho hrho
    hrho1 hrho0 S hS hSae
  have hle : ∀ n, p ≤ (1 - rho n) ^ (1 - 2 / (q : ℝ)) *
      (∫ x in S n, I x (t * (1 - rho n) ^ (2 / (q : ℝ))) ∂μ) := by
    intro n
    have h := hpalm n
    rwa [palmIdentificationRHS_eq_retainedIntegral (q := q) μ (hS n) I t
      (by linarith [hrho n, hrho1 n])] at h
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.Eventually.of_forall hle)

end OTSelector.Reconstruction
