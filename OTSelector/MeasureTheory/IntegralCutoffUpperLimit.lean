import OTSelector.MeasureTheory.EventualUpperCutoffs
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalPressureCutoffIntegralUpper.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalPressureCutoffIntegralUpper`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IntegralCutoffUpperLimit

## Lemma skeleton

* **Conditions:** Finite original root law, integrable true reference, a measurable approximation sequence bounded below by one fixed constant and with almost-everywhere eventual pressure upper control.
* **Objects:** Eventually large retained sets with integrable approximating pressure and an upper integral within any tolerance of the true reference mean.
* **Proof detail:** Take pressure sublevel cutoffs, whose bad mass vanishes. On retained sets squeeze between the fixed lower bound and reference+epsilon, and control reference integral on discarded sets by absolute continuity of the integral.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=107): Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=105): Section 3B, Theorem 3.28, pp. 90–91.

Source relation (composition): Retained-set upper-limit integration; no global domination or integrability of every approximation on the whole space is assumed.
-/

/-! Deterministic original root cutoffs integrate true pressure upper limits
using only integrability of the true pressure and its physical probe lower bound. -/
open Set Function MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true pressure upper limit and the physical nonnegative-kinetic probe
lower bound produce original root cutoffs of any requested lost mass, with
actual cutoff integral upper. No majorant for the approximating pressures is
assumed; cutoff integrability is derived internally. -/
theorem exists_original_pressure_cutoff_integral_upper
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℕ → X → ℝ) (pref : X → ℝ)
    (hp : ∀ n, Measurable (p n)) (hpref : Integrable pref μ)
    (hprefMeas : Measurable pref)
    {B : ℝ} (hB : 0 ≤ B) (hlower : ∀ n, ∀ᵐ x ∂μ, -B ≤ p n x)
    (hupper : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, p n x < pref x + ε) :
    ∀ budget tolerance, 0 < budget → 0 < tolerance →
      ∀ᶠ n in atTop, ∃ K : Set X, MeasurableSet K ∧ μ.real Kᶜ < budget ∧
        IntegrableOn (p n) K μ ∧
        (∫ x in K, p n x ∂μ) < (∫ x, pref x ∂μ) + tolerance := by
  intro budget tolerance hbudget htolerance
  let ε := tolerance / (2 * (μ.real univ + 1))
  have hε : 0 < ε := div_pos htolerance (by positivity)
  have hεsmall : ε * μ.real univ ≤ tolerance / 2 := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2 * (μ.real univ + 1) by positivity)).mpr
    nlinarith only [htolerance,measureReal_nonneg (μ := μ) (s := univ)]
  obtain ⟨K,hK,hmass,hcontrol⟩ := exists_original_pressure_root_cutoffs μ p pref hp hprefMeas hupper hε
  have hprefLower : ∀ᵐ x ∂μ, -B ≤ pref x := by
    filter_upwards [hupper,ae_all_iff.mpr hlower] with x hx hxlow
    by_contra hn
    have hpos : 0 < (-B - pref x) / 2 := by linarith only [hn]
    obtain ⟨n,hn⟩ := (hx _ hpos).exists
    have hlow := hxlow n
    linarith only [hn,hlow,hpos]
  have hdomI : Integrable (fun x ↦ |pref x| + ε + B) μ :=
    (hpref.abs.add (integrable_const ε)).add (integrable_const B)
  have hI n : Integrable ((K n).indicator (p n)) μ := by
    apply hdomI.mono' ((hp n).aestronglyMeasurable.indicator (hK n))
    filter_upwards [hlower n] with x hxlow
    by_cases hx : x ∈ K n
    · rw [indicator_of_mem hx,Real.norm_eq_abs]
      have hup := hcontrol n x hx
      have hpos := le_abs_self (pref x)
      have habs := abs_nonneg (pref x)
      exact abs_le.mpr ⟨by linarith only [hxlow,habs,hε],by linarith only [hup,hpos,hB]⟩
    · rw [indicator_of_notMem hx,norm_zero]
      exact add_nonneg (add_nonneg (abs_nonneg _) hε.le) hB
  have htailI n : Integrable ((K n)ᶜ.indicator (fun _ ↦ B)) μ :=
    (integrable_const B).indicator (hK n).compl
  have hcompare n : (∫ x in K n, p n x ∂μ) ≤
      (∫ x, pref x ∂μ) + ε * μ.real univ + B * μ.real (K n)ᶜ := by
    have hmono : (∫ x, (K n).indicator (p n) x ∂μ) ≤
        ∫ x, pref x + ε + (K n)ᶜ.indicator (fun _ ↦ B) x ∂μ := by
      apply integral_mono_ae (hI n) ((hpref.add (integrable_const ε)).add (htailI n))
      filter_upwards [hprefLower] with x hx
      change (K n).indicator (p n) x ≤ pref x + ε + (K n)ᶜ.indicator (fun _ ↦ B) x
      by_cases hmem : x ∈ K n
      · simp only [indicator_of_mem hmem,indicator_of_notMem (show x ∉ (K n)ᶜ by exact not_not.mpr hmem),add_zero]
        exact hcontrol n x hmem
      · simp only [indicator_of_notMem hmem,indicator_of_mem (show x ∈ (K n)ᶜ from hmem)]
        linarith only [hx,hε]
    have hconstI : Integrable (fun _x : X ↦ ε) μ := integrable_const ε
    have hbaseI : Integrable (fun x ↦ pref x + ε) μ := hpref.add hconstI
    rw [integral_indicator (hK n),
      integral_add hbaseI (htailI n),
      integral_add hpref hconstI,integral_const,
      integral_indicator (hK n).compl,integral_const] at hmono
    simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hmono
  have htail : Tendsto (fun n ↦ B * μ.real (K n)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hmass.const_mul B
  filter_upwards [(tendsto_order.mp hmass).2 budget hbudget,
    (tendsto_order.mp htail).2 (tolerance / 2) (half_pos htolerance)] with n hmassN htailN
  refine ⟨K n,hK n,hmassN,(integrable_indicator_iff (hK n)).mp (hI n),?_⟩
  linarith only [hcompare n,hεsmall,htailN]

end OTSelector.Reconstruction

end
end
