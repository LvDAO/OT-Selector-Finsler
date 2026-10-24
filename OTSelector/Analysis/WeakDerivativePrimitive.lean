import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
## Lemma skeleton

* **Conditions:** Integrable scalar functions satisfying all fixed-endpoint C1 test identities.
* **Objects:** An almost-everywhere constant, or an absolutely continuous primitive representative.
* **Proof detail:** Subtract an integral primitive, annihilate zero-mean tests, then apply the fundamental constant principle.

## Mathematical sources

* J. M. Ball; E. C. M. Crooks, *Local minimizers and planar interfaces in a phase-transition model with interfacial energy (2011)*, Section 3, proof of Lemma 3.1, equation (3.5), p. 512 (du Bois–Reymond constant principle).
  https://people.maths.ox.ac.uk/~ball/Papers/BallAndCrooks2011.pdf#page=12
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 225E (absolutely continuous functions as indefinite integrals), 225F (integration by parts).
  https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29

**Relationship to the sources:** The paper illustrates du Bois–Reymond; the L1 finite-interval representative theorem is proved here using integration by parts and test-function extensionality.
-/

/-!
# Absolutely continuous representatives of scalar weak derivatives

A scalar integrable function annihilating derivatives of all C1 fixed-endpoint tests
is almost everywhere constant. Consequently a scalar weak derivative identity on a
finite interval identifies the original integrable momentum almost everywhere with
an absolutely continuous primitive. Continuity or absolute continuity of the original
momentum is not assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace OTSelector.Geometry

/-- An integrable scalar function annihilating every C1 fixed-endpoint derivative
is almost everywhere equal to its interval average. -/
theorem ae_eq_average_of_integral_mul_deriv_eq_zero
    {p : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hp : IntervalIntegrable p volume a b)
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ a = 0 → φ b = 0 →
      (∫ t in a..b, p t * deriv φ t) = 0) :
    p =ᵐ[volume.restrict (Ioo a b)] (fun _ ↦ (∫ t in a..b, p t) / (b - a)) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp [Filter.EventuallyEq]
  let C := (∫ t in a..b, p t) / (b - a)
  have hf : Integrable (fun t ↦ p t - C) (volume.restrict (Ioo a b)) := by
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp
      (hp.sub intervalIntegrable_const)
  have hzero : ∀ᵐ t ∂volume.restrict (Ioo a b), p t - C = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
    intro g hg _
    let m := (∫ t in a..b, g t) / (b - a)
    let g₀ : ℝ → ℝ := fun t ↦ g t - m
    let φ : ℝ → ℝ := fun t ↦ ∫ s in a..t, g₀ s
    have hg₀ : Continuous g₀ := hg.continuous.sub continuous_const
    have hφd (t : ℝ) : HasDerivAt φ (g₀ t) t :=
      intervalIntegral.integral_hasDerivAt_right (hg₀.intervalIntegrable a t)
        hg₀.aestronglyMeasurable.stronglyMeasurableAtFilter hg₀.continuousAt
    have hφderiv : deriv φ = g₀ := funext (fun t ↦ (hφd t).deriv)
    have hφ : ContDiff ℝ 1 φ := by
      apply contDiff_one_iff_deriv.mpr
      refine ⟨fun t ↦ (hφd t).differentiableAt, ?_⟩
      rw [hφderiv]
      exact hg₀
    have hφa : φ a = 0 := by simp [φ]
    have hφb : φ b = 0 := by
      dsimp only [φ, g₀]
      rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable a b)
        intervalIntegrable_const, intervalIntegral.integral_const]
      dsimp only [m]
      simp only [smul_eq_mul]
      field_simp
      ring
    have hpg : IntervalIntegrable (fun t ↦ p t * g t) volume a b :=
      hp.mul_continuousOn hg.continuous.continuousOn
    have htestg := htest φ hφ hφa hφb
    rw [hφderiv] at htestg
    change (∫ t in a..b, p t * (g t - m)) = 0 at htestg
    simp_rw [mul_sub] at htestg
    rw [intervalIntegral.integral_sub hpg (hp.mul_const m),
      intervalIntegral.integral_mul_const] at htestg
    change (∫ t in Ioo a b, g t * (p t - C)) = 0
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    have hfun : (fun t ↦ g t * (p t - C)) = (fun t ↦ p t * g t - g t * C) := by
      funext t
      ring
    rw [hfun, intervalIntegral.integral_sub hpg
      ((hg.continuous.intervalIntegrable a b).mul_const C),
      intervalIntegral.integral_mul_const]
    convert htestg using 1
    dsimp [C, m]
    ring
  filter_upwards [hzero] with t ht
  exact sub_eq_zero.mp ht

/-- The scalar weak derivative identity constructs an absolutely continuous momentum
representative; the given momentum itself need only be interval integrable. -/
theorem exists_ae_eq_const_add_integral_of_weak_derivative
    {p q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : IntervalIntegrable p volume a b) (hq : IntervalIntegrable q volume a b)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ a = 0 → φ b = 0 →
      (∫ t in a..b, q t * φ t + p t * deriv φ t) = 0) :
    ∃ C : ℝ,
      (p =ᵐ[volume.restrict (Ioo a b)] (fun t ↦ C + ∫ s in a..t, q s)) ∧
      AbsolutelyContinuousOnInterval (fun t ↦ C + ∫ s in a..t, q s) a b := by
  let Q : ℝ → ℝ := fun t ↦ ∫ s in a..t, q s
  have hQ : AbsolutelyContinuousOnInterval Q a b :=
    hq.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc)
  have hQi : IntervalIntegrable Q volume a b := hQ.continuousOn.intervalIntegrable
  have htest : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ a = 0 → φ b = 0 →
      (∫ t in a..b, (p t - Q t) * deriv φ t) = 0 := by
    intro φ hφ hφa hφb
    have hφac : AbsolutelyContinuousOnInterval φ a b :=
      hφ.contDiffOn.absolutelyContinuousOnInterval
    have hparts := hQ.integral_mul_deriv_eq_deriv_mul hφac
    have hQderiv : (∫ t in a..b, deriv Q t * φ t) = ∫ t in a..b, q t * φ t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hq.ae_hasDerivAt_integral] with t ht htin
      have hd := ht (uIoc_subset_uIcc htin) a left_mem_uIcc
      change deriv (fun u ↦ ∫ s in a..u, q s) t * φ t = q t * φ t
      rw [hd.deriv]
    rw [hQderiv, hφa, hφb, mul_zero, mul_zero, sub_zero, zero_sub] at hparts
    have hw := hweak φ hφ hφa hφb
    rw [intervalIntegral.integral_add
      (hq.mul_continuousOn hφ.continuous.continuousOn)
      (hp.mul_continuousOn hφ.continuous_deriv_one.continuousOn)] at hw
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub
      (hp.mul_continuousOn hφ.continuous_deriv_one.continuousOn)
      (hQi.mul_continuousOn hφ.continuous_deriv_one.continuousOn)]
    linarith
  have heq := ae_eq_average_of_integral_mul_deriv_eq_zero hab (hp.sub hQi) htest
  let C := (∫ t in a..b, p t - Q t) / (b - a)
  refine ⟨C, ?_, ?_⟩
  · filter_upwards [heq] with t ht
    change p t - Q t = C at ht
    change p t = C + Q t
    linarith
  · have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ C) a b :=
      (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ ↦ C) (uIcc a b))
        |>.absolutelyContinuousOnInterval
    exact hc.fun_add hQ

end OTSelector.Geometry
