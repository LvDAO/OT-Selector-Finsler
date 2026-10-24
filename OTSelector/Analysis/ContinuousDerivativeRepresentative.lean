import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
## Lemma skeleton

* **Conditions:** An absolutely continuous Banach-valued curve and a continuous representative of its almost-everywhere derivative.
* **Objects:** The actual derivative at every interior time.
* **Proof detail:** Recover the curve as its derivative integral, replace the a.e. representative and differentiate the continuous primitive.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 225E (absolutely continuous functions as indefinite integrals), 225F (integration by parts).
  https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** The scalar FTC principle is in Fremlin; Banach-valued representatives and Lean interval endpoints are proved formal extensions.
-/

/-!
# Pointwise derivatives from continuous almost-everywhere representatives

Absolute continuity of a position curve upgrades its continuous AE velocity to the
actual derivative at every interior time. For an integrable forcing, a continuous
AE representative similarly differentiates the original primitive everywhere in the
interior. These are Banach-valued results and do not presuppose a C1 position curve.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An absolutely continuous curve with a continuous AE derivative has that actual
derivative at every interior time. Absolute continuity prevents a singular remainder. -/
theorem hasDerivAt_of_absolutelyContinuous_of_continuous_ae_derivative
    {x v : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hx : AbsolutelyContinuousOnInterval x a b) (hv : ContinuousOn v (Icc a b))
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt x (v t) t) :
    ∀ t ∈ Ioo a b, HasDerivAt x (v t) t := by
  let V : ℝ → E := fun t ↦ v (projIcc a b hab t)
  have hV : Continuous V :=
    (continuousOn_iff_continuous_domRestrict.mp hv).comp continuous_projIcc
  have hVeq (t : ℝ) (ht : t ∈ Icc a b) : V t = v t := by
    simp only [V, projIcc_of_mem _ ht]
  let Q : ℝ → E := fun t ↦ ∫ s in a..t, V s
  have hQd (t : ℝ) : HasDerivAt Q (V t) t :=
    intervalIntegral.integral_hasDerivAt_right (hV.intervalIntegrable a t)
      (hV.stronglyMeasurableAtFilter volume (𝓝 t)) hV.continuousAt
  have hQderiv : deriv Q = V := funext (fun t ↦ (hQd t).deriv)
  have hQ : ContDiff ℝ 1 Q := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t ↦ (hQd t).differentiableAt, ?_⟩
    rwa [hQderiv]
  have hQac : AbsolutelyContinuousOnInterval Q a b :=
    hQ.contDiffOn.absolutelyContinuousOnInterval
  have hderiv' : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt x (v t) t := by
    rw [uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc]
    exact hderiv
  have hzero : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun s ↦ x s - Q s) 0 t := by
    filter_upwards [ae_imp_of_ae_restrict hderiv'] with t ht htin
    have htin' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using htin
    have hd := (ht htin).fun_sub (hQd t)
    simpa only [hVeq t htin', sub_self] using hd
  obtain ⟨C, hC⟩ := (hx.fun_sub hQac).const_of_ae_hasDerivAt_zero hzero
  intro t ht
  have heq : x =ᶠ[𝓝 t] (fun s ↦ C + Q s) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    have hc := hC s (by simpa only [uIcc_of_le hab] using hs)
    exact sub_eq_iff_eq_add.mp hc
  have hd := ((hQd t).const_add C).congr_of_eventuallyEq heq
  simpa only [hVeq t (Ioo_subset_Icc_self ht)] using hd

/-- A continuous AE representative of an integrable forcing is the pointwise actual
derivative of the original integral primitive throughout the open interval. -/
theorem hasDerivAt_integral_of_continuous_ae_representative
    {q Q : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hq : IntervalIntegrable q volume a b) (hQ : ContinuousOn Q (Icc a b))
    (heq : q =ᵐ[volume.restrict (Ioo a b)] Q) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u ↦ ∫ s in a..u, q s) (Q t) t := by
  have hqt : IntervalIntegrable q volume a t := hq.mono_set (by
    rw [uIcc_of_le ht.1.le, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2.le)
  have hmeas : StronglyMeasurableAtFilter q (𝓝 t) volume :=
    ⟨Ioc a b, Ioc_mem_nhds ht.1 ht.2, hq.1.aestronglyMeasurable⟩
  have hevent : q =ᶠ[𝓝 t ⊓ ae volume] Q := by
    filter_upwards [(ae_imp_of_ae_restrict heq).filter_mono inf_le_right,
      (show ∀ᶠ s in 𝓝 t, s ∈ Ioo a b from isOpen_Ioo.mem_nhds ht).filter_mono inf_le_left] with s hs hsin
    exact hs hsin
  have hlim : Tendsto q (𝓝 t ⊓ ae volume) (𝓝 (Q t)) :=
    ((hQ.continuousAt (Icc_mem_nhds ht.1 ht.2)).mono_left inf_le_left).congr' hevent.symm
  exact intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right hqt hmeas hlim

end OTSelector.Geometry
