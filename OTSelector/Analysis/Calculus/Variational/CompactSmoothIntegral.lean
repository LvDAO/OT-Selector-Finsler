import Mathlib.Analysis.Calculus.ContDiff.Comp
import OTSelector.Analysis.CompactFrechetIntegral
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CompactSmoothIntegral.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CompactSmoothIntegral`; the selected original proof blocks follow. -/
section

/-!
Conditions: An integrand is jointly smooth near the compact parameter/time trace, with the stated normed target and actual interval-integral convention.

Objects: Smoothness of the actual parameter interval integral to every specified order.

Proof detail: Localize to a compact thickening, commute differentiation with the integral under uniform derivative bounds and iterate.

Sources: Jiří Lebl, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters) (https://www.jirka.org/ra/html/sec_diffunderint.html); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Normed-target/parameter extension of the finite-dimensional Leibniz rule. It does not add an unstated CompleteSpace hypothesis to totalized integrals.
-/

/-!
# Smooth parameter dependence of actual compact interval integrals

Joint smoothness on an open neighborhood of a compact time trace implies smoothness
of the actual parameter integral. Compactness supplies all local derivative bounds,
measurability, and integrability. The integrands may take values in any real normed space, so
successive genuine Frechet derivatives can be integrated without an additional oracle.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

universe u v
namespace OTSelector.Geometry

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- C1 regularity on an open neighborhood of the compact central trace suffices to
interchange the actual parameter derivative with the actual interval integral. -/
theorem hasFDerivAt_intervalIntegral_of_contDiffOn_normed
    {f : W × ℝ → V} {D : Set (W × ℝ)} {s₀ : W} {a b : ℝ}
    (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D) (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D) :
    HasFDerivAt (fun s ↦ ∫ t in a..b, f (s, t))
      (∫ t in a..b, (fderiv ℝ f (s₀, t)).comp (ContinuousLinearMap.inl ℝ W ℝ)) s₀ := by
  obtain ⟨r, hr, hstrip⟩ := exists_pos_compact_parameter_ball_strip hD htrace
  let S : Set W := Metric.closedBall s₀ r
  have hs₀ : s₀ ∈ S := Metric.mem_closedBall_self hr.le
  have hS : S ∈ 𝓝 s₀ := Metric.closedBall_mem_nhds s₀ hr
  let g : W × ℝ → W →L[ℝ] V := fun z ↦
    (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ W ℝ)
  have hg : ContinuousOn g D :=
    (hf.continuousOn_fderiv_of_isOpen hD le_rfl).clm_comp continuousOn_const
  have hderiv : ∀ s ∈ S, ∀ t ∈ Icc a b,
      HasFDerivAt (fun u ↦ f (u, t)) (g (s, t)) s := by
    intro s hs t ht
    have hfd := (hf.contDiffAt
      (hD.mem_nhds (show (s, t) ∈ D from hstrip ⟨hs, ht⟩))).differentiableAt_one
    exact hfd.hasFDerivAt.comp s (hasFDerivAt_prodMk_left s t)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ r).prod isCompact_Icc).exists_bound_of_continuousOn
    (hg.mono hstrip)
  have hint : ∀ s ∈ S, IntervalIntegrable (fun t ↦ f (s, t)) volume a b := by
    intro s hs
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ hstrip ⟨hs, ht⟩)
  have hgint : IntervalIntegrable (fun t ↦ g (s₀, t)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ hstrip ⟨hs₀, ht⟩)
  have hmeas : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable (fun t ↦ f (s, t)) (volume.restrict (Ι a b)) := by
    filter_upwards [hS] with s hs
    exact (hint s hs).aestronglyMeasurable_restrict_uIoc
  have htmem : ∀ t ∈ Ι a b, t ∈ Icc a b := by
    rw [uIoc_of_le hab]
    exact fun t ht ↦ ⟨ht.1.le, ht.2⟩
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ s ∈ S, ‖g (s, t)‖ ≤ C :=
    Filter.Eventually.of_forall (fun t ht s hs ↦ hC (s, t) ⟨hs, htmem t ht⟩)
  have hdiff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ s ∈ S,
      HasFDerivAt (fun u ↦ f (u, t)) (g (s, t)) s :=
    Filter.Eventually.of_forall (fun t ht s hs ↦ hderiv s hs t (htmem t ht))
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    hS hmeas (hint s₀ hs₀) hgint.aestronglyMeasurable_restrict_uIoc hbound
    (intervalIntegrable_const) hdiff
  exact h

private theorem contDiffOn_nat_intervalIntegral_of_smooth
    {U : Set W} {D : Set (W × ℝ)} (hU : IsOpen U) (hD : IsOpen D)
    {a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ s ∈ U, ∀ t ∈ Icc a b, (s, t) ∈ D)
    (n : ℕ) {V' : Type (max u v)} [NormedAddCommGroup V']
    [NormedSpace ℝ V'] {f : W × ℝ → V'}
    (hf : ContDiffOn ℝ ∞ f D) :
    ContDiffOn ℝ n (fun s ↦ ∫ t in a..b, f (s, t)) U := by
  induction n generalizing V' with
  | zero =>
    apply contDiffOn_zero.mpr
    intro s hs
    exact (hasFDerivAt_intervalIntegral_of_contDiffOn_normed hD (hf.of_le (by simp))
      hab (htrace s hs)).continuousAt.continuousWithinAt
  | succ n ih =>
    let g : W × ℝ → W →L[ℝ] V' := fun q ↦
      (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ W ℝ)
    have hg : ContDiffOn ℝ ∞ g D :=
      (hf.fderiv_of_isOpen hD (m := ∞) (by simp)).clm_comp contDiffOn_const
    have hgi : ContDiffOn ℝ n (fun s ↦ ∫ t in a..b, g (s, t)) U := ih hg
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n := (n : ℕ∞ω)) hU.uniqueDiffOn).mpr
    refine ⟨by simp, fun s ↦ ∫ t in a..b, g (s, t), hgi, ?_⟩
    intro s hs
    exact (hasFDerivAt_intervalIntegral_of_contDiffOn_normed hD (hf.of_le (by simp))
      hab (htrace s hs)).hasFDerivWithinAt

/-- An actual compact interval integral is smooth on every open parameter set whose
whole compact time strip stays in the integrand's original open smoothness domain. -/
theorem contDiffOn_infty_intervalIntegral_of_contDiffOn
    {f : W × ℝ → V} {U : Set W} {D : Set (W × ℝ)}
    (hU : IsOpen U) (hD : IsOpen D) (hf : ContDiffOn ℝ ∞ f D)
    {a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ s ∈ U, ∀ t ∈ Icc a b, (s, t) ∈ D) :
    ContDiffOn ℝ ∞ (fun s ↦ ∫ t in a..b, f (s, t)) U := by
  let g : W × ℝ → W →L[ℝ] V := fun q ↦
    (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ W ℝ)
  have hg : ContDiffOn ℝ ∞ g D :=
    (hf.fderiv_of_isOpen hD (m := ∞) (by simp)).clm_comp contDiffOn_const
  have hgi : ContDiffOn ℝ ∞ (fun s ↦ ∫ t in a..b, g (s, t)) U := by
    apply contDiffOn_infty.mpr
    intro n
    exact contDiffOn_nat_intervalIntegral_of_smooth hU hD hab htrace n hg
  have hd (s : W) (hs : s ∈ U) :
      HasFDerivAt (fun r ↦ ∫ t in a..b, f (r, t)) (∫ t in a..b, g (s, t)) s :=
    hasFDerivAt_intervalIntegral_of_contDiffOn_normed hD (hf.of_le (by simp))
      hab (htrace s hs)
  apply (contDiffOn_infty_iff_fderiv_of_isOpen hU).mpr
  refine ⟨fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt, ?_⟩
  exact hgi.congr (fun s hs ↦ (hd s hs).fderiv)

/-- Smoothness near just the compact central trace gives actual smooth dependence of
the interval integral at the central parameter; no external domination is required. -/
theorem contDiffAt_infty_intervalIntegral_of_contDiffOn
    {f : W × ℝ → V} {D : Set (W × ℝ)} {s₀ : W} {a b : ℝ}
    (hD : IsOpen D) (hf : ContDiffOn ℝ ∞ f D) (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D) :
    ContDiffAt ℝ ∞ (fun s ↦ ∫ t in a..b, f (s, t)) s₀ := by
  obtain ⟨r, hr, hstrip⟩ := exists_pos_compact_parameter_ball_strip hD htrace
  have h := contDiffOn_infty_intervalIntegral_of_contDiffOn Metric.isOpen_ball hD hf hab
    (fun s hs t ht ↦ hstrip ⟨Metric.ball_subset_closedBall hs, ht⟩)
  exact h.contDiffAt (Metric.ball_mem_nhds s₀ hr)

end OTSelector.Geometry

end
