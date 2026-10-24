import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
## Lemma skeleton

* **Conditions:** C1 scalar function on a compact time trace with normed parameter space.
* **Objects:** The Fréchet derivative of the interval integral.
* **Proof detail:** Obtain one compact-strip derivative bound and use the Banach derivative integral theorem.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters).
  https://www.jirka.org/ra/html/sec_diffunderint.html
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** The source treats real/finitely many parameters; the Lean theorem proves the normed-space Fréchet generalization, not a verbatim theorem from Lebl.
-/

/-!
# Actual Frechet differentiation over a compact time segment

A scalar function that is C1 on an open neighborhood of a compact parameter trace
can be differentiated under the time integral. Compactness supplies a common parameter
neighborhood and a constant bound for the actual parameter derivative. Slice continuity
supplies all integrability and measurability facts; none is a public input.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace OTSelector.Geometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- An open set containing a compact vertical trace contains a closed ball strip
of positive width around that trace. The statement also covers an empty time interval. -/
theorem exists_pos_compact_parameter_ball_strip
    {D : Set (W × ℝ)} {s₀ : W} {a b : ℝ}
    (hD : IsOpen D) (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall s₀ r ×ˢ Icc a b ⊆ D := by
  have hprod : ({s₀} : Set W) ×ˢ Icc a b ⊆ D := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have hs' : s = s₀ := hs
    subst s
    exact htrace t ht
  obtain ⟨U, V, hU, _, hsU, hIV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hD hprod
  obtain ⟨r, hr, hball⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall s₀ r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hsU (mem_singleton s₀)))
  refine ⟨r, hr, ?_⟩
  intro z hz
  apply hUV
  refine ⟨hball ?_, hIV hz.2⟩
  exact hz.1


/-- C1 regularity on an open neighborhood of the compact central trace suffices to
interchange the actual parameter derivative with the actual interval integral. -/
theorem hasFDerivAt_intervalIntegral_of_contDiffOn
    {f : W × ℝ → ℝ} {D : Set (W × ℝ)} {s₀ : W} {a b : ℝ}
    (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D) (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D) :
    HasFDerivAt (fun s ↦ ∫ t in a..b, f (s, t))
      (∫ t in a..b, fderiv ℝ (fun r ↦ f (r, t)) s₀) s₀ := by
  obtain ⟨r, hr, hstrip⟩ := exists_pos_compact_parameter_ball_strip hD htrace
  let S : Set W := Metric.closedBall s₀ r
  have hs₀ : s₀ ∈ S := Metric.mem_closedBall_self hr.le
  have hS : S ∈ 𝓝 s₀ := Metric.closedBall_mem_nhds s₀ hr
  let g : W × ℝ → W →L[ℝ] ℝ := fun z ↦
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
  have heq : (∫ t in a..b, g (s₀, t)) =
      ∫ t in a..b, fderiv ℝ (fun u ↦ f (u, t)) s₀ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (hderiv s₀ hs₀ t ht).fderiv.symm
  exact heq ▸ h

end OTSelector.Geometry
