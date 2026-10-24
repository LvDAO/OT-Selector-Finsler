import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded

/-!
## Lemma skeleton

* **Conditions:** C1 scalar function on an open neighborhood of a compact parameter trace.
* **Objects:** The parameter derivative of an interval integral.
* **Proof detail:** Compactness supplies one strip and derivative bound, then apply differentiation under the integral.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters).
  https://www.jirka.org/ra/html/sec_diffunderint.html

**Relationship to the sources:** The open-domain compact-strip wrapper derives the rectangle hypotheses of Leibniz rather than adding them as an oracle.
-/

/-!
# Differentiation of an actual integral on a compact parameter strip

A scalar function that is C1 on an open neighborhood of a compact parameter trace
can be differentiated under the time integral. Compactness supplies a common parameter
neighborhood and a constant bound for the actual parameter derivative. Slice continuity
supplies all integrability and measurability facts; none is a public input.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace OTSelector.Geometry

/-- An open set containing a compact vertical trace contains a closed rectangular strip
of positive width around that trace. The statement also covers an empty time interval. -/
theorem exists_pos_compact_parameter_strip
    {D : Set (ℝ × ℝ)} {s₀ a b : ℝ}
    (hD : IsOpen D) (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D) :
    ∃ r : ℝ, 0 < r ∧ Icc (s₀ - r) (s₀ + r) ×ˢ Icc a b ⊆ D := by
  have hprod : ({s₀} : Set ℝ) ×ˢ Icc a b ⊆ D := by
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
  simpa only [Real.closedBall_eq_Icc] using hz.1


/-- C1 regularity on an open neighborhood of the compact central trace suffices to
interchange the actual parameter derivative with the actual interval integral. -/
theorem hasDerivAt_intervalIntegral_of_contDiffOn
    {f : ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ)} {s₀ a b : ℝ}
    (hD : IsOpen D) (hf : ContDiffOn ℝ 1 f D) (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D) :
    HasDerivAt (fun s ↦ ∫ t in a..b, f (s, t))
      (∫ t in a..b, deriv (fun r ↦ f (r, t)) s₀) s₀ := by
  obtain ⟨r, hr, hstrip⟩ := exists_pos_compact_parameter_strip hD htrace
  let S : Set ℝ := Icc (s₀ - r) (s₀ + r)
  have hs₀ : s₀ ∈ S := ⟨by linarith, by linarith⟩
  have hS : S ∈ 𝓝 s₀ := Icc_mem_nhds (by linarith) (by linarith)
  let g : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ f z (1, 0)
  have hg : ContinuousOn g D :=
    (hf.continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const
  have hderiv : ∀ s ∈ S, ∀ t ∈ Icc a b,
      HasDerivAt (fun u ↦ f (u, t)) (g (s, t)) s := by
    intro s hs t ht
    have hfd := (hf.contDiffAt
      (hD.mem_nhds (show (s, t) ∈ D from hstrip ⟨hs, ht⟩))).differentiableAt_one
    exact hfd.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
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
      HasDerivAt (fun u ↦ f (u, t)) (g (s, t)) s :=
    Filter.Eventually.of_forall (fun t ht s hs ↦ hderiv s hs t (htmem t ht))
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hS hmeas (hint s₀ hs₀) hgint.aestronglyMeasurable_restrict_uIoc hbound
    (intervalIntegrable_const) hdiff
  have heq : (∫ t in a..b, g (s₀, t)) =
      ∫ t in a..b, deriv (fun u ↦ f (u, t)) s₀ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (hderiv s₀ hs₀ t ht).deriv.symm
  exact heq ▸ h.2

end OTSelector.Geometry
