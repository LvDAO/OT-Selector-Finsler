import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Analysis.Calculus.DensityOneDifferential

Conditions: A set has Haar density one at the point, a map is constant there, and the explicit within-set or ambient actual Fréchet derivative exists.

Objects: Zero derivative and uniqueness/equality of the actual differentials.

Proof detail: A nonzero linear differential would remain nonzero on an open cone. Its first-order error contradicts equality on a density-one set; apply the zero result to differences for uniqueness.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation: A locally proved density-one uniqueness consequence; finite-dimensional Haar and normed-target versions are explicit generalizations of the Euclidean density argument.
-/

/-!
# Differentials determined by density-one sets

A first-order derivative along a set of full local Haar density is determined by the
values on that set. In particular, a function constant on the set has zero differential
at each density-one point where the indicated derivative exists. This is a pointwise
statement; no almost-everywhere differentiability conclusion is substituted for it.
-/

open Set Filter Metric Bornology MeasureTheory MeasureTheory.Measure
open scoped Topology Pointwise ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- A within-set derivative of a function constant at a Haar density-one point vanishes.
The set need not be measurable, and the codomain need not be finite dimensional. -/
theorem hasFDerivWithinAt_eq_zero_of_density_one {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {f : E → F} {A : E →L[ℝ] F}
    (hf : HasFDerivWithinAt f A s x) (heq : ∀ y ∈ s, f y = f x) : A = 0 := by
  -- The rescaled-ball argument is the pointwise core of mathlib
  -- `ApproximatesLinearOn.norm_fderiv_sub_le`, specialized to a constant restriction.
  ext z
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  suffices H : ∀ ε, 0 < ε → ‖A z‖ ≤ ε * (‖z‖ + ε) + ‖A‖ * ε by
    have hlim : Tendsto (fun ε : ℝ ↦ ε * (‖z‖ + ε) + ‖A‖ * ε)
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (show Continuous (fun ε : ℝ ↦ ε * (‖z‖ + ε) + ‖A‖ * ε)
        by fun_prop).tendsto' (0 : ℝ) 0 (by simp) |>.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin] using H
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z hε).ne'
  obtain ⟨ρ, hρ, happrox⟩ :
      ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E | ‖f y - f x - A (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 (hf.isLittleO.def hε)
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x hρ)
  obtain ⟨r, ⟨y, ⟨hy, hys⟩⟩, hrball, hr⟩ :
      ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, ha, hya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hys
    rcases hys with ⟨a, ha, he⟩
    exact ⟨a, ha, by simp only [he, add_neg_cancel_left]⟩
  have hnorma : ‖a‖ ≤ ‖z‖ + ε := by
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := add_le_add_right (mem_closedBall_iff_norm.1 ha) _
  have hAa : ‖A a‖ ≤ ε * (‖z‖ + ε) := by
    have h : ‖f y - f x - A (y - x)‖ ≤ ε * ‖y - x‖ :=
      happrox ⟨hrball hys, hy⟩
    rw [heq y hy, sub_self, zero_sub, norm_neg, hya] at h
    simp only [add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.le] at h
    have h' : ‖A a‖ ≤ ε * ‖a‖ := by nlinarith
    exact h'.trans (mul_le_mul_of_nonneg_left hnorma hε.le)
  calc
    ‖A z‖ = ‖A a + A (z - a)‖ := by rw [← map_add, add_sub_cancel]
    _ ≤ ‖A a‖ + ‖A (z - a)‖ := norm_add_le _ _
    _ ≤ ε * (‖z‖ + ε) + ‖A‖ * ‖z - a‖ :=
      add_le_add hAa (A.le_opNorm _)
    _ ≤ ε * (‖z‖ + ε) + ‖A‖ * ε := by
      gcongr
      exact mem_closedBall_iff_norm'.1 ha

/-- A genuine Haar density-one point has unique within-set derivatives, even without
measurability of the set or finite dimensionality of the target. -/
theorem hasFDerivWithinAt_unique_of_density_one {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {f : E → F} {A B : E →L[ℝ] F}
    (hA : HasFDerivWithinAt f A s x) (hB : HasFDerivWithinAt f B s x) : A = B := by
  apply sub_eq_zero.mp
  exact hasFDerivWithinAt_eq_zero_of_density_one μ hx (hA.sub hB) (by simp)

/-- The ambient derivative of a function constant on a density-one set is zero. -/
theorem hasFDerivAt_eq_zero_of_density_one {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {f : E → F} {A : E →L[ℝ] F}
    (hf : HasFDerivAt f A x) (heq : ∀ y ∈ s, f y = f x) : A = 0 :=
  hasFDerivWithinAt_eq_zero_of_density_one μ hx hf.hasFDerivWithinAt heq

/-- A differentiable map constant on a set has zero actual Frechet derivative at
any point of that set where its local Haar density is one. -/
theorem fderiv_eq_zero_of_eqOn_const_of_density_one {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s) {f : E → F} {c : F}
    (hf : DifferentiableAt ℝ f x) (heq : EqOn f (fun _ ↦ c) s) :
    fderiv ℝ f x = 0 := by
  apply hasFDerivAt_eq_zero_of_density_one μ hx hf.hasFDerivAt
  intro y hy
  exact (heq hy).trans (heq hxs).symm

/-- Agreement on a density-one set determines actual ambient differentials at a
point in that set, not merely almost everywhere on it. -/
theorem fderiv_eq_of_eqOn_of_density_one {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s) {f g : E → F}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (heq : EqOn f g s) :
    fderiv ℝ f x = fderiv ℝ g x := by
  apply hasFDerivWithinAt_unique_of_density_one μ hx hf.hasFDerivAt.hasFDerivWithinAt
  exact hg.hasFDerivAt.hasFDerivWithinAt.congr' heq hxs

end OTSelector.Geometry
