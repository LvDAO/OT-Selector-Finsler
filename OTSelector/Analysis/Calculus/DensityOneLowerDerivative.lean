import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.DensityOneLowerDerivative.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.DensityOneLowerDerivative`; the selected original proof blocks follow. -/
section

/-!
Conditions: A set has Haar density one at a point; the map has the stated actual within derivative and centered lower norm bound there.

Objects: The same lower bound in every direction and injectivity when the bound is positive.

Proof detail: Approximate each short directional displacement by points in the density-one set and pass the derivative expansion to the limit.

Sources: D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37).
Relation: Locally proved density-one derivative transfer. The target need not be finite-dimensional.
-/

/-!
# Lower derivative bounds at density-one points

A local lower norm bound on a Haar density-one set passes to the actual derivative
within that set, with the same constant in every direction. Small translated and
rescaled balls supply nearby points in every direction directly from Haar density.
A positive constant consequently makes the derivative injective. The set need not be
measurable, and the target space need not be finite dimensional.
-/

open Set Filter Metric Bornology MeasureTheory MeasureTheory.Measure
open scoped Topology Pointwise ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- A local lower norm bound on a density-one set passes to every direction of its
actual within-set derivative, with the same nonnegative constant. -/
theorem norm_apply_ge_of_density_one {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {f : E → Y} {L : E →L[ℝ] Y}
    (hf : HasFDerivWithinAt f L s x) {c : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ᶠ y in 𝓝[s] x, c * ‖y - x‖ ≤ ‖f y - f x‖) :
    ∀ v : E, c * ‖v‖ ≤ ‖L v‖ := by
  intro v
  suffices hε : ∀ ε, 0 < ε →
      c * ‖v‖ ≤ ‖L v‖ + ε * (‖v‖ + ε) + (‖L‖ + c) * ε by
    have hlim : Tendsto (fun ε : ℝ ↦
        ‖L v‖ + ε * (‖v‖ + ε) + (‖L‖ + c) * ε)
        (𝓝[>] 0) (𝓝 ‖L v‖) := by
      simpa using (show Continuous (fun ε : ℝ ↦
        ‖L v‖ + ε * (‖v‖ + ε) + (‖L‖ + c) * ε) by fun_prop).tendsto'
          (0 : ℝ) ‖L v‖ (by simp) |>.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin] using hε
  intro ε hε
  have hhit : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall v ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ v hε).ne'
  obtain ⟨ρ, hρ, hlocal⟩ : ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E |
      ‖f y - f x - L (y - x)‖ ≤ ε * ‖y - x‖ ∧ c * ‖y - x‖ ≤ ‖f y - f x‖} :=
    mem_nhdsWithin_iff.1 ((hf.isLittleO.def hε).and hlower)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall v ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x hρ)
  obtain ⟨r, ⟨y, ⟨hys, hyball⟩⟩, hrball, hr⟩ :
      ∃ r : ℝ, (s ∩ ({x} + r • closedBall v ε)).Nonempty ∧
        {x} + r • closedBall v ε ⊆ ball x ρ ∧ 0 < r :=
    (hhit.and (hsmall.and self_mem_nhdsWithin)).exists
  obtain ⟨a, ha, hya⟩ : ∃ a, a ∈ closedBall v ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hyball
    rcases hyball with ⟨a, ha, he⟩
    exact ⟨a, ha, by simp only [he, add_neg_cancel_left]⟩
  obtain ⟨herror, hlowerY⟩ := hlocal ⟨hrball hyball, hys⟩
  have htriangle : ‖f y - f x‖ ≤ ‖L (y - x)‖ + ε * ‖y - x‖ := by
    calc
      ‖f y - f x‖ = ‖L (y - x) + (f y - f x - L (y - x))‖ := by
        congr 1
        abel
      _ ≤ ‖L (y - x)‖ + ‖f y - f x - L (y - x)‖ := norm_add_le _ _
      _ ≤ ‖L (y - x)‖ + ε * ‖y - x‖ := add_le_add_right herror _
  have hscale := hlowerY.trans htriangle
  rw [hya] at hscale
  simp only [add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr.le] at hscale
  have haLower : c * ‖a‖ ≤ ‖L a‖ + ε * ‖a‖ := by
    apply (mul_le_mul_iff_right₀ hr).mp
    convert hscale using 1 <;> ring
  have hnorma : ‖a‖ ≤ ‖v‖ + ε := by
    calc
      ‖a‖ ≤ ‖v‖ + ‖a - v‖ := norm_le_insert' _ _
      _ ≤ ‖v‖ + ε := add_le_add_right (mem_closedBall_iff_norm.1 ha) _
  have hnormv : ‖v‖ ≤ ‖a‖ + ε := by
    calc
      ‖v‖ ≤ ‖a‖ + ‖v - a‖ := norm_le_insert' _ _
      _ ≤ ‖a‖ + ε := add_le_add_right (mem_closedBall_iff_norm'.1 ha) _
  have hLa : ‖L a‖ ≤ ‖L v‖ + ‖L‖ * ε := by
    calc
      ‖L a‖ ≤ ‖L v‖ + ‖L (a - v)‖ := by
        simpa only [map_sub] using norm_le_insert' (L a) (L v)
      _ ≤ ‖L v‖ + ‖L‖ * ‖a - v‖ := add_le_add_right (L.le_opNorm _) _
      _ ≤ ‖L v‖ + ‖L‖ * ε := by gcongr; exact mem_closedBall_iff_norm.1 ha
  have h₁ := mul_le_mul_of_nonneg_left hnormv hc
  have h₂ := mul_le_mul_of_nonneg_left hnorma hε.le
  nlinarith

/-- A positive local lower norm bound on a density-one set forces the actual
within-set derivative to be injective, without a supplied rank assumption. -/
theorem injective_of_density_one_lower_bound {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {f : E → Y} {L : E →L[ℝ] Y}
    (hf : HasFDerivWithinAt f L s x) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ y in 𝓝[s] x, c * ‖y - x‖ ≤ ‖f y - f x‖) :
    Function.Injective L := by
  intro v w hvw
  have h := norm_apply_ge_of_density_one μ hx hf hc.le hlower (v - w)
  rw [map_sub, hvw, sub_self, norm_zero] at h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (v - w)]

end OTSelector.Geometry

end
end
