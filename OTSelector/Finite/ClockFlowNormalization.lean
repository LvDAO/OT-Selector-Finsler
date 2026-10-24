import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawClockFlowNormalization.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawClockFlowNormalization`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawClockFlowNormalization

**Conditions:** Positive original intensity d, with the explicit lower/relative intensity bounds required by each estimate.

**Objects:** Conditional class flows P/d on the unchanged label marginal and normalized residual mass.

**Proof detail:** Distribute division through finite row/column sums, preserve nonnegativity and legal zeros, and bound d−(1−η)d₀ using the assumed relative intensity comparison.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Convert full original intensity-weighted class flows to conditional flows on the unchanged original label marginal, retaining exact residual mass bounds.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Convert full Haar-weighted class flow to conditional flow on the unchanged
original label marginal. It is used only where the original intensity is positive. -/
def normalizedClockClassFlow {I J Z : Type*} (d : Z → ℝ) (P : Z → I → J → ℝ)
    (z : Z) (i : I) (j : J) : ℝ := P z i j / d z

theorem measurable_normalizedClockClassFlow
    {I J Z : Type*} [MeasurableSpace Z] (d : Z → ℝ) (hd : Measurable d)
    (P : Z → I → J → ℝ) (hP : ∀ i j, Measurable (fun z ↦ P z i j)) (i : I) (j : J) :
    Measurable (fun z ↦ normalizedClockClassFlow d P z i j) :=
  measurable_div.comp ((hP i j).prodMk hd)

/-- Positive original intensity gives the exact original conditional marginals
after class-flow division, with the same legal support. -/
theorem normalizedClockClassFlow_marginals
    {I J : Type*} [Fintype I] [Fintype J]
    (d : ℝ) (hd : 0 < d) (P : I → J → ℝ) (a : I → ℝ) (b : J → ℝ)
    (allowed : I → J → Prop)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = d * a i)
    (hcol : ∀ j, ∑ i, P i j = d * b j)
    (hzero : ∀ i j, ¬ allowed i j → P i j = 0) :
    (∀ i j, 0 ≤ P i j / d) ∧
    (∀ i, ∑ j, P i j / d = a i) ∧
    (∀ j, ∑ i, P i j / d = b j) ∧
    ∀ i j, ¬ allowed i j → P i j / d = 0 := by
  refine ⟨fun i j ↦ div_nonneg (hP i j) hd.le, ?_, ?_, ?_⟩
  · intro i
    rw [← Finset.sum_div, hrow i, mul_div_cancel_left₀ _ hd.ne']
  · intro j
    rw [← Finset.sum_div, hcol j, mul_div_cancel_left₀ _ hd.ne']
  · intro i j hij
    rw [hzero i j hij, zero_div]

/-- A positive original density floor converts the actual weighted residual
mass bound to a uniform conditional bound on the original label marginal. -/
theorem normalizedClockClassFlow_mass_le
    {I J : Type*} [Fintype I] [Fintype J]
    (d lower B : ℝ) (hlower : 0 < lower) (hd : lower ≤ d) (hB : 0 ≤ B)
    (Q : I → J → ℝ) (hmass : (∑ i, ∑ j, Q i j) ≤ B) :
    (∑ i, ∑ j, Q i j / d) ≤ B / lower := by
  have hdpos : 0 < d := hlower.trans_le hd
  simp_rw [← Finset.sum_div]
  exact (div_le_div_of_nonneg_right hmass hdpos.le).trans
    (div_le_div_of_nonneg_left hB hlower hd)

/-- Exact residual flow mass has a relative bound independent of the local
intensity floor. Only original positive intensity and its relative oscillation
enter; the same estimate applies to every retained reference cell. -/
theorem normalized_referenceResidual_mass_le
    {I J : Type*} [Fintype I] [Fintype J]
    (d d₀ η ε : ℝ) (hd : 0 < d) (_hd₀ : 0 < d₀)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : 0 ≤ ε)
    (hupper : d ≤ (1 + ε) * d₀)
    (Q : I → J → ℝ) (hmass : (∑ i, ∑ j, Q i j) = d - (1 - η) * d₀) :
    (∑ i, ∑ j, Q i j / d) ≤ η + ε := by
  have hone : 0 < 1 + ε := by linarith
  simp_rw [← Finset.sum_div]
  rw [hmass]
  calc
    _ ≤ (η + ε) / (1 + ε) := by
      apply (div_le_div_iff₀ hd hone).mpr
      have hmul := mul_nonneg (sub_nonneg.mpr hη1) (sub_nonneg.mpr hupper)
      nlinarith
    _ ≤ _ := div_le_self (add_nonneg hη hε) (by linarith)

/-- Exact row sums retain the full original intensity in the residual mass
formula, rather than charging a uniform kinetic bound per changed sample. -/
theorem referenceResidual_flow_total
    {I J : Type*} [Fintype I] [Fintype J]
    (Q : I → J → ℝ) (a a₀ : I → ℝ) (d d₀ η : ℝ)
    (hrow : ∀ i, ∑ j, Q i j = a i - (1 - η) * a₀ i)
    (htotal : ∑ i, a i = d) (htotal₀ : ∑ i, a₀ i = d₀) :
    (∑ i, ∑ j, Q i j) = d - (1 - η) * d₀ := by
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htotal, htotal₀]

end OTSelector.Reconstruction

end
end
