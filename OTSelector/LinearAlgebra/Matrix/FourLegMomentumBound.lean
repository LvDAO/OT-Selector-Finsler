import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.LinearAlgebra.Matrix.FourLegQuadraticVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LegalCycleMomentumBound.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LegalCycleMomentumBound`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.LegalCycleMomentumBound

**Conditions:** Four positive original compliance legs satisfy the displayed two-cycle comparison and explicit inverse-quadratic upper bound C.

**Objects:** Componentwise and norm squared differences of the actual common-cut momenta.

**Proof detail:** Insert a variable coordinate meeting-point perturbation into the four-leg inequality; nonnegativity of its quadratic for every scalar forces a discriminant bound, then pass from components to the finite-coordinate norm.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108), Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94; [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Common-cut approximate momentum field and phase-cell envelopes](main.tex#degenerate-central-phase-envelope), main.tex label degenerate-central-phase-envelope, line 9561.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# The common-cut momentum estimate from legal two-cycle geometry

The exact four-leg competitor bounds the difference of the actual momenta by actual path
position separation plus the original cycle defect.  Bounds on the local inverse legs are
intermediate scale estimates, not new assumptions on the final geometric theorem.
-/

open Set Function Matrix
open scoped Matrix.Norms.Operator Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The legal midpoint comparison controls each actual momentum difference component by
the actual common-cut path-position separation and the original additive cycle defect. -/
theorem legalTwoCycle_momentum_component_sq_le
    {A₁ B₁ A₂ B₂ : Matrix ι ι ℝ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef) (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (p₁ p₂ δ : ι → ℝ) (D₀ C : ℝ)
    (hcycle : matrixQuadratic (A₁ + B₁) p₁ + matrixQuadratic (A₂ + B₂) p₂ ≤
      matrixQuadratic (A₁ + B₂)⁻¹ (δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂) +
        matrixQuadratic (A₂ + B₁)⁻¹ (-δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁) + D₀)
    (hbound : ∀ v : ι → ℝ,
      matrixQuadratic A₁⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic A₂⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic B₁⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic B₂⁻¹ v ≤ C * ∑ j, v j ^ 2)
    (i : ι) : (p₁ i - p₂ i) ^ 2 ≤ 4 * C * (D₀ + C * ∑ j, δ j ^ 2) := by
  have hpoly (r : ℝ) :
      0 ≤ (4 * C) * (r * r) + (2 * (p₁ i - p₂ i)) * r +
        (D₀ + C * ∑ j, δ j ^ 2) := by
    let h : ι → ℝ := (1 / 2 : ℝ) • δ + r • Pi.single i 1
    have hlinear : 2 * ((p₁ - p₂) ⬝ᵥ h) - (p₁ - p₂) ⬝ᵥ δ =
        2 * (p₁ i - p₂ i) * r := by
      simp only [h, dotProduct_add, dotProduct_smul, dotProduct_single, Pi.sub_apply]
      ring
    have hcoord (j : ι) : h j ^ 2 + (h j - δ j) ^ 2 =
        δ j ^ 2 / 2 + if j = i then 2 * r ^ 2 else 0 := by
      by_cases hji : j = i
      · subst j
        simp only [h, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
          ite_true]
        ring
      · simp only [h, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hji, smul_eq_mul,
          mul_zero, add_zero, hji, ite_false]
        ring
    have hsum : (∑ j, h j ^ 2) + ∑ j, (h j - δ j) ^ 2 =
        (1 / 2 : ℝ) * ∑ j, δ j ^ 2 + 2 * r ^ 2 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [hcoord]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← Finset.sum_div]
      ring
    have hvar := legalTwoCycle_fourLeg_variation hA₁ hB₁ hA₂ hB₂ p₁ p₂ δ D₀ hcycle h
    have hquad := add_le_add
      (add_le_add (hbound h).1 (hbound h).2.1)
      (add_le_add (hbound (h - δ)).2.2.1 (hbound (h - δ)).2.2.2)
    have hquad' : matrixQuadratic A₁⁻¹ h + matrixQuadratic A₂⁻¹ h +
        matrixQuadratic B₁⁻¹ (h - δ) + matrixQuadratic B₂⁻¹ (h - δ) ≤
        C * (∑ j, δ j ^ 2) + 4 * C * r ^ 2 := by
      have heq : C * (∑ j, h j ^ 2) + C * (∑ j, h j ^ 2) +
          (C * (∑ j, (h j - δ j) ^ 2) + C * (∑ j, (h j - δ j) ^ 2)) =
          C * (∑ j, δ j ^ 2) + 4 * C * r ^ 2 := by
        calc
          _ = 2 * C * ((∑ j, h j ^ 2) + ∑ j, (h j - δ j) ^ 2) := by ring
          _ = _ := by rw [hsum]; ring
      simp only [Pi.sub_apply] at hquad
      rw [heq] at hquad
      linarith
    nlinarith only [hvar, hquad', hlinear]
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  nlinarith

/-- The same common-cut estimate controls the actual fixed-coordinate momentum norm, with
an explicit dimension factor and the unchanged cycle defect. -/
theorem legalTwoCycle_momentum_norm_sq_le
    {A₁ B₁ A₂ B₂ : Matrix ι ι ℝ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef) (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (p₁ p₂ δ : ι → ℝ) {D₀ C : ℝ} (hD₀ : 0 ≤ D₀) (hC : 0 ≤ C)
    (hcycle : matrixQuadratic (A₁ + B₁) p₁ + matrixQuadratic (A₂ + B₂) p₂ ≤
      matrixQuadratic (A₁ + B₂)⁻¹ (δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂) +
        matrixQuadratic (A₂ + B₁)⁻¹ (-δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁) + D₀)
    (hbound : ∀ v : ι → ℝ,
      matrixQuadratic A₁⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic A₂⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic B₁⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic B₂⁻¹ v ≤ C * ∑ j, v j ^ 2) :
    ‖p₁ - p₂‖ ^ 2 ≤ 4 * C * (D₀ + C * (Fintype.card ι : ℝ) * ‖δ‖ ^ 2) := by
  have hδ : (∑ j, δ j ^ 2) ≤ (Fintype.card ι : ℝ) * ‖δ‖ ^ 2 := by
    calc
      _ ≤ ∑ _j : ι, ‖δ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hj := norm_le_pi_norm δ j
        rw [Real.norm_eq_abs] at hj
        nlinarith [sq_abs (δ j), abs_nonneg (δ j)]
      _ = _ := by simp
  let R := 4 * C * (D₀ + C * (Fintype.card ι : ℝ) * ‖δ‖ ^ 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hn : ‖p₁ - p₂‖ ≤ Real.sqrt R := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg R)).mpr
    intro i
    have hi := legalTwoCycle_momentum_component_sq_le
      hA₁ hB₁ hA₂ hB₂ p₁ p₂ δ D₀ C hcycle hbound i
    have hprod : 4 * C * (D₀ + C * ∑ j, δ j ^ 2) ≤ R := by
      have hb := mul_le_mul_of_nonneg_left hδ hC
      have hc := mul_le_mul_of_nonneg_left (add_le_add (le_refl D₀) hb)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC)
      simpa only [R, mul_assoc] using hc
    have hsq := hi.trans hprod
    rw [Real.norm_eq_abs, Pi.sub_apply]
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg R)).mp
      (by simpa only [sq_abs, Real.sq_sqrt hR] using hsq)
  nlinarith [Real.sq_sqrt hR, norm_nonneg (p₁ - p₂)]

end OTSelector.Reconstruction

end
end
