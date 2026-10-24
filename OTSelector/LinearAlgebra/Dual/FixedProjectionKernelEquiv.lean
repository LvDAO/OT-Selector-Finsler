import OTSelector.Analysis.NormedSpace.CovectorSplitting
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FixedProjectionKernelEquiv.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FixedProjectionKernelEquiv`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two covectors are nonzero on the same fixed transverse vector.

Objects: An explicit continuous linear equivalence of their kernels and its level-section differential.

Proof detail: Subtract the multiple p(w)/p(v) of the transverse vector, verify the inverse projection and solve the level/projection equations.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55).
Relation: Elementary transverse projection construction; its explicit formula is local, not claimed as a numbered textbook theorem.
-/

/-!
# Changing covector kernels with a fixed projection

Two covectors nonzero on the same fixed vector have canonically equivalent kernels.
The equivalence is the actual derivative of a fixed-projection level section.
-/

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Project onto the second covector kernel along the same fixed vector. -/
def fixedProjectionKernelEquiv (p₀ p : E →L[ℝ] ℝ) (v₀ : E)
    (hp₀ : p₀ v₀ ≠ 0) (hp : p v₀ ≠ 0) : p₀.ker ≃L[ℝ] p.ker := by
  let π₀ := (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
    (covectorSplitting p₀ v₀ hp₀).symm.toContinuousLinearMap
  let π := (ContinuousLinearMap.fst ℝ p.ker ℝ).comp
    (covectorSplitting p v₀ hp).symm.toContinuousLinearMap
  have hπ₀v : π₀ v₀ = 0 := by
    apply Subtype.ext
    simp [π₀, hp₀]
  have hπv : π v₀ = 0 := by
    apply Subtype.ext
    simp [π, hp]
  have hπ₀ (w : p₀.ker) : π₀ (w : E) = w := by
    apply Subtype.ext
    simp [π₀, show p₀ (w : E) = 0 from w.property]
  have hπ (w : p.ker) : π (w : E) = w := by
    apply Subtype.ext
    simp [π, show p (w : E) = 0 from w.property]
  refine ContinuousLinearEquiv.equivOfInverse (π.comp p₀.ker.subtypeL)
    (π₀.comp p.ker.subtypeL) ?_ ?_
  · intro w
    change π₀ ((π (w : E) : p.ker) : E) = w
    rw [show ((π (w : E) : p.ker) : E) =
      (w : E) - (p (w : E) / p v₀) • v₀ by simp [π]]
    simp only [map_sub, map_smul, hπ₀v, smul_zero, sub_zero, hπ₀]
  · intro w
    change π ((π₀ (w : E) : p₀.ker) : E) = w
    rw [show ((π₀ (w : E) : p₀.ker) : E) =
      (w : E) - (p₀ (w : E) / p₀ v₀) • v₀ by simp [π₀]]
    simp only [map_sub, map_smul, hπv, smul_zero, sub_zero, hπ]

/-- The kernel equivalence has the fixed-projection section derivative as its underlying map. -/
@[simp] theorem fixedProjectionKernelEquiv_apply
    (p₀ p : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0) (hp : p v₀ ≠ 0)
    (w : p₀.ker) :
    (fixedProjectionKernelEquiv p₀ p v₀ hp₀ hp w : E) =
      (w : E) - (p (w : E) / p v₀) • v₀ := by
  simp [fixedProjectionKernelEquiv]

/-- The inverse is the original fixed projection restricted to the new kernel. -/
@[simp] theorem fixedProjectionKernelEquiv_symm_apply
    (p₀ p : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0) (hp : p v₀ ≠ 0)
    (w : p.ker) :
    (fixedProjectionKernelEquiv p₀ p v₀ hp₀ hp).symm w =
      ((covectorSplitting p₀ v₀ hp₀).symm (w : E)).1 := rfl

/-- Composition with the kernel inclusion gives the exact level-section first jet. -/
theorem fixedProjectionKernelEquiv_subtype_comp
    (p₀ p : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0) (hp : p v₀ ≠ 0) :
    p.ker.subtypeL.comp (fixedProjectionKernelEquiv p₀ p v₀ hp₀ hp).toContinuousLinearMap =
      p₀.ker.subtypeL -
        (p.comp p₀.ker.subtypeL).smulRight ((p v₀)⁻¹ • v₀) := by
  ext w
  simp [div_eq_mul_inv, smul_smul]

end OTSelector.Geometry

end
end
