import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.Assignment
import OTSelector.Finite.FractionalOptimal
import OTSelector.Finite.FractionalUnique
import OTSelector.Finite.PerturbedValue

/-!
# Finite.PerturbedValueUnique

**Conditions:** A fixed finite real cost matrix has a unique optimizing permutation; probe and sample size are fixed.

**Objects:** A local affine value germ and its derivative, shared by every original fractional optimum.

**Proof detail:** Each competing permutation has a strictly positive cost gap; finitely many continuous tilted gaps stay positive on one common neighborhood, so the same optimizer gives an exact affine formula there.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95), Section 3.2.3, pp. 80–81 (p. 81 also states the concave infimum version); [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=155), Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Local affine behavior of the finite value at a unique optimum

A unique optimal permutation remains the unique optimum for all sufficiently small real tilts.
The actual finite perturbed minimum is therefore locally affine, with derivative equal to the
probe readout of the unique optimum. Birkhoff uniqueness gives the same derivative for every
fractional optimum. The neighborhood may depend on the two matrices and the sample size; no
uniform neighborhood or differentiability of a limiting pressure is asserted.
-/

open Filter
open scoped Topology

namespace OTSelector

variable {n : ℕ}

/-- Every finite strict cost gap persists in one common neighborhood of zero. -/
theorem eventually_optimalAssignment_iff_eq_of_unique
    (cost probe : Matrix (Fin n) (Fin n) ℝ) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ)
    (hunique : ∀ τ, OptimalAssignment cost τ → τ = σ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ τ,
      OptimalAssignment (perturbedEdgeCost cost probe t) τ ↔ τ = σ := by
  have hstrict (τ : Assignment n) (hτ : τ ≠ σ) :
      assignmentCost cost σ < assignmentCost cost τ := by
    refine lt_of_le_of_ne (hσ τ) ?_
    intro heq
    apply hτ (hunique τ ?_)
    intro ρ
    exact heq ▸ hσ ρ
  have hcont (τ : Assignment n) :
      ContinuousAt (fun t ↦ assignmentCost (perturbedEdgeCost cost probe t) τ) 0 := by
    simp_rw [assignmentCost_perturbedEdgeCost]
    fun_prop
  have hgap : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ τ, τ ≠ σ →
      assignmentCost (perturbedEdgeCost cost probe t) σ <
        assignmentCost (perturbedEdgeCost cost probe t) τ := by
    rw [eventually_all]
    intro τ
    by_cases hτ : τ = σ
    · simp [hτ]
    · exact ((hcont σ).eventually_lt (hcont τ)
        (by simpa using hstrict τ hτ)).mono fun _ ht _ ↦ ht
  filter_upwards [hgap] with t ht
  have hσt : OptimalAssignment (perturbedEdgeCost cost probe t) σ := by
    intro ρ
    by_cases hρ : ρ = σ
    · subst ρ
      exact le_rfl
    · exact (ht ρ hρ).le
  intro τ
  constructor
  · intro hτ
    by_contra hne
    exact (not_lt_of_ge (hτ σ)) (ht τ hne)
  · rintro rfl
    exact hσt

/-- The actual finite minimum agrees with its exact affine expansion near zero. -/
theorem perturbedAssignmentValue_eventuallyEq_affine_of_unique
    (cost probe : Matrix (Fin n) (Fin n) ℝ) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ)
    (hunique : ∀ τ, OptimalAssignment cost τ → τ = σ) :
    perturbedAssignmentValue cost probe =ᶠ[𝓝 (0 : ℝ)]
      fun t ↦ perturbedAssignmentValue cost probe 0 + t * assignmentCost probe σ := by
  have hzero : perturbedAssignmentValue cost probe 0 = assignmentCost cost σ := by
    simpa only [perturbedEdgeCost_zero] using
      perturbedAssignmentValue_eq_of_optimal cost probe 0 σ (by simpa using hσ)
  filter_upwards [eventually_optimalAssignment_iff_eq_of_unique cost probe σ hσ hunique]
    with t ht
  rw [perturbedAssignmentValue_eq_of_optimal cost probe t σ ((ht σ).mpr rfl),
    assignmentCost_perturbedEdgeCost, hzero]

/-- The finite perturbed value has derivative equal to the unique permutation's probe total. -/
theorem hasDerivAt_perturbedAssignmentValue_of_unique
    (cost probe : Matrix (Fin n) (Fin n) ℝ) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ)
    (hunique : ∀ τ, OptimalAssignment cost τ → τ = σ) :
    HasDerivAt (perturbedAssignmentValue cost probe) (assignmentCost probe σ) 0 := by
  have haff : HasDerivAt
      (fun t ↦ perturbedAssignmentValue cost probe 0 + t * assignmentCost probe σ)
      (assignmentCost probe σ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (assignmentCost probe σ)).const_add
      (perturbedAssignmentValue cost probe 0)
  exact haff.congr_of_eventuallyEq
    (perturbedAssignmentValue_eventuallyEq_affine_of_unique cost probe σ hσ hunique)

/-- Dividing the value by the sample size gives the corresponding empirical probe average. -/
theorem hasDerivAt_perturbedAssignmentValue_div_of_unique
    (cost probe : Matrix (Fin n) (Fin n) ℝ) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ)
    (hunique : ∀ τ, OptimalAssignment cost τ → τ = σ) :
    HasDerivAt (fun t ↦ perturbedAssignmentValue cost probe t / (n : ℝ))
      (assignmentCost probe σ / (n : ℝ)) 0 :=
  (hasDerivAt_perturbedAssignmentValue_of_unique cost probe σ hσ hunique).div_const _

/-- Every fractional optimum gives the same derivative of the actual normalized finite value. -/
theorem hasDerivAt_perturbedAssignmentValue_div_of_optimalFractional_of_unique
    (cost probe P : Matrix (Fin n) (Fin n) ℝ)
    (hunique : ∃! σ, OptimalAssignment cost σ) (hP : OptimalFractionalAssignment cost P) :
    HasDerivAt (fun t ↦ perturbedAssignmentValue cost probe t / (n : ℝ))
      (fractionalAssignmentCost probe P / (n : ℝ)) 0 := by
  obtain ⟨σ, hσ, huniq⟩ := hunique
  rw [optimalFractionalAssignment_eq_permMatrix_of_unique cost P σ huniq hP,
    fractionalAssignmentCost_permMatrix]
  exact hasDerivAt_perturbedAssignmentValue_div_of_unique cost probe σ hσ huniq

end OTSelector
