import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.Vlasov.OT.Coupling
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FocalResidueQuadraticEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FocalResidueQuadraticEnergy`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FocalResidueQuadraticEnergy

**Conditions:** A positive-definite original compliance A dominates a positive multiple of r⁻¹G in Loewner order, with c,r>0.

**Objects:** The actual inverse momentum and its focal-residue energy relative to the true kinetic quadratic.

**Proof detail:** Use A(A⁻¹v)=v and symmetry to identify inverse-momentum energies; evaluate the semidefinite lower bound on A⁻¹v and rearrange, retaining the one-half kinetic factor.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108), Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94; [OTSelector project, Actual focal simple-pole expansion](main.tex#lem:focal-simple-pole), main.tex label lem:focal-simple-pole, line 9401.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Quadratic identities for the same actual focal residue and original inverse
momentum. These bounds retain the true kinetic coefficient and its Taylor factor. -/
open Set Function Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluating the original compliance at its own inverse momentum gives the
same original inverse-compliance kinetic quadratic, with the same factor `1/2`. -/
theorem matrixQuadratic_inverseMomentum_eq {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (v : ι → ℝ) : matrixQuadratic A (A⁻¹ *ᵥ v) = matrixQuadratic A⁻¹ v := by
  have hunit := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  simp only [matrixQuadratic, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec]
  rw [dotProduct_comm]

omit [DecidableEq ι] in
/-- A fixed physical residue has a finite explicit quadratic bound in the same
coordinate norm. No lower bound on the residue rank is required. -/
theorem residue_dotProduct_le_absEntrySum_mul_norm_sq (G : Matrix ι ι ℝ) (p : ι → ℝ) :
    p ⬝ᵥ (G *ᵥ p) ≤ (∑ i, ∑ j, |G i j|) * ‖p‖ ^ 2 := by
  have hterm (i j : ι) : p i * (G i j * p j) ≤ |G i j| * ‖p‖ ^ 2 := by
    calc
      _ ≤ |p i * (G i j * p j)| := le_abs_self _
      _ = |G i j| * |p i| * |p j| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |G i j| * ‖p‖ * ‖p‖ := by
        gcongr
        · exact (Real.norm_eq_abs (p i)).symm.trans_le (norm_le_pi_norm p i)
        · exact (Real.norm_eq_abs (p j)).symm.trans_le (norm_le_pi_norm p j)
      _ = _ := by ring
  change (∑ i, p i * (∑ j, G i j * p j)) ≤ (∑ i, ∑ j, |G i j|) * ‖p‖ ^ 2
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, |G i j| * ‖p‖ ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
    _ = _ := by simp_rw [← Finset.sum_mul]

/-- A genuine Loewner compliance lower bound controls the same residue energy
of its actual inverse momentum. -/
theorem residue_energy_le_of_compliance_lower
    {A G : Matrix ι ι ℝ} {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hA : A.PosDef) (hlower : (A - ((c / 2) * r⁻¹) • G).PosSemidef)
    (v : ι → ℝ) :
    ((A⁻¹ *ᵥ v) ⬝ᵥ (G *ᵥ (A⁻¹ *ᵥ v))) / r ≤ (4 / c) * matrixQuadratic A⁻¹ v := by
  let p := A⁻¹ *ᵥ v
  have hq := hlower.dotProduct_mulVec_nonneg p
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hq
  have he : p ⬝ᵥ (A *ᵥ p) = 2 * matrixQuadratic A⁻¹ v := by
    have h := matrixQuadratic_inverseMomentum_eq hA v
    dsimp only [matrixQuadratic] at h
    change (1 / 2 : ℝ) * (p ⬝ᵥ (A *ᵥ p)) = (1 / 2 : ℝ) * (v ⬝ᵥ (A⁻¹ *ᵥ v)) at h
    dsimp only [matrixQuadratic]
    linarith
  rw [he] at hq
  have hd : 0 < (c / 2) * r⁻¹ := by positivity
  have hquot : p ⬝ᵥ (G *ᵥ p) ≤ (2 * matrixQuadratic A⁻¹ v) / ((c / 2) * r⁻¹) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [hq]
  calc
    _ ≤ ((2 * matrixQuadratic A⁻¹ v) / ((c / 2) * r⁻¹)) / r :=
      div_le_div_of_nonneg_right hquot hr.le
    _ = _ := by field_simp; ring

end OTSelector.Reconstruction

end
end
