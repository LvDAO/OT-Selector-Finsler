import LeanLevy.RandomMeasure.PoissonRandomMeasure
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
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.Analysis.RelativeBandRatio
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DoublePoleRelativeMobility.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DoublePoleRelativeMobility`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.DoublePoleRelativeMobility

**Conditions:** An actual double-pole residue plus remainder at s and a>0, a right inverse at a, and explicit relative-time/remainder/inverse bounds.

**Objects:** An exact formula for W(s)W(a)⁻¹−I and a relative mobility estimate independent of an endpoint condition number.

**Proof detail:** Eliminate the common residue using the reference inverse identity; separate the scalar pole ratio and remainder difference, then apply matrix norm submultiplicativity and the relative-band scalar estimate.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662), Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T); [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=46), Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47; [OTSelector project, Actual focal simple-pole expansion](main.tex#lem:focal-simple-pole), main.tex label lem:focal-simple-pole, line 9401.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Relative-band mobility for the same actual double-pole field

Multiplying by the inverse at the reference time cancels the actual residue's anisotropy.
The resulting exact identity controls the relative physical mobility by the relative scalar
pole change, the bounded original inverse coefficient, and the smooth actual remainder.
No condition-number bound on the degenerating endpoint matrix enters the estimate.
-/

open Set Matrix
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact cancellation of the actual fixed residue against the same reference inverse. -/
theorem doublePole_relative_mobility_identity
    {G W W₀ R R₀ A : Matrix ι ι ℝ} {s a : ℝ} (ha : a≠0)
    (hW : W=(s^2)⁻¹•G+R) (hW₀ : W₀=(a^2)⁻¹•G+R₀) (hWA : W₀*A=1) :
    W*A-1=(a^2/s^2-1)•(1-R₀*A)+(R-R₀)*A := by
  have hscaled : (a^2)⁻¹•(G*A)+R₀*A=1 := by
    simpa only [hW₀,Matrix.add_mul,Matrix.smul_mul] using hWA
  have hp := congrArg (fun B : Matrix ι ι ℝ ↦ a^2•B) hscaled
  simp only [smul_add,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 ha),one_smul] at hp
  have hGA : G*A=a^2•(1-R₀*A) := by
    calc
      _ = (G*A+a^2•(R₀*A))-a^2•(R₀*A) := by abel
      _ = a^2•1-a^2•(R₀*A) := by rw [hp]
      _ = _ := by module
  rw [hW,Matrix.add_mul,Matrix.smul_mul,hGA,Matrix.sub_mul]
  simp only [div_eq_mul_inv]
  module

/-- The physical relative mobility varies by O(ε) on a relative time band, with constants
from the same actual smooth remainder and bounded actual reference inverse. -/
theorem norm_doublePole_relative_mobility_le
    {G W W₀ R R₀ A : Matrix ι ι ℝ} {s a ε M N H δ : ℝ}
    (ha : 0<a) (haδ : a≤δ) (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hband : |s-a|≤ε*a) (hN : 0≤N) (hH : 0≤H)
    (hR₀ : ‖R₀‖≤M) (hA : ‖A‖≤H) (hRdiff : ‖R-R₀‖≤N*|s-a|)
    (hW : W=(s^2)⁻¹•G+R) (hW₀ : W₀=(a^2)⁻¹•G+R₀) (hWA : W₀*A=1) :
    ‖W*A-1‖≤(10*(‖(1:Matrix ι ι ℝ)‖+M*H)+N*δ*H)*ε := by
  have hM : 0≤M := (norm_nonneg R₀).trans hR₀
  have hcoefficient := (doublePole_ratio_relativeBand ha hε hεhalf hband).2.2
  have hRA : ‖R₀*A‖≤M*H := norm_mul_le_of_le hR₀ hA
  have hI : ‖1-R₀*A‖≤‖(1:Matrix ι ι ℝ)‖+M*H :=
    (norm_sub_le _ _).trans (add_le_add le_rfl hRA)
  have hdiff : ‖(R-R₀)*A‖≤(N*(ε*a))*H := by
    apply norm_mul_le_of_le _ hA
    exact hRdiff.trans (mul_le_mul_of_nonneg_left hband hN)
  rw [doublePole_relative_mobility_identity ha.ne' hW hW₀ hWA]
  calc
    _ ≤ ‖(a^2/s^2-1)•(1-R₀*A)‖+‖(R-R₀)*A‖ := norm_add_le _ _
    _ ≤ |a^2/s^2-1| *(‖(1:Matrix ι ι ℝ)‖+M*H)+(N*(ε*a))*H := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left hI (abs_nonneg _)) hdiff
    _ ≤ (10*ε)*(‖(1:Matrix ι ι ℝ)‖+M*H)+(N*(ε*a))*H := by gcongr
    _ ≤ (10*ε)*(‖(1:Matrix ι ι ℝ)‖+M*H)+(N*(ε*δ))*H := by gcongr
    _ = _ := by ring

end OTSelector.Reconstruction

end
end
