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
import OTSelector.LinearAlgebra.Matrix.QuadraticMomentumBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PositiveResidueVelocityEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PositiveResidueVelocityEnergy`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.PositiveResidueVelocityEnergy

**Conditions:** A positive-semidefinite physical residue and the explicit positive relative time/source scales and bounded remainder.

**Objects:** Velocity controlled by the square root of its own residue energy, with the actual t^(−3/2) scale.

**Proof detail:** Apply the component PSD Cauchy–Schwarz inequality and a finite maximum diagonal bound to control Gp; split pole and remainder velocities and use the exact square-root/power scaling identity.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [OTSelector project, Full-path focal traffic and residue-energy control](main.tex#thm:focal-full-path-traffic), main.tex label thm:focal-full-path-traffic, line 9624.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! The same positive physical residue controls its velocity by the square root
of its own quadratic energy. No eigenspace or commuting-remainder hypothesis is used. -/
open Set Function Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A fixed positive residue controls its image by its own original quadratic
energy, with a finite constant produced directly from the same matrix. -/
theorem exists_positiveResidue_mulVec_sqrt_energy_bound
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ι → ℝ, ‖G *ᵥ p‖ ≤ C * Real.sqrt (p ⬝ᵥ (G *ᵥ p)) := by
  let J : ℝ := (∑ i, |G i i|) + 1
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨Real.sqrt J, Real.sqrt_pos.mpr hJ, fun p ↦ ?_⟩
  have hq : 0 ≤ p ⬝ᵥ (G *ᵥ p) := by simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg p
  have hdiag (i : ι) : G i i ≤ J := by
    have h := Finset.single_le_sum (fun j _ ↦ abs_nonneg (G j j)) (Finset.mem_univ i)
    dsimp [J]
    linarith [le_abs_self (G i i)]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_mul hJ.le]
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg hJ.le hq)).mpr
  rw [sq_abs]
  exact (mulVec_component_sq_le_diag_quadratic hG p i).trans
    (mul_le_mul_of_nonneg_right (hdiag i) hq)

/-- The physical double-pole power times the source-energy square root has its
precise `t^(-3/2)` scale. -/
theorem inverse_sq_mul_sqrt_two_scale {t : ℝ} (ht : 0 < t) :
    (t ^ 2)⁻¹ * Real.sqrt (2 * t) = Real.sqrt 2 * t ^ (-3 / 2 : ℝ) := by
  have hp : (t ^ 2)⁻¹ = t ^ (-2 : ℝ) := by
    rw [Real.rpow_neg ht.le, Real.rpow_two]
  rw [Real.sqrt_mul (by norm_num), hp]
  have htScale : t ^ (-2 : ℝ) * Real.sqrt t = t ^ (-3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
    norm_num
  calc
    _ = Real.sqrt 2 * (t ^ (-2 : ℝ) * Real.sqrt t) := by ring
    _ = _ := by rw [htScale]

/-- The original pole plus a bounded actual remainder gives the physical
velocity estimate in the same source or target residue energy. -/
theorem pole_velocity_le_source_energy_scale
    {G R : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {L M t r a : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (ht : 0 < t)
    (hr : t ≤ r) (ha : 0 < a) (hat : a ≤ 2 * t)
    (hGnorm : ∀ p : ι → ℝ, ‖G *ᵥ p‖ ≤ L * Real.sqrt (p ⬝ᵥ (G *ᵥ p)))
    (hR : ‖R‖ ≤ M) (p : ι → ℝ) :
    ‖((r ^ 2)⁻¹ • G + R) *ᵥ p‖ ≤ (L * Real.sqrt 2 + M) *
      (t ^ (-3 / 2 : ℝ) * Real.sqrt ((p ⬝ᵥ (G *ᵥ p)) / a) + ‖p‖) := by
  let e : ℝ := (p ⬝ᵥ (G *ᵥ p)) / a
  have hq : 0 ≤ p ⬝ᵥ (G *ᵥ p) := by simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg p
  have he : 0 ≤ e := div_nonneg hq ha.le
  have hqeq : p ⬝ᵥ (G *ᵥ p) = a * e := by dsimp [e]; field_simp
  have hqle : p ⬝ᵥ (G *ᵥ p) ≤ 2 * t * e := by rw [hqeq]; gcongr
  have hsqrt : Real.sqrt (p ⬝ᵥ (G *ᵥ p)) ≤ Real.sqrt (2 * t) * Real.sqrt e := by
    exact (Real.sqrt_le_sqrt hqle).trans_eq (Real.sqrt_mul (by positivity) e)
  have hr0 : 0 < r := ht.trans_le hr
  have hinv : (r ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ ht.le hr 2)
  calc
    _ ≤ (r ^ 2)⁻¹ * ‖G *ᵥ p‖ + ‖R‖ * ‖p‖ := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec]
      exact (norm_add_le _ _).trans (add_le_add
        (by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)])
        (Matrix.linfty_opNorm_mulVec R p))
    _ ≤ (t ^ 2)⁻¹ * (L * (Real.sqrt (2 * t) * Real.sqrt e)) + M * ‖p‖ := by
      gcongr
      exact (hGnorm p).trans (mul_le_mul_of_nonneg_left hsqrt hL)
    _ = (L * Real.sqrt 2) * (t ^ (-3 / 2 : ℝ) * Real.sqrt e) + M * ‖p‖ := by
      have hscale := inverse_sq_mul_sqrt_two_scale ht
      calc
        _ = L * ((t ^ 2)⁻¹ * Real.sqrt (2 * t)) * Real.sqrt e + M * ‖p‖ := by ring
        _ = _ := by rw [hscale]; ring
    _ ≤ _ := by
      change _ ≤ (L * Real.sqrt 2 + M) * (t ^ (-3 / 2 : ℝ) * Real.sqrt e + ‖p‖)
      have hL0 : 0 ≤ L * Real.sqrt 2 := mul_nonneg hL (Real.sqrt_nonneg _)
      have hu0 : 0 ≤ t ^ (-3 / 2 : ℝ) * Real.sqrt e :=
        mul_nonneg (Real.rpow_nonneg ht.le _) (Real.sqrt_nonneg _)
      calc
        _ ≤ (L * Real.sqrt 2 + M) * (t ^ (-3 / 2 : ℝ) * Real.sqrt e) +
            (L * Real.sqrt 2 + M) * ‖p‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) hu0)
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL0) (norm_nonneg _))
        _ = _ := by ring

end OTSelector.Reconstruction

end
end
