import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import OTSelector.Analysis.Calculus.Variational.CalibratedEnergyIdentities
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.ChartLipschitzCalibration
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Geometry.Finsler.KernelDistanceHessian

* **Conditions:** For the first generic lemma, a complete metric and one actual intrinsic Euler–Lagrange curve on its connected open interval; for the second, the stated affine calibrated constant-velocity tube.
* **Objects:** A same-family C2 complete extension through the actual curve and the intrinsic Euler–Lagrange predicate derived from affine calibration.
* **Proof detail:** Construct the original initial-state family and identify the central curve by uniqueness; derive the affine tube energy equation from actual calibrated identities.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (derived): Exact mixed split: only the two generic extension/affine-calibration lemmas are covered. Both endpoint-distance kernel-Hessian paper adapters are excluded.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerKernelDistanceHessian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerKernelDistanceHessian`; the selected original proof blocks follow. -/
section

/-!
# The original kernel distance Hessian without a supplied geodesic family

Original metric completeness constructs the smooth family from one intrinsic
Euler--Lagrange curve. Initial-value uniqueness identifies its central member with that
curve on its open connected time interval. The actual global endpoint distance therefore
has the inverse-integral length Hessian formula using only the given curve and genuine
local calibration data; a separate flow family or variation is not an input.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Completeness constructs the actual smooth family through any given local intrinsic
Euler--Lagrange curve, identified throughout its connected open time domain. -/
theorem exists_complete_tangentFamily_C2_through_curve (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {c : ℝ → M} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hc : F.IsEulerLagrangeOn c I) {a : ℝ} (ha : a ∈ I)
    (hx : c a ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    let z₀ := ((extChartAt 𝓘(ℝ, E) old ∘ c) a,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ c) a)
    z₀ ∈ chartEnergyDomain old ∧ ∃ Γ : (E × E) → ℝ → M,
      (∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ) ∧
      (∀ z ∈ chartEnergyDomain old,
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (chartEnergyDomain old ×ˢ univ) ∧ EqOn (Γ z₀) c I := by
  dsimp only
  obtain ⟨htan, hz⟩ := hF.chartTangent_of_isEulerLagrangeAt (hc a ha) old hx
  obtain ⟨Γ, hEL, hinit, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old a
  refine ⟨hz, Γ, hEL, hinit, hG, ?_⟩
  apply hF.eqOn_of_isEulerLagrangeOn hI hconn
    (fun t _ ↦ hEL _ hz t (mem_univ _)) hc ha
  rw [hinit _ hz, ← htan, (extChartAt _ _).left_inv]
  simpa only [FiberBundle.chartedSpace_chartAt, mfld_simps] using hx



/-- An actual fixed-velocity unit calibration tube already satisfies the original
Euler--Lagrange equation: its actual energy momentum is constant and its base derivative
vanishes. No geodesic equation or independently chosen energy is assumed. -/
theorem isEulerLagrangeOn_of_affine_calibration_curve (hF : F.IsSmoothStronglyConvex)
    (old : M) {c : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hc : ContDiffOn ℝ 2 (extChartAt 𝓘(ℝ, E) old ∘ c) I)
    (hx : ∀ t ∈ I, c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ I, (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ U)
    (hvelocity : ∀ t ∈ I, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t = v₀) :
    F.IsEulerLagrangeOn c I := by
  have hbound (x : E) (hx : x ∈ U) (v : E) :
      p v ≤ (F.chartLength old (x, v) : ℝ) :=
    hF.chart_covector_le_chartLength old hu hU hsub p heq hx v
  have hv : v₀ ≠ 0 := by
    intro hz
    rw [hz, _root_.map_zero] at hp
    exact zero_ne_one hp
  intro t ht
  refine ⟨old, I, hI, ht, hx, hc, ?_, ?_⟩
  · intro s hs
    rw [hvelocity s hs]
    exact ⟨hsub (hspace s hs), hv⟩
  · intro s hs
    have hid := hF.chartEnergy_calibrated_identities old hU hsub p hp hunit hbound
      (hspace s hs)
    have hb : baseEnergyDifferential (F.chartEnergy old)
        ((extChartAt 𝓘(ℝ, E) old ∘ c) s,
          deriv (extChartAt 𝓘(ℝ, E) old ∘ c) s) = 0 := by
      rw [hvelocity s hs]
      exact hid.2.2.2.1
    rw [hb]
    apply (hasDerivAt_const s p).congr_of_eventuallyEq
    filter_upwards [hI.mem_nhds hs] with r hr
    rw [hvelocity r hr]
    exact (hF.chartEnergy_calibrated_identities old hU hsub p hp hunit hbound
      (hspace r hr)).2.2.1



end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
