import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.NormedSpace.FiberNormCompact
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart

/-!
## Lemma skeleton

* **Conditions:** A compact coordinate-base set and a bounded speed interval; a strictly positive lower speed only when avoiding the zero section.
* **Objects:** Compact chart phase-speed slabs and containment in the slit energy domain.
* **Proof detail:** Transfer continuity/homogeneity to chart length, apply the compact fiber-norm lemma, and use positivity to exclude zero velocity.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006 author manuscript)*, Section 1.1, Remarks 1.3(6)–(9), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 2, pp. 304–305 (Minkowski norms and Finsler metrics), p. 308 (Legendre duality, equation (2–12)).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2

**Relationship to the sources:** This is a uniform compactness corollary for continuous positive homogeneous lengths; it does not use the fiber triangle inequality.
-/

/-!
# Compact speed layers for the actual Finsler energy

Over every compact subset of an actual chart, a closed bounded interval of original
Finsler speeds gives a compact set of coordinate states. If its lower speed is positive,
the entire compact set lies in the slit domain of the true Euler--Lagrange equations.
This supplies state confinement for finite-time continuation without assuming a compact
manifold or replacing its Finsler norm by an inner product.
-/

open Set Bundle Manifold
open scoped ContDiff Topology

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (F : ContinuousFinslerNorm E M)

/-- The original chart length is continuous, including at zero velocity. -/
theorem continuousOn_chartLength (x₀ : M) :
    ContinuousOn (F.chartLength x₀) ((extChartAt 𝓘(ℝ, E) x₀).target ×ˢ univ) := by
  have h := F.continuous_toFun.comp_continuousOn
    (continuousOn_extChartAt_symm (I := 𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M))
  simpa only [tangentChart_target, chartLength, Function.comp_def] using! h

/-- True tangent-chart homogeneity preserves the original fiber length. -/
theorem chartLength_smul (x₀ : M) {u : E}
    (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (r : ℝ) (v : E) :
    F.chartLength x₀ (u, r • v) = ‖r‖₊ * F.chartLength x₀ (u, v) := by
  simp only [F.chartLength_eq_fiber x₀ hu, _root_.map_smul, F.map_smul]

/-- The zero coordinate velocity has zero original speed. -/
@[simp] theorem chartLength_zero (x₀ : M) {u : E}
    (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target) : F.chartLength x₀ (u, 0) = 0 := by
  simpa using F.chartLength_smul x₀ hu 0 0

/-- Bounded closed ranges of actual Finsler speed above a compact coordinate base are compact. -/
theorem isCompact_chartSpeed_range [FiniteDimensional ℝ E] (x₀ : M) {K : Set E}
    (hK : IsCompact K) (hsub : K ⊆ (extChartAt 𝓘(ℝ, E) x₀).target) (a b : ℝ) :
    IsCompact {z : E × E | z.1 ∈ K ∧ (F.chartLength x₀ z : ℝ) ∈ Icc a b} := by
  apply isCompact_fiberNorm_closed_range hK
    (F := fun u v ↦ (F.chartLength x₀ (u, v) : ℝ))
  · exact (NNReal.continuous_coe.comp_continuousOn
      (F.continuousOn_chartLength x₀)).mono (prod_mono hsub Subset.rfl)
  · intro u hu r v
    simp only [F.chartLength_smul x₀ (hsub hu), NNReal.coe_mul, coe_nnnorm,
      Real.norm_eq_abs]
  · intro u hu v hv
    exact NNReal.coe_pos.mpr (F.chartLength_pos x₀ ⟨hsub hu, hv⟩)

/-- A positive lower speed keeps the entire compact range inside the true slit domain. -/
theorem chartSpeed_range_subset_domain (x₀ : M) {K : Set E}
    (hsub : K ⊆ (extChartAt 𝓘(ℝ, E) x₀).target) {a b : ℝ} (ha : 0 < a) :
    {z : E × E | z.1 ∈ K ∧ (F.chartLength x₀ z : ℝ) ∈ Icc a b} ⊆
      chartEnergyDomain x₀ := by
  intro z hz
  refine ⟨hsub hz.1, fun hv ↦ ?_⟩
  have hzero : F.chartLength x₀ z = 0 := by
    rw [show z = (z.1, z.2) from rfl, hv, F.chartLength_zero x₀ (hsub hz.1)]
  have hle := hz.2.1
  rw [hzero, NNReal.coe_zero] at hle
  exact (not_le_of_gt ha) hle

end OTSelector.Geometry.ContinuousFinslerNorm
