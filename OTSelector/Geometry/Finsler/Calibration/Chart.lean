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
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FundamentalInequality
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
## Lemma skeleton

* **Conditions:** A chart, positive smooth strongly convex Finsler energy for the fundamental inequality, and a C1 local potential.
* **Objects:** Chart length, normalized Legendre covector and pulled-back calibrating potential.
* **Proof detail:** Identify chart energy with half the length squared, divide the supporting covector by speed, then transfer its bound/saturation through the chart differential.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006 author manuscript)*, Section 1.1, Definition 1.2, Remarks 1.3 and Propositions 1.4–1.5, pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4
* J. C. Álvarez Paiva; A. C. Thompson, *Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)*, Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
  https://library.slmath.org/books/Book50/files/02AT.pdf#page=22
* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10

**Relationship to the sources:** The chart/NNReal domain lemmas are adapters; the covector bound is the Finsler fundamental inequality and the minimizing principle is exact-form calibration.
-/

/-!
# Actual chart momenta and manifold calibration pullbacks

The fundamental inequality for the original Finsler fiber energy transfers through the
true tangent chart. Chart energy, chart length, and actual momentum obey the resulting
normalization identities, including for every zero or nonzero comparison velocity.

A C1 scalar potential on an open coordinate set pulls back to a C1 function on the
corresponding open manifold set. Its coordinate differential bound and saturation transfer
to the original tangent length by the actual chart differential and inverse tangent-chart
identity. This conversion requires only a C1 manifold; the energy inequalities use the
existing smooth strongly convex Finsler data. Neither part requires finite-dimensionality
or an inner product. The coordinate potential is supplied, not constructed, by this module.
-/

open Bundle Set Manifold Filter
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

namespace ContinuousFinslerNorm

/-- The original Finsler length evaluated through one actual inverse tangent chart. -/
def chartLength [IsManifold 𝓘(ℝ, E) 1 M]
    (F : ContinuousFinslerNorm E M) (x₀ : M) (z : E × E) : ℝ≥0 :=
  F.toFun ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
    (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)

section Smooth
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Chart energy is exactly one half of the squared original chart length. -/
theorem chartEnergy_eq_chartLength_sq (F : ContinuousFinslerNorm E M)
    (x₀ : M) (z : E × E) :
    F.chartEnergy x₀ z = (F.chartLength x₀ z : ℝ) ^ 2 / 2 := rfl

/-- Equal actual chart energies give equal original chart lengths. -/
theorem chartLength_eq_of_chartEnergy_eq (F : ContinuousFinslerNorm E M)
    (x₀ : M) {z z' : E × E} (h : F.chartEnergy x₀ z = F.chartEnergy x₀ z') :
    F.chartLength x₀ z = F.chartLength x₀ z' := F.toFun_eq_of_energy_eq h

/-- In the fixed representation of a tangent fiber, chart length uses the genuine chart change. -/
theorem chartLength_eq_fiber (F : ContinuousFinslerNorm E M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (v : E) :
    F.chartLength x₀ (y, v) = F.toFun ⟨(extChartAt 𝓘(ℝ, E) x₀).symm y,
      tangentFiberModelEquiv _ (chartFiberEquiv x₀ hy v)⟩ := by
  rw [chartLength, tangentChart_symm_eq x₀ hy]
  simp only [chartFiberEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Nonzero velocities in the chart domain have strictly positive original length. -/
theorem chartLength_pos (F : ContinuousFinslerNorm E M) (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) : 0 < F.chartLength x₀ z := by
  rw [show z = (z.1, z.2) from rfl, F.chartLength_eq_fiber x₀ hz.1]
  apply F.pos
  intro heq
  have heq' : chartFiberEquiv x₀ hz.1 z.2 = 0 :=
    (tangentFiberModelEquiv _).injective (heq.trans (_root_.map_zero _).symm)
  exact hz.2 ((chartFiberEquiv x₀ hz.1).injective (heq'.trans (_root_.map_zero _).symm))

/-- The actual chart momentum is the original fiber differential in the true fiber coordinates. -/
theorem chartLegendre_apply_eq_fiber (F : ContinuousFinslerNorm E M) (x₀ : M)
    {z : E × E} (hz : z.1 ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (w : E) :
    fiberLegendre (F.chartEnergy x₀) z w =
      fderiv ℝ (F.fiberEnergyModel ((extChartAt 𝓘(ℝ, E) x₀).symm z.1))
        (chartFiberEquiv x₀ hz z.2) (chartFiberEquiv x₀ hz w) := by
  have heq : (fun v ↦ F.chartEnergy x₀ (z.1, v)) =
      F.fiberEnergyModel ((extChartAt 𝓘(ℝ, E) x₀).symm z.1) ∘ chartFiberEquiv x₀ hz :=
    funext (F.chartEnergy_eq_fiberEnergyModel x₀ hz)
  change fderiv ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v)) z.2 w = _
  rw [heq, (chartFiberEquiv x₀ hz).comp_right_fderiv]
  rfl

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The actual chart momentum obeys the fundamental inequality for every comparison velocity. -/
theorem chart_fundamental_inequality (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (w : E) :
    fiberLegendre (F.chartEnergy x₀) z w ≤
      (F.chartLength x₀ z : ℝ) * (F.chartLength x₀ (z.1, w) : ℝ) := by
  rcases z with ⟨y, v⟩
  rw [F.chartLegendre_apply_eq_fiber x₀ hz.1]
  have hv : chartFiberEquiv x₀ hz.1 v ≠ 0 :=
    fun heq ↦ hz.2 ((chartFiberEquiv x₀ hz.1).injective (heq.trans (_root_.map_zero _).symm))
  simpa only [F.chartLength_eq_fiber x₀ hz.1] using
    hF.fiber_fundamental_inequality ((extChartAt 𝓘(ℝ, E) x₀).symm y)
      hv (chartFiberEquiv x₀ hz.1 w)

/-- Euler's identity pairs chart momentum with its velocity to give the squared original speed. -/
theorem chartLegendre_self_eq_chartLength_sq (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) :
    fiberLegendre (F.chartEnergy x₀) z z.2 = (F.chartLength x₀ z : ℝ) ^ 2 := by
  rw [hF.chartEnergy_euler x₀ hz, F.chartEnergy_eq_chartLength_sq]
  ring

/-- At fixed positive original speed s, normalized momentum is bounded by original length. -/
theorem chartLegendre_div_le_chartLength (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) {s : ℝ} (hs : (F.chartLength x₀ z : ℝ) = s)
    (w : E) :
    fiberLegendre (F.chartEnergy x₀) z w / s ≤ (F.chartLength x₀ (z.1, w) : ℝ) := by
  have hpos : 0 < s := hs ▸ NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
  apply (div_le_iff₀ hpos).2
  simpa only [hs, mul_comm] using hF.chart_fundamental_inequality x₀ hz w

/-- Normalized momentum saturates the original length in the direction of its velocity. -/
theorem chartLegendre_div_self_eq_chartLength (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) {s : ℝ} (hs : (F.chartLength x₀ z : ℝ) = s) :
    fiberLegendre (F.chartEnergy x₀) z z.2 / s = (F.chartLength x₀ z : ℝ) := by
  rw [hF.chartLegendre_self_eq_chartLength_sq x₀ hz, hs]
  have hpos : 0 < s := hs ▸ NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)
  field_simp

end IsSmoothStronglyConvex
end Smooth

/-- The manifold domain of a coordinate potential on V in one fixed chart. -/
def chartCalibrationDomain (x₀ : M) (V : Set E) : Set M :=
  (extChartAt 𝓘(ℝ, E) x₀).source ∩ (extChartAt 𝓘(ℝ, E) x₀) ⁻¹' V

/-- An open coordinate domain pulls back to an open manifold domain. -/
theorem isOpen_chartCalibrationDomain (x₀ : M) {V : Set E} (hV : IsOpen V) :
    IsOpen (chartCalibrationDomain x₀ V) := by
  exact (continuousOn_extChartAt x₀).isOpen_inter_preimage
    (isOpen_extChartAt_source x₀) hV

/-- A coordinate neighborhood of the chart anchor pulls back to a neighborhood containing it. -/
theorem mem_chartCalibrationDomain (x₀ : M) {V : Set E}
    (h : extChartAt 𝓘(ℝ, E) x₀ x₀ ∈ V) : x₀ ∈ chartCalibrationDomain x₀ V :=
  ⟨mem_extChartAt_source x₀, h⟩

/-- Inverse chart images of coordinate points in the domain belong to the pullback domain. -/
theorem chart_symm_mem_chartCalibrationDomain (x₀ : M) {V : Set E} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (hV : y ∈ V) :
    (extChartAt 𝓘(ℝ, E) x₀).symm y ∈ chartCalibrationDomain x₀ V := by
  refine ⟨(extChartAt 𝓘(ℝ, E) x₀).map_target hy, ?_⟩
  change extChartAt 𝓘(ℝ, E) x₀ ((extChartAt 𝓘(ℝ, E) x₀).symm y) ∈ V
  rwa [(extChartAt 𝓘(ℝ, E) x₀).right_inv hy]

section Pullback
variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- A C1 coordinate potential gives an actual C1 scalar function on its chart domain. -/
theorem contMDiffOn_chartPullback (x₀ : M) {u : E → ℝ} {V : Set E}
    (hu : ContDiffOn ℝ 1 u V) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (u ∘ extChartAt 𝓘(ℝ, E) x₀)
      (chartCalibrationDomain x₀ V) := by
  apply hu.contMDiffOn.comp
    (contMDiffOn_extChartAt.mono (fun x hx ↦ ?_)) (fun x hx ↦ hx.2)
  simpa only [extChartAt_source] using hx.1

/-- The differential of the actual chart pullback is the coordinate differential composed
with the actual chart differential. -/
theorem mfderiv_chartPullback_apply (x₀ : M) {u : E → ℝ} {V : Set E}
    (hV : IsOpen V) (hu : ContDiffOn ℝ 1 u V)
    {x : M} (hx : x ∈ chartCalibrationDomain x₀ V)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (u ∘ extChartAt 𝓘(ℝ, E) x₀) x v =
      fderiv ℝ u (extChartAt 𝓘(ℝ, E) x₀ x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v) := by
  have hd := (hu.contDiffAt (hV.mem_nhds hx.2)).differentiableAt one_ne_zero
  have he := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
    (show x ∈ (chartAt E x₀).source by simpa only [extChartAt_source] using hx.1)
  rw [mfderiv_comp x hd.mdifferentiableAt he, mfderiv_eq_fderiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the inverse tangent chart to the actual coordinate representation recovers
the original tangent vector, without an auxiliary metric. -/
theorem tangentChart_symm_mfderiv_extChartAt (x₀ : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) x₀).source)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
        (extChartAt 𝓘(ℝ, E) x₀ x,
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v) = ⟨x, v⟩ := by
  let e := extChartAt 𝓘(ℝ, E) x₀
  have htarget : e x ∈ e.target := e.map_source hx
  have hd := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
    (show x ∈ (chartAt E x₀).source by simpa only [extChartAt_source] using hx)
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm htarget
  have heq : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [(isOpen_extChartAt_source x₀).mem_nhds hx] with y hy
    exact e.left_inv hy
  rw [tangentChart_symm_eq_tangentMap x₀ htarget]
  change tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm
    (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) e ⟨x, v⟩) = ⟨x, v⟩
  rw [← tangentMap_comp_at ⟨x, v⟩ hi hd]
  apply TotalSpace.ext heq.self_of_nhds
  simp only [tangentMap, heq.mfderiv_eq, mfderiv_id]
  rfl

/-- Chart length of the actual coordinate velocity is exactly the original tangent length. -/
theorem chartLength_mfderiv_extChartAt (F : ContinuousFinslerNorm E M) (x₀ : M)
    {x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, E) x₀).source)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    F.chartLength x₀ (extChartAt 𝓘(ℝ, E) x₀ x,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v) = F.toFun ⟨x, v⟩ := by
  rw [chartLength, tangentChart_symm_mfderiv_extChartAt x₀ hx]

/-- A coordinate calibration bound becomes the actual manifold calibration bound. -/
theorem mfderiv_chartPullback_le (F : ContinuousFinslerNorm E M) (x₀ : M)
    {u : E → ℝ} {V : Set E} (hV : IsOpen V) (hu : ContDiffOn ℝ 1 u V)
    (hbound : ∀ y ∈ V, ∀ w : E, fderiv ℝ u y w ≤ (F.chartLength x₀ (y, w) : ℝ))
    {x : M} (hx : x ∈ chartCalibrationDomain x₀ V)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (u ∘ extChartAt 𝓘(ℝ, E) x₀) x v)
      (F.toFun ⟨x, v⟩ : ℝ) := by
  rw [mfderiv_chartPullback_apply x₀ hV hu hx]
  have h := hbound _ hx.2 (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v)
  rwa [F.chartLength_mfderiv_extChartAt x₀ hx.1] at h

/-- Saturation in the actual coordinate velocity transfers to saturation of the original length. -/
theorem mfderiv_chartPullback_eq (F : ContinuousFinslerNorm E M) (x₀ : M)
    {u : E → ℝ} {V : Set E} (hV : IsOpen V) (hu : ContDiffOn ℝ 1 u V)
    {x : M} (hx : x ∈ chartCalibrationDomain x₀ V)
    (v : TangentSpace 𝓘(ℝ, E) x)
    (hsat : fderiv ℝ u (extChartAt 𝓘(ℝ, E) x₀ x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v) =
      (F.chartLength x₀ (extChartAt 𝓘(ℝ, E) x₀ x,
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v) : ℝ)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (u ∘ extChartAt 𝓘(ℝ, E) x₀) x v =
      (F.toFun ⟨x, v⟩ : ℝ) := by
  rw [mfderiv_chartPullback_apply x₀ hV hu hx, hsat,
    F.chartLength_mfderiv_extChartAt x₀ hx.1]

end Pullback
end ContinuousFinslerNorm
end OTSelector.Geometry
