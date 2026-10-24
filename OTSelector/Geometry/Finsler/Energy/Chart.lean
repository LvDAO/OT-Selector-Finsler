import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** A smooth manifold chart and the original tangent length. Joint smoothness and Hessian positivity use IsSmoothStronglyConvex; the final local inverse/Hamiltonian existence conclusions use finite dimension.
* **Objects:** The original energy in a fixed tangent chart, the chart slit domain, its actual linear fiber change and a jointly smooth local base-momentum Legendre inverse.
* **Proof detail:** Identify the true tangent-chart inverse fiber map as a continuous linear equivalence. Apply the second-derivative chain rule to transport positive Hessians, then invoke the parametric local Legendre inverse and local Hamiltonian construction.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 2, pp. 304–305, smooth slit energy and positive fundamental tensor.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 2, p. 308, derivative Legendre map and inverse, equation (2–12).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
  https://www.jirka.org/ra/realanal2.pdf#page=51

**Relationship to the sources:** This supplies the explicit chart and bundle calculus behind the standard smooth Finsler/Legendre discussion. It is a coordinate implementation of that construction; joint local inverse properties are proved for the actual chart energy.
-/

/-!
# Joint smooth Finsler energy and Legendre coordinates

Express the actual tangent-bundle energy in one fixed chart. The fiber chart change
is a continuous linear equivalence, so strong convexity transfers to the actual
vertical Hessian. The parameterized inverse theorem then supplies a Legendre inverse
jointly smooth in the base point and momentum, on its actual open target.

These are local coordinates for the general smooth Finsler energy. Geodesic flow,
its relation to minimizing length, and Jacobi fields remain separate constructions.
-/

open Bundle Set Manifold Filter
open scoped ContDiff Topology

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual second derivative transforms covariantly under a fixed linear fiber change. -/
theorem fderiv2_comp_linearEquiv {L : E → ℝ} (e : E ≃L[ℝ] E) {v : E}
    (h2 : DifferentiableAt ℝ (fderiv ℝ L) (e v)) (u w : E) :
    fderiv ℝ (fderiv ℝ (L ∘ e)) v u w =
      fderiv ℝ (fderiv ℝ L) (e v) (e u) (e w) := by
  have hfirst : fderiv ℝ (L ∘ e) = fun x ↦ (fderiv ℝ L (e x)).comp (e : E →L[ℝ] E) := by
    funext x
    exact e.comp_right_fderiv
  rw [hfirst]
  have hsecond := (h2.hasFDerivAt.comp v e.hasFDerivAt).clm_comp
    (hasFDerivAt_const (e : E →L[ℝ] E) v)
  have hs := hsecond.fderiv
  simp only [Function.comp_def] at hs
  rw [hs]
  simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm

/-- The actual energy expressed in one fixed tangent-bundle chart. -/
def chartEnergy (F : ContinuousFinslerNorm E M) (x₀ : M) (z : E × E) : ℝ :=
  F.energy ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
    (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)

/-- Local base chart coordinates and nonzero fiber velocities. -/
def chartEnergyDomain (x₀ : M) : Set (E × E) :=
  (extChartAt 𝓘(ℝ, E) x₀).target ×ˢ {v : E | v ≠ 0}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The energy coordinate domain is open. -/
theorem isOpen_chartEnergyDomain (x₀ : M) : IsOpen (chartEnergyDomain (E := E) x₀) :=
  (isOpen_extChartAt_target x₀).prod isOpen_ne

/-- The inverse chart's base point belongs to the fixed tangent trivialization. -/
theorem chartEnergy_base_mem (x₀ : M) {u : E}
    (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    (extChartAt 𝓘(ℝ, E) x₀).symm u ∈
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source 𝓘(ℝ, E)]
  exact (extChartAt 𝓘(ℝ, E) x₀).map_target hu

/-- Inverse tangent charts act linearly and invertibly on each fiber. -/
theorem tangentChart_symm_eq (x₀ : M) {u : E}
    (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (v : E) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (u, v) =
    ⟨(extChartAt 𝓘(ℝ, E) x₀).symm u,
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearEquivAt ℝ
        ((extChartAt 𝓘(ℝ, E) x₀).symm u) (chartEnergy_base_mem x₀ hu)).symm v⟩ := by
  rw [FiberBundle.extChartAt]
  exact Bundle.Trivialization.symm_apply_eq_mk_continuousLinearEquivAt_symm
    _ _ (chartEnergy_base_mem x₀ hu) v

/-- The tangent chart target is exactly the product of the base target and all velocities. -/
theorem tangentChart_target (x₀ : M) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).target =
      (extChartAt 𝓘(ℝ, E) x₀).target ×ˢ (univ : Set E) := by
  rw [FiberBundle.extChartAt_target]
  congr 1
  apply inter_eq_left.mpr
  intro u hu
  exact chartEnergy_base_mem x₀ hu

/-- The inverse fiber coordinate map in the linear model representation of that actual fiber. -/
def chartFiberEquiv (x₀ : M) {u : E} (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    E ≃L[ℝ] E :=
  (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearEquivAt ℝ
    ((extChartAt 𝓘(ℝ, E) x₀).symm u) (chartEnergy_base_mem x₀ hu)).symm).trans
      (tangentFiberModelEquiv ((extChartAt 𝓘(ℝ, E) x₀).symm u)).symm

/-- Coordinate energy is the original fiber energy composed with the true linear chart change. -/
theorem chartEnergy_eq_fiberEnergyModel (F : ContinuousFinslerNorm E M) (x₀ : M)
    {u : E} (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (v : E) :
    F.chartEnergy x₀ (u, v) = F.fiberEnergyModel ((extChartAt 𝓘(ℝ, E) x₀).symm u)
      (chartFiberEquiv x₀ hu v) := by
  rw [chartEnergy, tangentChart_symm_eq x₀ hu]
  simp only [fiberEnergyModel, chartFiberEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, fiberEnergy]

/-- Homogeneity survives the actual tangent coordinate change. -/
theorem chartEnergy_smul (F : ContinuousFinslerNorm E M) (x₀ : M)
    {u : E} (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (r : ℝ) (v : E) :
    F.chartEnergy x₀ (u, r • v) = r ^ 2 * F.chartEnergy x₀ (u, v) := by
  rw [F.chartEnergy_eq_fiberEnergyModel x₀ hu, F.chartEnergy_eq_fiberEnergyModel x₀ hu]
  rw [_root_.map_smul, F.fiberEnergyModel_smul]

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The actual energy is jointly smooth in base and velocity on a fixed tangent chart. -/
theorem contDiffOn_chartEnergy (x₀ : M) :
    ContDiffOn ℝ ∞ (F.chartEnergy x₀) (chartEnergyDomain x₀) := by
  intro z hz
  let p₀ : TangentBundle 𝓘(ℝ, E) M := ⟨x₀, 0⟩
  let c := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) p₀
  have hz' : z ∈ c.target := by
    rw [tangentChart_target]
    exact ⟨hz.1, mem_univ _⟩
  have hi : ContMDiffAt 𝓘(ℝ, E × E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ c.symm z := by
    have h := contMDiffWithinAt_extChartAt_symm_range (n := ∞) p₀ hz'
    simpa only [← modelWithCornersSelf_prod, modelWithCornersSelf_coe, Set.range_id,
      contMDiffWithinAt_univ] using! h
  have hslit : c.symm z ∈ {p : TangentBundle 𝓘(ℝ, E) M | p.2 ≠ 0} := by
    dsimp only [c, p₀]
    rw [show z = (z.1, z.2) from rfl, tangentChart_symm_eq x₀ hz.1]
    let e := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).continuousLinearEquivAt ℝ
      ((extChartAt 𝓘(ℝ, E) x₀).symm z.1) (chartEnergy_base_mem x₀ hz.1)
    change e.symm z.2 ≠ 0
    exact fun he ↦ hz.2 (e.symm.injective (he.trans (_root_.map_zero e.symm).symm))
  have he := hF.contMDiffOn_energy.contMDiffAt (F.isOpen_slitTangent.mem_nhds hslit)
  exact (he.comp z hi).contDiffAt.contDiffWithinAt

/-- Strong convexity transfers to the actual vertical Hessian in a fixed tangent chart. -/
theorem chartEnergy_hessian_pos (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀)
    {w : E} (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (fun v ↦ F.chartEnergy x₀ (z.1, v))) z.2 w w := by
  let y := (extChartAt 𝓘(ℝ, E) x₀).symm z.1
  let e := chartFiberEquiv x₀ hz.1
  have heq : (fun v ↦ F.chartEnergy x₀ (z.1, v)) = F.fiberEnergyModel y ∘ e :=
    funext (F.chartEnergy_eq_fiberEnergyModel x₀ hz.1)
  have hv : e z.2 ≠ 0 := fun h ↦ hz.2 (e.injective (h.trans (_root_.map_zero e).symm))
  have hw' : e w ≠ 0 := fun h ↦ hw (e.injective (h.trans (_root_.map_zero e).symm))
  rw [heq, fderiv2_comp_linearEquiv e (hF.differentiableAt_legendre y hv)]
  exact hF.hessian_pos y (e z.2) hv (e w) hw'

/-- The actual Finsler Legendre map has a local inverse jointly smooth in base and momentum. -/
theorem exists_smooth_chartLegendre_local_inverse [FiniteDimensional ℝ E]
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀) ∧
      z ∈ e.source ∧ parametricLegendre (F.chartEnergy x₀) z ∈ e.target ∧
      e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ (parametricLegendre (F.chartEnergy x₀)) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.target, (e.symm p).1 = p.1) ∧
      ∀ p ∈ e.target, HasFDerivAt e.symm
        (ContinuousLinearMap.inverse
          (fderiv ℝ (parametricLegendre (F.chartEnergy x₀)) (e.symm p))) p := by
  exact exists_smooth_parametricLegendre_local_inverse (isOpen_chartEnergyDomain x₀)
    (hF.contDiffOn_chartEnergy x₀)
    (fun _ hz _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw) hz

/-- The actual Finsler energy constructs a smooth local Hamiltonian and its canonical field. -/
theorem exists_smooth_chartHamiltonian [FiniteDimensional ℝ E]
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀) ∧
      z ∈ e.source ∧ parametricLegendre (F.chartEnergy x₀) z ∈ e.target ∧
      e.source ⊆ chartEnergyDomain x₀ ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonian (F.chartEnergy x₀) e) e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonianVectorField (F.chartEnergy x₀) e) e.target ∧
      ∀ p ∈ e.target, ∀ dq : E × (E →L[ℝ] ℝ),
        fderiv ℝ (localHamiltonian (F.chartEnergy x₀) e) p dq =
          dq.2 (localHamiltonianVectorField (F.chartEnergy x₀) e p).1 -
            (localHamiltonianVectorField (F.chartEnergy x₀) e p).2 dq.1 := by
  exact exists_smooth_localHamiltonian (isOpen_chartEnergyDomain x₀)
    (hF.contDiffOn_chartEnergy x₀)
    (fun _ hz _ hw ↦ hF.chartEnergy_hessian_pos x₀ hz hw) hz

end IsSmoothStronglyConvex

end ContinuousFinslerNorm
end OTSelector.Geometry
