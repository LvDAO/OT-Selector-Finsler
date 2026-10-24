import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
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
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
## Lemma skeleton

* **Conditions:** Two overlapping smooth manifold charts and tangent vectors; nonzero fiber vectors for slit domains.
* **Objects:** Coordinate transition, its invertible derivative and the pulled-back chart energy.
* **Proof detail:** Use inverse-chart identities, differentiate both inverse compositions, and identify the same tangent vector in either chart.

## Mathematical sources

* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** All slit-domain and energy-germ wrappers are implementation consequences of the manifold chain rule. The source reference gives chart/tangent calculus, not project-specific transition names.
-/

/-!
# Actual Finsler energy under a change of manifold coordinates

Coordinate changes and their derivatives are taken from the given smooth atlas.
On the actual open overlap they preserve the represented tangent vector, and hence
preserve the original Finsler energy when position and velocity are transformed together.
The atlas also supplies continuous linear invertibility of the actual transition derivative,
so nonzero velocities stay nonzero. No inner product or finite-dimensional assumption is used.

This is a geometric coordinate identity; Euler–Lagrange covariance is a separate calculus step.
-/

open Bundle Set Filter
open scoped Manifold Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual transition from the coordinates at `new` to those at `old`. -/
def chartTransition (old new : M) : E → E :=
  extChartAt 𝓘(ℝ, E) old ∘ (extChartAt 𝓘(ℝ, E) new).symm

/-- New coordinates whose represented base point also lies in the old chart. -/
def chartTransitionDomain (old new : M) : Set E :=
  (extChartAt 𝓘(ℝ, E) new).target ∩
    (extChartAt 𝓘(ℝ, E) new).symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).source

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The genuine overlap of the coordinate charts is open. -/
theorem isOpen_chartTransitionDomain (old new : M) :
    IsOpen (chartTransitionDomain (E := E) old new) := by
  exact (continuousOn_extChartAt_symm new).isOpen_inter_preimage
    (isOpen_extChartAt_target new) (isOpen_extChartAt_source old)

/-- Smoothness of the transition is supplied by the given manifold atlas. -/
theorem contDiffOn_chartTransition (old new : M) :
    ContDiffOn ℝ ∞ (chartTransition (E := E) old new) (chartTransitionDomain old new) := by
  exact contDiffOn_ext_coord_change old new

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A transition point is in the target of the old chart. -/
theorem chartTransition_mem_target (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) :
    chartTransition old new y ∈ (extChartAt 𝓘(ℝ, E) old).target :=
  (extChartAt 𝓘(ℝ, E) old).map_source hy.2

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Returning to the manifold after the transition recovers the same base point. -/
theorem chart_symm_chartTransition (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) :
    (extChartAt 𝓘(ℝ, E) old).symm (chartTransition old new y) =
      (extChartAt 𝓘(ℝ, E) new).symm y :=
  (extChartAt 𝓘(ℝ, E) old).left_inv hy.2

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The transition maps the actual overlap into the reverse overlap. -/
theorem mapsTo_chartTransition (old new : M) :
    MapsTo (chartTransition (E := E) old new) (chartTransitionDomain old new)
      (chartTransitionDomain new old) := by
  intro y hy
  refine ⟨chartTransition_mem_target old new hy, ?_⟩
  change (extChartAt 𝓘(ℝ, E) old).symm (chartTransition old new y) ∈
    (extChartAt 𝓘(ℝ, E) new).source
  rw [chart_symm_chartTransition old new hy]
  exact (extChartAt 𝓘(ℝ, E) new).map_target hy.1

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The two actual coordinate transitions are inverse on their overlap. -/
theorem chartTransition_reverse (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) :
    chartTransition new old (chartTransition old new y) = y := by
  change extChartAt 𝓘(ℝ, E) new
    ((extChartAt 𝓘(ℝ, E) old).symm (chartTransition old new y)) = y
  rw [chart_symm_chartTransition old new hy]
  exact (extChartAt 𝓘(ℝ, E) new).right_inv hy.1

/-- The atlas supplies continuous linear invertibility of the actual transition derivative. -/
theorem isInvertible_fderiv_chartTransition (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) :
    (fderiv ℝ (chartTransition old new) y).IsInvertible := by
  have h := (𝓘(ℝ, E)).isInvertible_fderivWithin_extendCoordChange (n := ∞) (by simp)
    (IsManifold.chart_mem_maximalAtlas new) (IsManifold.chart_mem_maximalAtlas old) hy
  change (fderivWithin ℝ (chartTransition old new)
    (chartTransitionDomain old new) y).IsInvertible at h
  rwa [fderivWithin_of_isOpen (isOpen_chartTransitionDomain old new) hy] at h

/-- The actual coordinate derivative is bijective without a finite-dimensional assumption. -/
theorem fderiv_chartTransition_bijective (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) :
    Function.Bijective (fderiv ℝ (chartTransition old new) y) := by
  obtain ⟨e, he⟩ := isInvertible_fderiv_chartTransition old new hy
  rw [← he]
  exact e.bijective

/-- The coordinate derivative is injective on the actual overlap. -/
theorem fderiv_chartTransition_injective (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) :
    Function.Injective (fderiv ℝ (chartTransition old new) y) :=
  (fderiv_chartTransition_bijective old new hy).1

/-- The coordinate derivative is surjective on the actual overlap. -/
theorem fderiv_chartTransition_surjective (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) :
    Function.Surjective (fderiv ℝ (chartTransition old new) y) :=
  (fderiv_chartTransition_bijective old new hy).2

/-- Nonzero tangent velocities remain nonzero under the actual coordinate derivative. -/
theorem fderiv_chartTransition_ne_zero (old new : M) {y w : E}
    (hy : y ∈ chartTransitionDomain old new) (hw : w ≠ 0) :
    fderiv ℝ (chartTransition old new) y w ≠ 0 := by
  intro h
  apply hw
  exact (fderiv_chartTransition_injective old new hy)
    (h.trans ((fderiv ℝ (chartTransition old new) y).map_zero.symm))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The slit part of the actual overlap is open in position and velocity. -/
theorem isOpen_chartTransitionSlitDomain (old new : M) :
    IsOpen (chartTransitionDomain (E := E) old new ×ˢ {w : E | w ≠ 0}) :=
  (isOpen_chartTransitionDomain old new).prod isOpen_ne

/-- The actual tangent lift maps the slit overlap into the old energy chart domain. -/
theorem mapsTo_chartTransition_energyDomain (old new : M) :
    MapsTo
      (fun z : E × E ↦
        (chartTransition old new z.1, fderiv ℝ (chartTransition old new) z.1 z.2))
      (chartTransitionDomain old new ×ˢ {w : E | w ≠ 0})
      (ContinuousFinslerNorm.chartEnergyDomain old) := by
  intro z hz
  exact ⟨chartTransition_mem_target old new hz.1,
    fderiv_chartTransition_ne_zero old new hz.1 hz.2⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Every state in the slit overlap belongs to the new energy chart domain. -/
theorem chartTransitionSlitDomain_subset (old new : M) :
    chartTransitionDomain (E := E) old new ×ˢ {w : E | w ≠ 0} ⊆
      ContinuousFinslerNorm.chartEnergyDomain new :=
  fun _ hz ↦ ⟨hz.1.1, hz.2⟩

/-- The actual tangent lift of the coordinate change is smooth on the full fiber overlap. -/
theorem contDiffOn_chartTransition_phase (old new : M) :
    ContDiffOn ℝ ∞
      (fun z : E × E ↦
        (chartTransition old new z.1, fderiv ℝ (chartTransition old new) z.1 z.2))
      (chartTransitionDomain old new ×ˢ (univ : Set E)) := by
  have hf := contDiffOn_chartTransition (E := E) old new
  have hd := hf.fderiv_of_isOpen (isOpen_chartTransitionDomain old new)
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  exact (hf.comp contDiffOn_fst (fun _ h ↦ h.1)).prodMk
    ((hd.comp contDiffOn_fst (fun _ h ↦ h.1)).clm_apply contDiffOn_snd)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse tangent charts represent exactly the same genuine tangent vector. -/
theorem tangentChart_symm_chartTransition (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) (w : E) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
        (chartTransition old new y, fderiv ℝ (chartTransition old new) y w) =
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨new, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (y, w) := by
  have hd : DifferentiableAt ℝ (chartTransition old new) y :=
    ((contDiffOn_chartTransition old new).contDiffAt
      ((isOpen_chartTransitionDomain old new).mem_nhds hy)).differentiableAt (by simp)
  have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) old).symm (chartTransition old new y) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm (chartTransition_mem_target old new hy)
  have heq : (extChartAt 𝓘(ℝ, E) old).symm ∘ chartTransition old new =ᶠ[𝓝 y]
      (extChartAt 𝓘(ℝ, E) new).symm := by
    filter_upwards [(isOpen_chartTransitionDomain old new).mem_nhds hy] with z hz
    exact chart_symm_chartTransition old new hz
  have htm : tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) (chartTransition old new) ⟨y, w⟩ =
      ⟨chartTransition old new y, fderiv ℝ (chartTransition old new) y w⟩ := by
    simp only [tangentMap, mfderiv_eq_fderiv]
    rfl
  rw [tangentChart_symm_eq_tangentMap old (chartTransition_mem_target old new hy),
    tangentChart_symm_eq_tangentMap new hy.1, ← htm,
    ← tangentMap_comp_at ⟨y, w⟩ hc hd.mdifferentiableAt]
  apply TotalSpace.ext heq.self_of_nhds
  unfold tangentMap
  rw [heq.mfderiv_eq]
  rfl

namespace ContinuousFinslerNorm

/-- The actual Finsler energy is invariant under the actual position-and-velocity change.
This holds for every velocity, including zero, on the genuine base overlap. -/
theorem chartEnergy_chartTransition (F : ContinuousFinslerNorm E M) (old new : M) {y : E}
    (hy : y ∈ chartTransitionDomain old new) (w : E) :
    F.chartEnergy new (y, w) = F.chartEnergy old
      (chartTransition old new y, fderiv ℝ (chartTransition old new) y w) := by
  unfold chartEnergy
  rw [tangentChart_symm_chartTransition old new hy]

/-- The energy identity holds on a full phase neighborhood, so ordinary derivatives
of every order may be transferred between the two coordinate expressions. -/
theorem chartEnergy_eventuallyEq_chartTransition (F : ContinuousFinslerNorm E M)
    (old new : M) {y : E} (hy : y ∈ chartTransitionDomain old new) (w : E) :
    F.chartEnergy new =ᶠ[𝓝 (y, w)]
      (fun z ↦ F.chartEnergy old
        (chartTransition old new z.1, fderiv ℝ (chartTransition old new) z.1 z.2)) := by
  filter_upwards [((isOpen_chartTransitionDomain old new).prod isOpen_univ).mem_nhds
    (show (y, w) ∈ chartTransitionDomain old new ×ˢ (univ : Set E) from ⟨hy, mem_univ w⟩)]
      with z hz
  exact F.chartEnergy_chartTransition old new hz.1 z.2

end ContinuousFinslerNorm
end OTSelector.Geometry
