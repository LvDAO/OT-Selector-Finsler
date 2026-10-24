import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
## Lemma skeleton

* **Conditions:** A differentiable coordinate curve staying in a manifold chart target.
* **Objects:** Its actual tangent vector in inverse tangent-chart coordinates.
* **Proof detail:** Apply the manifold chain rule to the inverse chart and use tangent-trivialization inverse identities.

## Mathematical sources

* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** This is the tangent-bundle representation adapter for velocity vectors; no new intrinsic geometry theorem or Riemannian structure is assumed.
-/

/-!
# Tangent velocities of curves reconstructed from a chart

The inverse chart on the total tangent bundle agrees with the tangent map of the inverse
base chart. Consequently an ordinary coordinate derivative `HasDerivAt u v t` identifies
the actual manifold velocity of the reconstructed curve with the inverse tangent chart
at `(u t, v)`. The conclusion is an equality in the total tangent bundle, so no transport
between separately written dependent fibers is needed.

Only a differentiable manifold structure is required. This module establishes the
kinematic chart identity; it makes no assumption or conclusion about coordinate covariance
of a dynamical system.
-/

open Bundle Set
open scoped Manifold Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse total tangent chart is the tangent map of the inverse base chart. -/
theorem tangentChart_symm_eq_tangentMap (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (v : E) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (y, v) =
    tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm ⟨y, v⟩ := by
  have hx : (extChartAt 𝓘(ℝ, E) x₀).symm y ∈ (chartAt E x₀).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) x₀).map_target hy
  have hb : (extChartAt 𝓘(ℝ, E) x₀).symm y ∈
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hd := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, E)) hx
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
  rw [FiberBundle.extChartAt]
  change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).toOpenPartialHomeomorph.symm
    ((extChartAt 𝓘(ℝ, E) x₀).symm y, v) = _
  rw [Bundle.Trivialization.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) _ _ hb v]
  unfold tangentMap
  congr 1
  rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq (R := ℝ), hd]
  congr 2
  exact (extChartAt 𝓘(ℝ, E) x₀).right_inv hy

set_option backward.isDefEq.respectTransparency false in
/-- The tangent velocity of a curve reconstructed from coordinates is the inverse
of the tangent chart applied to its coordinate position and ordinary derivative. -/
theorem tangentMap_chart_symm_curve (x₀ : M) {u : ℝ → E} {t : ℝ} {v : E}
    (hu : u t ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (hdu : HasDerivAt u v t) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ u) ⟨t, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (u t, v) := by
  have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) x₀).symm (u t) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hu
  have hut : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u ⟨t, (1 : ℝ)⟩ = ⟨u t, v⟩ := by
    simp only [tangentMap, mfderiv_eq_fderiv]
    congr 1
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := u) (x := t)).trans hdu.deriv
  rw [tangentMap_comp_at ⟨t, (1 : ℝ)⟩ hc hdu.differentiableAt.mdifferentiableAt, hut]
  exact (tangentChart_symm_eq_tangentMap x₀ hu v).symm

set_option backward.isDefEq.respectTransparency false in
/-- At its own anchor the inverse tangent chart returns the given tangent vector. -/
theorem tangentChart_symm_self (x₀ : M) (v : E) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
        (extChartAt 𝓘(ℝ, E) x₀ x₀, v) = ⟨x₀, v⟩ := by
  rw [tangentChart_symm_eq_tangentMap x₀ (mem_extChartAt_target x₀) v]
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀)
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
  have ht : tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm
      ⟨extChartAt 𝓘(ℝ, E) x₀ x₀, v⟩ =
      ⟨(extChartAt 𝓘(ℝ, E) x₀).symm (extChartAt 𝓘(ℝ, E) x₀ x₀), v⟩ := by
    unfold tangentMap
    congr 1
    exact congrArg (fun T : E →L[ℝ] E ↦ T v) hd
  rw [ht]
  congr 1
  exact (extChartAt 𝓘(ℝ, E) x₀).left_inv (mem_extChartAt_source x₀)

end OTSelector.Geometry
