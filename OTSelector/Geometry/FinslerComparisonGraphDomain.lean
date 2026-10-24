import OTSelector.Topology.Real.OpenTimeInterval
import OTSelector.Geometry.FinslerSmoothPhaseJetData
import OTSelector.Geometry.Manifold.CurveGraphRegularSource

/-!
Conditions: An open product set contains the given parameter/time point.

Objects: A nontrivial closed time interval centered around that actual point and contained in the same open set.

Proof detail: Take a product neighborhood, shrink its time radius and choose two interior endpoints.

Sources: D. H. Fremlin, Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products) (https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6).
Relation: Elementary product-topology corollary; only the selected interval lemma is covered from the original file.
-/

/-!
# Constructed regular domains for the comparison's same graph coordinates

The complete comparison supplies the required C² position germ. Its actual positive
adapted velocity then constructs an open domain in the chosen graph chart, retaining
that chart and any prescribed graph-phase domain. Closed time neighborhoods lie inside
this domain, so the same geometric data remain valid at both endpoints.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]



namespace ContinuousFinslerNorm.SmoothPhaseJetComparison

set_option backward.isDefEq.respectTransparency false

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual comparison constructs a regular open source domain for the supplied
same graph inverse, mapped into its actual graph-phase domain. -/
theorem exists_regular_graph_source
    {initial : M} {t₀ : ℝ} {w₀ : W} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w₀ z₀ R Q)
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V)) (t : ℝ)
    (hx : C.curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hpositive : 0 < (A (deriv (extChartAt 𝓘(ℝ, E) old ∘ C.curve w₀) t)).1)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap
      (fun q ↦ A (extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2))))
    (hsource : (w₀, t) ∈ e.source) {D : Set (W × ℝ)} (hD : IsOpen D)
    (hcenter : (w₀, (A (extChartAt 𝓘(ℝ, E) old (C.curve w₀ t))).1) ∈ D) :
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2))
    ∃ U : Set (W × ℝ), IsOpen U ∧ (w₀, t) ∈ U ∧ U ⊆ e.source ∧ MapsTo e U D ∧
      ContDiffOn ℝ 2 γ U ∧ ∀ q ∈ U,
        0 < (fderiv ℝ γ q (0, 1)).1 ∧ DifferentiableAt ℝ e.symm (e q) := by
  let γ₀ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2)
  let γ := fun q : W × ℝ ↦ A (γ₀ q)
  have hΨ := hF.contDiffAt_chartMomentumFamily_of_tangentFamily C.open_labels C.complete
    C.tangent_C2 C.anchor_mem old t hx
  have hγ₀ : ContDiffAt ℝ 2 γ₀ (w₀, t) := hΨ.fst
  have hγ : ContDiffAt ℝ 2 γ (w₀, t) := A.contDiff.contDiffAt.comp (w₀, t) hγ₀
  have hd₀ := (hγ₀.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t w₀).prodMk (hasDerivAt_id t))
  have hvelocity : fderiv ℝ γ (w₀, t) (0, 1) =
      A (deriv (extChartAt 𝓘(ℝ, E) old ∘ C.curve w₀) t) := by
    have hd := (A.hasFDerivAt.comp (w₀, t)
      (hγ₀.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    change fderiv ℝ γ (w₀, t) = _ at hd
    rw [hd]
    exact congrArg A hd₀.deriv.symm
  apply exists_curveGraph_regular_source_of_contDiffAt he hγ hsource hD hcenter
  rwa [hvelocity]

end ContinuousFinslerNorm.SmoothPhaseJetComparison
end OTSelector.Geometry
