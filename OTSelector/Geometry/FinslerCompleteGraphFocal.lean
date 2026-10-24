import OTSelector.Geometry.Finsler.CompleteRegraphedJacobi
import OTSelector.Geometry.GraphVariationPole
import OTSelector.Geometry.FinslerGraphFocal

/-!
# Focal expansions for the same complete-family graph chart

The constructed reduced Jacobi chart supplies its own full phase rank and canonical
isotropy. Its actual graph velocity lies in the same original Legendre branch, so the
actual graph momentum lies in that branch's target. The existing positive-Hessian focal
theorems therefore give regular crossing, an exact smooth inverse pole, and two-sided
rates for the position variation of this very family and graph inverse.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι]

/-- The actual central position variation has regular crossing, a smooth simple inverse
pole with the exact kernel rank, and two-sided determinant and inverse-norm bounds. -/
def HasGraphFocalExpansion (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (Ψ : W × ℝ → V × (V →L[ℝ] ℝ)) (D : Set (W × ℝ)) (w₀ : W) : Prop :=
  let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
  let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
  ∀ t, (w₀, t) ∈ D →
    Function.Bijective (focalCrossingMap (J t) (deriv J t)) ∧
    (∃ (U : Set ℝ) (R : Matrix ι ι ℝ) (K : ℝ → Matrix ι ι ℝ),
      IsOpen U ∧ 0 ∈ U ∧ U ⊆ {s | (w₀, t + s) ∈ D} ∧ ContDiffOn ℝ ∞ K U ∧
      (∀ s ∈ U, s ≠ 0 → (J (t + s)).det ≠ 0 ∧
        (J (t + s))⁻¹ = s⁻¹ • R + K s) ∧
      R.rank = Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ∧
      (0 < Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) → R ≠ 0)) ∧
    (0 < Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) →
      ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ∃ cdet Cdet cinv Cinv : ℝ,
        0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
        ∀ᶠ s in 𝓝[>] (0 : ℝ),
          cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ≤
              |(J (t + ε * s)).det| ∧
            |(J (t + ε * s)).det| ≤
              Cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ∧
            cinv / |s| ≤ ‖(J (t + ε * s))⁻¹‖ ∧
            ‖(J (t + ε * s))⁻¹‖ ≤ Cinv / |s|)

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- The already constructed Jacobi chart has the actual focal expansion on every central
slice. The graph inverse, original Legendre branch and neighborhood are preserved. -/
theorem exists_completeGraph_focalChart (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {Γ : W → ℝ → M} {B : Set W} {w₀ : W} {old : M} {t₀ : ℝ}
    (hchart : F.HasGraphJacobiChart Γ B w₀ old t₀) :
    let γ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ q.1 q.2)
    let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
    let L := F.chartGraphLagrangian old
    ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
      (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
      (D : Set (W × ℝ)),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      (w₀, t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ univ ∧
      (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) old).target ×ˢ univ ∧
      ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
      ContDiffOn ℝ 2 (F.chartGraphPhase old γ e) D ∧
      (∀ q ∈ D,
        let P := F.chartGraphPhase old γ e
        graphVelocityPhase (fun p ↦ (curveGraphPosition γ e p).2) q ∈ g.source ∧
        ((q.2, (P q).1), (P q).2) ∈ g.target ∧
        HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2) ∧
      (∀ q ∈ D, q.1 = w₀ →
        let R := fderiv ℝ (fun w ↦ F.chartGraphPhase old γ e (w, q.2)) q.1
        Function.Injective R ∧ ∀ ξ η : W, canonicalPhasePairing (R ξ) (R η) = 0) ∧
      HasGraphFocalExpansion bW bV (F.chartGraphPhase old γ e) D w₀ := by
  obtain ⟨e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget,
    hΨ, hJacobi, hphase⟩ := hchart
  let γ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ q.1 q.2)
  let P := F.chartGraphPhase old γ e
  have hmap (q : W × ℝ) (hq : q ∈ D) : ((q.2, (P q).1), (P q).2) ∈ g.target := by
    have h := g.map_source (hJacobi q hq).1
    rw [hg] at h
    exact h
  have hODE (q : W × ℝ) (hq : q ∈ D) :
      HasDerivAt (fun s ↦ P (q.1, s))
        (GraphHamiltonian.field (F.chartGraphLagrangian old) g q.2 (P q)) q.2 :=
    (hJacobi q hq).2.1
  refine ⟨e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget, hΨ,
    fun q hq ↦ ⟨(hJacobi q hq).1, hmap q hq, hODE q hq⟩, hphase, ?_⟩
  intro t ht
  have hp : ∀ s, (w₀, s) ∈ D → ((s, (P (w₀, s)).1), (P (w₀, s)).2) ∈ g.target :=
    fun s hs ↦ hmap (w₀, s) hs
  have hrank := hphase (w₀, t) ht rfl
  have hcross := hF.chartGraph_regular_focal_bounds old bW bV hg hsub hG hD hΨ hODE
    ht (hp t ht) hrank.1 hrank.2
  have hpole := hF.chartGraph_exists_smooth_inverse_pole old bW bV hg hsub hG hD hΨ hODE
    ht hp hrank.1 hrank.2
  exact ⟨hcross.1, hpole, hcross.2⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
