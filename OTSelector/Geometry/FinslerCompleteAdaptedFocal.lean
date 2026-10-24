import OTSelector.Geometry.Finsler.CompleteAdaptedJacobi
import OTSelector.Geometry.FinslerAdaptedGraphFocal
import OTSelector.Geometry.FinslerGraphFocalFinite

/-!
# Actual focal charts of the same complete family in adapted coordinates

The constructed adapted Jacobi chart supplies the original graph Legendre branch and
actual phase structure. Equal parameter and spatial dimensions choose matching bases
without changing the family. The very same graph inverse and domain carry exact focal
expansions and finitely many singular times on each compact subset of that domain.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- An actual adapted graph chart of the given family has exact focal expansions and
finitely many singular times in compact parts of its central time domain. -/
def HasAdaptedGraphFocalChart (F : ContinuousFinslerNorm E M)
    (A : E ≃L[ℝ] (ℝ × V)) (Γ : W → ℝ → M) (B : Set W)
    (w₀ : W) (old : M) (t₀ : ℝ) : Prop :=
  ∃ bW : Basis (Fin (Module.finrank ℝ V)) ℝ W,
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
    let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
    let L := F.adaptedGraphLagrangian old A
    ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
      (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
      (D : Set (W × ℝ)),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      (w₀, t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ univ ∧
      (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ ∧
      ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
      ContDiffOn ℝ 2 (F.adaptedGraphPhase old A γ e) D ∧
      (∀ q ∈ D,
        let P := F.adaptedGraphPhase old A γ e
        graphVelocityPhase (fun p ↦ (curveGraphPosition γ e p).2) q ∈ g.source ∧
        ((q.2, (P q).1), (P q).2) ∈ g.target ∧
        HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2) ∧
      (∀ q ∈ D, q.1 = w₀ →
        let R := fderiv ℝ (fun w ↦ F.adaptedGraphPhase old A γ e (w, q.2)) q.1
        Function.Injective R ∧ ∀ ξ η : W, canonicalPhasePairing (R ξ) (R η) = 0) ∧
      HasGraphFocalExpansion bW (Module.finBasis ℝ V)
        (F.adaptedGraphPhase old A γ e) D w₀ ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ {t | (w₀, t) ∈ D} →
        let Z := fun s ↦ fderiv ℝ (fun w ↦ F.adaptedGraphPhase old A γ e (w, s)) w₀
        let J := fun s ↦ vectorFamilyMatrix (Module.finBasis ℝ V)
          (fun j ↦ (Z s (bW j)).1)
        {t ∈ K | (J t).det = 0}.Finite

namespace IsSmoothStronglyConvex

/-- The constructed adapted Jacobi chart yields its own focal chart in automatically
matched bases, retaining its exact graph inverse, branch, domain and actual family. -/
theorem hasAdaptedGraphFocalChart_of_finrank [FiniteDimensional ℝ W]
    (hF : F.IsSmoothStronglyConvex)
    {A : E ≃L[ℝ] (ℝ × V)} {Γ : W → ℝ → M} {B : Set W}
    {w₀ : W} {old : M} {t₀ : ℝ}
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V)
    (hchart : F.HasAdaptedGraphJacobiChart A Γ B w₀ old t₀) :
    F.HasAdaptedGraphFocalChart A Γ B w₀ old t₀ := by
  let a : V ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let bW : Basis (Fin (Module.finrank ℝ V)) ℝ W :=
    (Module.finBasis ℝ V).map a.toLinearEquiv
  obtain ⟨e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget,
    hΨ, hJacobi, hphase⟩ := hchart
  let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
  let P := F.adaptedGraphPhase old A γ e
  have hmap (q : W × ℝ) (hq : q ∈ D) : ((q.2, (P q).1), (P q).2) ∈ g.target := by
    have h := g.map_source (hJacobi q hq).1
    rw [hg] at h
    exact h
  have hODE (q : W × ℝ) (hq : q ∈ D) :
      HasDerivAt (fun s ↦ P (q.1, s))
        (GraphHamiltonian.field (F.adaptedGraphLagrangian old A) g q.2 (P q)) q.2 :=
    (hJacobi q hq).2.1
  have hfocal : HasGraphFocalExpansion bW (Module.finBasis ℝ V) P D w₀ :=
    hF.adaptedGraph_hasFocalExpansion old A bW (Module.finBasis ℝ V)
      hg hsub hG hD hΨ hODE w₀ (fun t ht ↦ hmap (w₀, t) ht)
      (fun t ht ↦ (hphase (w₀, t) ht rfl).1)
      (fun t ht ↦ (hphase (w₀, t) ht rfl).2)
  refine ⟨bW, e, g, D, he, hsource, hB, hg, hsub, hG, hD, hcenter, htarget, hΨ,
    fun q hq ↦ ⟨(hJacobi q hq).1, hmap q hq, hODE q hq⟩, hphase, hfocal, ?_⟩
  intro K hK hKD
  exact hfocal.finite_singular_times hK hKD

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
