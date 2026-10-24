import OTSelector.Geometry.FinslerSmoothPhaseJetJacobi
import OTSelector.Geometry.FinslerComparisonGraphDomain

/-!
# One selected endpoint graph and its regular physical source

The record retains one actual graph inverse, Legendre inverse and phase domain,
including the original velocity's membership in the Legendre source. The same
chosen data carry a regular physical source neighborhood and its positive clock.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A single selected graph Jacobi chart and its genuine regular physical domain. -/
structure EndpointGraphData (F : ContinuousFinslerNorm E M)
    (A : E ≃L[ℝ] (ℝ × V)) (Γ : W → ℝ → M) (B : Set W)
    (w : W) (old : M) (t : ℝ) where
  e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)
  g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))
  D : Set (W × ℝ)
  raw :
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
    let L := F.adaptedGraphLagrangian old A
    (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
    (w, t) ∈ e.source ∧ e.source ⊆ B ×ˢ univ ∧
    (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
    g.source ⊆ (A.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ ∧
    ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧
    curveGraphCoordinateMap γ (w, t) ∈ D ∧ D ⊆ e.target ∧
    ContDiffOn ℝ 2 (F.adaptedGraphPhase old A γ e) D ∧
    (∀ q ∈ D,
      let P := F.adaptedGraphPhase old A γ e
      let Aₛ := GraphHamiltonian.blockA L g q.2 (P q)
      let Bₛ := GraphHamiltonian.blockB L g q.2 (P q)
      let Cₛ := GraphHamiltonian.blockC L g q.2 (P q)
      graphVelocityPhase (fun p ↦ (curveGraphPosition γ e p).2) q ∈ g.source ∧
      HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2 ∧
      (∀ ξ : W,
        let Z := fun s ↦ fderiv ℝ (fun z ↦ P (z, s)) q.1 ξ
        HasDerivAt (fun s ↦ (Z s).1) (Bₛ (Z q.2).1 + Cₛ (Z q.2).2) q.2 ∧
        HasDerivAt (fun s ↦ (Z s).2) (-Aₛ (Z q.2).1 - (Z q.2).2.comp Bₛ) q.2) ∧
      (∀ u v, Aₛ u v = Aₛ v u) ∧
      (∀ p r : V →L[ℝ] ℝ, r (Cₛ p) = p (Cₛ r)) ∧
      Cₛ = ContinuousLinearMap.inverse
        (GraphLegendre.verticalHessian L (g.symm ((q.2, (P q).1), (P q).2))) ∧
      ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (Cₛ p)) ∧
    ∀ q ∈ D, q.1 = w →
      let R := fderiv ℝ (fun z ↦ F.adaptedGraphPhase old A γ e (z, q.2)) q.1
      Function.Injective R ∧ ∀ ξ η : W, canonicalPhasePairing (R ξ) (R η) = 0
  U : Set (W × ℝ)
  open_U : IsOpen U
  anchor_U : (w, t) ∈ U
  source_U : U ⊆ e.source
  mapsTo_phase : MapsTo e U D
  position_C2 : ContDiffOn ℝ 2
    (fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))) U
  regular : ∀ q ∈ U,
    0 < (fderiv ℝ (fun p : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ p.1 p.2))) q
      (0, 1)).1 ∧ DifferentiableAt ℝ e.symm (e q)
  curve_source : ∀ q ∈ U, Γ q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) old).source

namespace SmoothPhaseJetComparison

variable {F : ContinuousFinslerNorm E M}

/-- The actual comparison chooses one raw graph chart and preserves it while
constructing a regular source inside any prescribed open physical neighborhood. -/
theorem exists_endpointGraphData
    {initial : M} {t₀ : ℝ} {w : W} {z₀ : E × (E →L[ℝ] ℝ)}
    {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q)
    (hF : F.IsSmoothStronglyConvex) (old : M) (A : E ≃L[ℝ] (ℝ × V)) (t : ℝ)
    (hx : C.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hpositive : 0 < (A (deriv (extChartAt 𝓘(ℝ, E) old ∘ C.curve w) t)).1)
    {N : Set (W × ℝ)} (hN : IsOpen N) (hanchor : (w, t) ∈ N) :
    ∃ G : EndpointGraphData F A C.curve C.labels w old t, G.U ⊆ N := by
  have hchart := hF.hasAdaptedGraphJacobiChart_of_family C.open_labels C.complete
    C.tangent_C2 C.energy_eq C.anchor_mem C.phase_rank C.phase_isotropic C.normal
    old A t hx hpositive
  obtain ⟨e, g, D, he, hs, hB, hg, hgsource, hgi, hD, hcenter, hDt, hPC2, hJacobi,
    hphase⟩ := hchart
  obtain ⟨U, hU, hwU, hUs, hUD, hC2, hregular⟩ :=
    C.exists_regular_graph_source hF old A t hx hpositive he hs hD hcenter
  have hposition : ContinuousOn (fun q : W × ℝ ↦ C.curve q.1 q.2) U :=
    (contMDiffOn_positionFamily_of_tangentFamily C.tangent_C2).continuousOn.mono
      (hUs.trans hB)
  let U' := (U ∩ (fun q : W × ℝ ↦ C.curve q.1 q.2) ⁻¹'
    (extChartAt 𝓘(ℝ, E) old).source) ∩ N
  have hU' : IsOpen U' :=
    (hposition.isOpen_inter_preimage hU (isOpen_extChartAt_source old)).inter hN
  refine ⟨{
    e := e
    g := g
    D := D
    raw := ⟨he, hs, hB, hg, hgsource, hgi, hD, hcenter, hDt, hPC2, hJacobi, hphase⟩
    U := U'
    open_U := hU'
    anchor_U := ⟨⟨hwU, hx⟩, hanchor⟩
    source_U := fun q hq ↦ hUs hq.1.1
    mapsTo_phase := fun q hq ↦ hUD hq.1.1
    position_C2 := hC2.mono (fun q hq ↦ hq.1.1)
    regular := fun q hq ↦ hregular q hq.1.1
    curve_source := fun q hq ↦ hq.1.2 }, inter_subset_right⟩

end SmoothPhaseJetComparison
end OTSelector.Geometry.ContinuousFinslerNorm
