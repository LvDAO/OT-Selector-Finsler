import OTSelector.Geometry.Finsler.CompletePotentialJacobi
import OTSelector.Geometry.FinslerCompleteGraphFocal

/-!
# Actual focal charts of one complete potential-level family

The automatically constructed level has the spatial dimension. Matching finite bases
are chosen from that dimension equality, so the genuine position variation is square
without reparameterizing the family or supplying a basis. The same complete family has
regular crossings and exact inverse poles in each legal positive-clock graph chart.
-/

open Set Manifold Bundle Module
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {W V M : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace (ℝ × V) M] [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M}

/-- A true graph inverse of the given intrinsic family carries focal expansions in
matching finite bases. The original graph Legendre branch and actual ODE are retained. -/
def HasGraphFocalChart (F : ContinuousFinslerNorm (ℝ × V) M)
    (Γ : W → ℝ → M) (B : Set W) (w₀ : W) (old : M) (t₀ : ℝ) : Prop :=
  ∃ bW : Basis (Fin (Module.finrank ℝ V)) ℝ W,
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
      HasGraphFocalExpansion bW (Module.finBasis ℝ V) (F.chartGraphPhase old γ e) D w₀

namespace IsSmoothStronglyConvex

/-- Equal parameter and spatial dimensions construct the actual square variation basis;
the already constructed Jacobi chart then yields its own focal chart. -/
theorem hasGraphFocalChart_of_finrank (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} {w₀ : W} {old : M} {t₀ : ℝ}
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V)
    (hchart : F.HasGraphJacobiChart Γ B w₀ old t₀) :
    F.HasGraphFocalChart Γ B w₀ old t₀ := by
  let a : V ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let bW : Basis (Fin (Module.finrank ℝ V)) ℝ W :=
    (Module.finBasis ℝ V).map a.toLinearEquiv
  exact ⟨bW, hF.exists_completeGraph_focalChart bW (Module.finBasis ℝ V) hchart⟩

/-- One complete potential-level family has genuine focal expansions in each legal
positive-clock chart. Level dimension, bases, phase rank and crossing are all derived. -/
theorem exists_complete_potentialLevelFocalFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {f : (ℝ × V) → ℝ} {Ω : Set (ℝ × V)} {y₀ v₀ : ℝ × V}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hy₀ : y₀ ∈ Ω)
    (hz : (y₀, v₀) ∈ chartEnergyDomain initial)
    (hmatch : fderiv ℝ f y₀ = fiberLegendre (F.chartEnergy initial) (y₀, v₀))
    (t₀ : ℝ) :
    let p := fderiv ℝ f y₀
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ (ℝ × V) ∧
    ∃ (B : Set p.ker) (σ : p.ker → ℝ × V) (a : p.ker → ℝ) (Γ : p.ker → ℝ → M),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧
      ContDiffOn ℝ ∞ σ B ∧ σ 0 = y₀ ∧ MapsTo σ B Ω ∧
      (∀ w ∈ B, f (σ w) = f y₀) ∧ HasFDerivAt σ p.ker.subtypeL 0 ∧
      ContDiffOn ℝ ∞ a B ∧ a 0 = 1 ∧ (∀ w ∈ B, 0 < a w) ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ 0) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, ℝ × V).prod 𝓘(ℝ, ℝ × V))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, ℝ × V) M)).symm (y₀, v₀) ∧
      (∀ w ∈ B, F.chartMomentumFamily initial Γ (w, t₀) =
        potentialConormalState f σ a w) ∧
      ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, ℝ × V).prod 𝓘(ℝ, ℝ × V)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ w) ⟨t, (1 : ℝ)⟩) =
          F.chartEnergy initial (y₀, v₀)) ∧
      (∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        Function.Injective
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) 0)) ∧
      (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        ∀ ξ η : p.ker, canonicalPhasePairing
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w ξ)
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w η) = 0) ∧
      (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        ∀ ξ : p.ker, (F.chartMomentumFamily old Γ (w, t)).2
          (fderiv ℝ (fun b ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ b t)) w ξ) = 0) ∧
      ∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        0 < (deriv (extChartAt 𝓘(ℝ, ℝ × V) old ∘ Γ 0) t).1 →
        F.HasGraphFocalChart Γ B 0 old t := by
  obtain ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hi, hm, hG, henergy, hrank, hpair, hnormal, hcharts⟩ :=
    hF.exists_complete_potentialLevelJacobiFamily hcomplete initial hΩ hf hy₀ hz hmatch t₀
  refine ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hi, hm, hG, henergy, hrank, hpair, hnormal, ?_⟩
  intro old t hx hpositive
  apply hF.hasGraphFocalChart_of_finrank _ (hcharts old t hx hpositive)
  rw [Module.finrank_prod, Module.finrank_self] at hdim
  omega

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
