import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialFamilyJetMatching
import OTSelector.Geometry.Symplectic.PotentialConormal
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11MatchedFamily

* **Conditions:** The constructed actual C1,1 potential-level good-point data and its actual normalized initial phase jet.
* **Objects:** A matched rough trajectory family with the same central complete curve and the actual within-core derivative of that selected smooth family.
* **Proof detail:** Retain the original smooth level chart/family, construct rough initial covector trajectories and apply the explicit same-family jet matching.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): No density or unique-differentiability premise is imposed on the inverse image of the contact core inside its level chart.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11MatchedFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11MatchedFamily`; the selected original proof blocks follow. -/
section

/-!
# Original rough trajectories matched to their smooth potential-level family

At almost every original calibrated contact point, retain the constructed smooth level
chart and complete normal family. The original potential covectors construct rough
trajectories whose central curve and within-core parameter derivatives agree with that
very family at every chart-legal time. No density or unique-differentiability assertion
is made for the inverse image of the contact core in the level chart.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- A smooth level family with its actual phase variations, together with rough
trajectories initialized by the original potential covector and sharing those variations
within the allowed contact labels. The Hessian belongs to the C1,1 extension. -/
def HasC11MatchedFamilyAt (F : ContinuousFinslerNorm E M) (old : M) (t₀ : ℝ)
    (u : M → ℝ) (G : E → ℝ) (K : Set E) (x : E) : Prop :=
  let p := fderiv ℝ G x
  Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
  ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))) (P : E → ℝ),
    (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old) ∧
    e.source ⊆ chartEnergyDomain old ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
    ContDiff ℝ ∞ P ∧ P x = u ((extChartAt 𝓘(ℝ, E) old).symm x) ∧
    HasFDerivAt P p x ∧ HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x ∧
    ∃ (B : Set p.ker) (σ : p.ker → E) (Γ Ψ : p.ker → ℝ → M),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧ ContDiffOn ℝ ∞ σ B ∧ σ 0 = x ∧
      (∀ w ∈ B, P (σ w) = P x) ∧ HasFDerivAt σ p.ker.subtypeL 0 ∧ InjOn σ B ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ)) ∧
      (∀ (chart : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) chart).source →
        Function.Injective (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) 0)) ∧
      (∀ w ∈ B, ∀ (chart : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) chart).source →
        ∀ ξ η : p.ker, canonicalPhasePairing
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) w ξ)
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) w η) = 0) ∧
      Ψ 0 = Γ 0 ∧
      (∀ᶠ w in 𝓝[σ ⁻¹' K] 0,
        (σ w, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (σ w)) ∈ e.target ∧
        F.IsEulerLagrangeOn (Ψ w) univ ∧
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Ψ w) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
              (e.symm (σ w, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (σ w)))) ∧
      ∀ (chart : M) (r : ℝ), Γ 0 r ∈ (extChartAt 𝓘(ℝ, E) chart).source →
        HasFDerivWithinAt (fun w ↦ F.chartMomentumFamily chart Ψ (w, r))
          (fderiv ℝ (fun w ↦ F.chartMomentumFamily chart Γ (w, r)) 0) (σ ⁻¹' K) 0

namespace IsSmoothStronglyConvex
variable [T2Space M] [PreconnectedSpace M]

omit [BorelSpace E] in
/-- The already constructed level family can be retained while matching the original
rough covectors to its actual parameter derivatives at every legal time. -/
theorem matchedFamily_of_C11PotentialFamily (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {m : Measure E} {old : M} {t₀ : ℝ} {u : M → ℝ} {G : E → ℝ}
    {K : Set E} {x : E} (hx : F.HasC11PotentialFamilyAt m old t₀ u G K x) :
    F.HasC11MatchedFamilyAt old t₀ u G K x := by
  obtain ⟨hxK, _, hfirst, _, hwithin, e, he, hsub, hInv, hp, P, hP, hPval,
    hP₁, hP₂, _, _, hdim, B₀, B, σ, v, a, Γ, U, _, hB, h0, hBB₀, _, _,
    hσ, hσ0, hlevel, hσD, hσinj, _, hv, _, hv0, _, hstate, hEL, hinit,
    _, hΓ, henergy, hinj, hiso, _, hjet⟩ := hx
  have hseed0 : (σ 0, v 0) = e.symm (x, fderiv ℝ G x) := by
    rw [hσ0, hv0]
    exact Prod.ext (parametricLegendre_inverse_components he hp).1.symm rfl
  obtain ⟨Ψ, hcenter, hrough, hmatch⟩ :=
    hF.exists_complete_family_matching_potentialLevel_jet hcomplete old t₀ hxK
      hfirst hwithin he hsub hInv hp hB h0 hσ0 hσD
      (hv.continuousOn.continuousAt (hB.mem_nhds h0)) hseed0
      (fun w hw ↦ (hstate w hw).1) hEL hinit hjet
  exact ⟨hdim, e, P, he, hsub, hInv, hP, hPval,
    hP₁.congr_fderiv hfirst.fderiv, hP₂, B, σ, Γ, Ψ, hB, h0,
    hσ.mono hBB₀, hσ0, (fun w hw ↦ hlevel w (hBB₀ hw)), hσD,
    hσinj.mono hBB₀, hEL, hΓ, henergy, hinj, hiso, hcenter, hrough, hmatch⟩

/-- Almost every point of an original calibrated C1,1 core admits this matching with
its smooth potential-level family, for every coordinate law absolutely continuous
with respect to Haar measure. No branch, family or matching premise is supplied. -/
theorem ae_matchedFamily_of_calibrated_C11_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instMatchedFamilyLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hinterior : let _instMatchedFamilyInterior : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm K (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ x ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x) :
    ∀ᵐ x ∂ν.restrict K, F.HasC11MatchedFamilyAt old t₀ u G K x := by
  filter_upwards [hF.ae_complete_potentialFamily_of_calibrated_C11_core hcomplete old t₀
    hν hK hKt hu hinterior hG hLip hval hactual] with x hx
  exact hF.matchedFamily_of_C11PotentialFamily hcomplete hx

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
