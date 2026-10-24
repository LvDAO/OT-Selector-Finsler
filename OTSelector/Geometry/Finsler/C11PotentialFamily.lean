import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11EikonalSeed
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Jacobi.CompletePotentialJet
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Symplectic.PotentialConormal
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11PotentialFamily

* **Conditions:** The actual calibrated contact core with a C1,1 extension and its original derivative matching.
* **Objects:** At almost every original core point, a smooth matching potential-level family with the genuine normalized initial momentum jet.
* **Proof detail:** Apply rough eikonal seed construction, realize the actual second jet by a smooth representative and construct its own normalized complete level family.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): Records phase immersion, without asserting position rank or an ambient second derivative of the original nonsmooth potential.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11PotentialFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11PotentialFamily`; the selected original proof blocks follow. -/
section

/-!
# Actual complete potential-level families at almost every C1,1 contact point

The original calibrated core constructs density-one rough eikonal seeds. The existing
complete potential-level producer then gives a smooth representative matching the
original value and first derivative and the actual C1,1 extension Hessian. Its own
normalized complete family retains the true initial momentum jet. Phase immersion
is recorded as such; no position-projection rank or ambient second derivative of the
original nonsmooth potential is asserted.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual C1,1 second jet on an original contact core, together with a constructed
smooth representative and its own complete normalized potential-level family. The
original potential has an actual first derivative and a within-core derivative of
that covector; the ambient Hessian belongs to the actual extension G. -/
def HasC11PotentialFamilyAt (F : ContinuousFinslerNorm E M) (m : Measure E)
    (old : M) (t₀ : ℝ) (u : M → ℝ) (G : E → ℝ) (K : Set E) (x : E) : Prop :=
  x ∈ K ∧
  Tendsto (fun r ↦ m (K ∩ closedBall x r) / m (closedBall x r))
    (𝓝[>] 0) (𝓝 1) ∧
  HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x ∧
  HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
  HasFDerivWithinAt (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm))
    (fderiv ℝ (fderiv ℝ G) x) K x ∧
  ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
    (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old) ∧
    e.source ⊆ chartEnergyDomain old ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
    (x, fderiv ℝ G x) ∈ e.target ∧
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧
      P x = u ((extChartAt 𝓘(ℝ, E) old).symm x) ∧
      HasFDerivAt P (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x) x ∧
      HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x ∧
      fderiv ℝ P x = fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x ∧
      fderiv ℝ (fderiv ℝ P) x = fderiv ℝ (fderiv ℝ G) x ∧
      let p := fderiv ℝ G x
      Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
      ∃ (B₀ B : Set p.ker) (σ v : p.ker → E) (a : p.ker → ℝ)
          (Γ : p.ker → ℝ → M) (U : Set E),
        IsOpen B₀ ∧ IsOpen B ∧ (0 : p.ker) ∈ B ∧ B ⊆ B₀ ∧ IsOpen U ∧ x ∈ U ∧
        ContDiffOn ℝ ∞ σ B₀ ∧ σ 0 = x ∧ (∀ w ∈ B₀, P (σ w) = P x) ∧
        HasFDerivAt σ p.ker.subtypeL 0 ∧ InjOn σ B₀ ∧
        σ '' B₀ = U ∩ {y | P y = P x} ∧
        ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧
        v 0 = (e.symm (x, fderiv ℝ G x)).2 ∧ a 0 = 1 ∧
        (∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain old ∧ 0 < a w ∧
          F.chartEnergy old (σ w, v w) = (1 / 2 : ℝ) ∧
          fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • fderiv ℝ P (σ w)) ∧
        (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
        (∀ w ∈ B, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σ w, v w)) ∧
        (∀ w ∈ B, F.chartMomentumFamily old Γ (w, t₀) =
          potentialConormalState P σ a w) ∧
        ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
          (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
        (∀ w ∈ B, ∀ t : ℝ,
          F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ)) ∧
        (∀ (chart : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) chart).source →
          Function.Injective (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) 0)) ∧
        (∀ w ∈ B, ∀ (chart : M) (t : ℝ),
          Γ w t ∈ (extChartAt 𝓘(ℝ, E) chart).source →
          ∀ ξ η : p.ker, canonicalPhasePairing
            (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) w ξ)
            (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) w η) = 0) ∧
        fderiv ℝ a 0 = 0 ∧
        HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, t₀))
          (p.ker.subtypeL.prod ((fderiv ℝ (fderiv ℝ G) x).comp p.ker.subtypeL)) 0

namespace IsSmoothStronglyConvex

variable [T2Space M] [PreconnectedSpace M]

/-- An actual calibrated C1,1 core constructs complete smooth potential-level families
at almost every point of every original measure absolutely continuous with respect to
Haar measure. The first jet matches the original potential and the second jet is the
actual extension Hessian. No branch, density, second derivative or family is supplied. -/
theorem ae_complete_potentialFamily_of_calibrated_C11_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instC11PotentialFamilyLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hinterior : let _instC11PotentialFamilyInterior : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm K (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ x ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x) :
    ∀ᵐ x ∂ν.restrict K, F.HasC11PotentialFamilyAt m old t₀ u G K x := by
  filter_upwards [hF.ae_complete_eikonal_seed_data_of_calibrated_C11_core
    hcomplete old hν hK hKt hu hinterior hG hLip hactual] with x hx
  obtain ⟨hxK, hdensity, hsecond, hwithin, e, V, he, hsub, heG, _, hxV,
    htarget, hdensityV, henergy⟩ := hx
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Eventually.of_forall fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt
  have hp := htarget x hxV
  obtain ⟨P, hP, hPx, hP₁, hP₂, hactual₁, hactual₂, hfamily⟩ :=
    hF.exists_complete_potentialLevelFamily_of_rough_secondJet m hcomplete old t₀
      he hsub heG hdensityV ⟨hxK, hxV⟩ hfirst hsecond hp henergy
  have hmatch : fderiv ℝ G x =
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x := (hactual x hxK).fderiv.symm
  exact ⟨hxK, hdensity, hactual x hxK, hsecond, hwithin, e, he, hsub, heG, hp, P, hP,
    hPx.trans (hval hxK), hP₁.congr_fderiv hmatch, hP₂, hactual₁.trans hmatch,
    hactual₂, hfamily⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
