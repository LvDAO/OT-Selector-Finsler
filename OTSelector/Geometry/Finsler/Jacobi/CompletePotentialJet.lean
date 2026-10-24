import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompletePotentialLevel
import OTSelector.Geometry.Finsler.EikonalJet
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.NormalizedSeedJet
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompletePotentialJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompletePotentialJet`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Jacobi.CompletePotentialJet

* **Conditions:** A density-one core on which the supplied local Hamiltonian of a differentiable rough covector equals 1/2, and its actual second jet at the base point.
* **Objects:** A smooth matching polynomial, its own kernel level chart and one complete normalized potential family whose actual initial momentum has the original rough first jet.
* **Proof detail:** Realize the symmetric one-point jet by a quadratic polynomial, differentiate the density-one Hamiltonian identity to zero and show the already chosen positive normalization has zero derivative.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): A derived rough-jet matching construction related to the manuscript eikonal-jet argument. This entry preserves the polynomial/family construction as project work rather than attributing it verbatim to a classical source.
-/

/-!
# The actual complete potential-level family of a rough eikonal jet

Construct the smooth polynomial, its own level chart, and the original normalized
potential family. Recover its normal data from that same family's actual initial
tangent, momentum, and conserved energy. The rough density-one identity then forces
the already constructed scale to have zero derivative, giving the actual initial
momentum the original rough first jet. No second family or scale is substituted.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
  (μ : Measure E) [IsAddHaarMeasure μ]

include hF

/-- A genuine rough eikonal second jet constructs its own smooth potential level and
complete normal family. The same scale and family have zero scale derivative and the
unscaled rough initial-momentum jet. The original dimension, immersion, level image,
normality, constant energy, complete tangent regularity, phase rank and isotropy
conclusions are retained. No vanishing energy-graph or scale derivative is an input. -/
theorem exists_complete_potentialLevelFamily_of_rough_secondJet
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy initial))
    (hsub : e.source ⊆ chartEnergyDomain initial)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hsecond : HasFDerivAt f' H x) (hp : (x, f' x) ∈ e.target)
    (heq : ∀ y ∈ s,
      localHamiltonian (F.chartEnergy initial) e (y, f' y) = (1 / 2 : ℝ)) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = f x ∧
      HasFDerivAt P (f' x) x ∧ HasFDerivAt (fderiv ℝ P) H x ∧
      fderiv ℝ P x = fderiv ℝ f x ∧
      fderiv ℝ (fderiv ℝ P) x = fderiv ℝ (fderiv ℝ f) x ∧
      let p := f' x
      Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
      ∃ (B₀ B : Set p.ker) (σ v : p.ker → E) (a : p.ker → ℝ)
        (Γ : p.ker → ℝ → M) (U : Set E),
        IsOpen B₀ ∧ IsOpen B ∧ (0 : p.ker) ∈ B ∧ B ⊆ B₀ ∧ IsOpen U ∧ x ∈ U ∧
        ContDiffOn ℝ ∞ σ B₀ ∧ σ 0 = x ∧ (∀ w ∈ B₀, P (σ w) = P x) ∧
        HasFDerivAt σ p.ker.subtypeL 0 ∧ InjOn σ B₀ ∧
        σ '' B₀ = U ∩ {y | P y = P x} ∧
        ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧
        v 0 = (e.symm (x, f' x)).2 ∧ a 0 = 1 ∧
        (∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain initial ∧ 0 < a w ∧
          F.chartEnergy initial (σ w, v w) = (1 / 2 : ℝ) ∧
          fiberLegendre (F.chartEnergy initial) (σ w, v w) = a w • fderiv ℝ P (σ w)) ∧
        (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
        (∀ w ∈ B, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σ w, v w)) ∧
        (∀ w ∈ B, F.chartMomentumFamily initial Γ (w, t₀) =
          potentialConormalState P σ a w) ∧
        ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
          (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
        (∀ w ∈ B, ∀ t : ℝ,
          F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ)) ∧
        (∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
          Function.Injective (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) 0)) ∧
        (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
          ∀ ξ η : p.ker, canonicalPhasePairing
            (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w ξ)
            (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w η) = 0) ∧
        fderiv ℝ a 0 = 0 ∧
        HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ (w, t₀))
          (p.ker.subtypeL.prod (H.comp p.ker.subtypeL)) 0 := by
  obtain ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂, hzero, hn⟩ :=
    hF.exists_smooth_chartHamiltonian_normalized_secondJet μ initial he hsub hG
      hx hxs hfirst hsecond hp heq
  have hbase := (parametricLegendre_inverse_components he hp).1
  have hcenter : (x, (e.symm (x, f' x)).2) = e.symm (x, f' x) :=
    Prod.ext hbase.symm rfl
  have hz : (x, (e.symm (x, f' x)).2) ∈ chartEnergyDomain initial := by
    rw [hcenter]
    exact hsub (e.map_target hp)
  have hm : fderiv ℝ P x =
      fiberLegendre (F.chartEnergy initial) (x, (e.symm (x, f' x)).2) := by
    rw [hD.fderiv, hcenter]
    exact (parametricLegendre_inverse_components he hp).2.symm
  have henergy₀ : F.chartEnergy initial (x, (e.symm (x, f' x)).2) = (1 / 2 : ℝ) := by
    rw [hcenter, ← hF.localHamiltonian_chartEnergy_eq initial he hsub hp]
    exact heq x hxs
  have hlevelData := hF.exists_complete_potentialLevelFamily hcomplete initial
    isOpen_univ hP.contDiffOn (mem_univ x) hz hm t₀
  dsimp only at hlevelData
  rw [hD.fderiv] at hlevelData
  obtain ⟨hdim, B₀, B, σ, v, a, Γ, U, hB₀, hB, h0B, hBB₀, hU, hxU, hUΩ,
    hσ, hσ0, hσΩ, hlevel, hσD, hinj, himage, hv, ha, hv0, ha0, hd, hEL, hi, hmomentum,
    hΓ, henergy, hrank, hpair⟩ := hlevelData
  have hdata (w) (hw : w ∈ B) :
      F.chartEnergy initial (σ w, v w) = (1 / 2 : ℝ) ∧
      fiberLegendre (F.chartEnergy initial) (σ w, v w) = a w • fderiv ℝ P (σ w) := by
    constructor
    · calc
        F.chartEnergy initial (σ w, v w) =
            F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩) :=
          (congrArg F.energy (hi w hw)).symm
        _ = (1 / 2 : ℝ) := (henergy w hw t₀).trans henergy₀
    · have heqp := hmomentum w hw
      change eulerLagrangePhaseLift _ _ _ = _ at heqp
      rw [hF.chartMomentum_of_tangent_eq (hEL w hw t₀ (mem_univ _)) initial
        (hd w hw).1 (hi w hw)] at heqp
      exact congrArg Prod.snd heqp
  have hdataNear : ∀ᶠ w in 𝓝 (0 : (f' x).ker),
      F.chartEnergy initial (σ w, v w) = F.chartEnergy initial (σ 0, v 0) ∧
      fiberLegendre (F.chartEnergy initial) (σ w, v w) = a w • fderiv ℝ P (σ w) := by
    filter_upwards [hB.mem_nhds h0B] with w hw
    exact ⟨(hdata w hw).1.trans (hdata 0 h0B).1.symm, (hdata w hw).2⟩
  have hzs : (σ 0, v 0) ∈ e.source := by
    rw [hσ0, hv0, hcenter]
    exact e.map_target hp
  have hjet : HasFDerivAt (fun w ↦ localHamiltonian (F.chartEnergy initial) e
      (σ w, fderiv ℝ P (σ w))) (0 : (f' x).ker →L[ℝ] ℝ) 0 := by
    have hzero' : HasFDerivAt (fun y ↦ localHamiltonian (F.chartEnergy initial) e
        (y, fderiv ℝ P y)) (0 : E →L[ℝ] ℝ) (σ 0) := by rwa [hσ0]
    simpa only [Function.comp_apply, ContinuousLinearMap.zero_comp] using! hzero'.comp 0 hσD
  have hmomentumNear : (fun w ↦ F.chartMomentumFamily initial Γ (w, t₀)) =ᶠ[𝓝 0]
      potentialConormalState P σ a := by
    filter_upwards [hB.mem_nhds h0B] with w hw
    exact hmomentum w hw
  obtain ⟨haZero, hjetMomentum⟩ := hF.initialMomentum_firstJet_of_constantEnergy initial
    (hP.contDiffAt.of_le (by simp)) hσD.differentiableAt
    (hv.contDiffAt (hB.mem_nhds h0B)).continuousAt
    ((ha.contDiffAt (hB.mem_nhds h0B)).differentiableAt (by simp)) ha0
    he hsub hG hzs hdataNear hjet hmomentumNear
  rw [hσD.fderiv, hσ0, hD₂.fderiv] at hjetMomentum
  refine ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂, hdim,
    B₀, B, σ, v, a, Γ, U, hB₀, hB, h0B, hBB₀, hU, hxU,
    hσ, hσ0, hlevel, hσD, hinj, himage, hv, ha, hv0, ha0,
    (fun w hw ↦ ⟨(hd w hw).1, (hd w hw).2, (hdata w hw).1, (hdata w hw).2⟩),
    hEL, hi, hmomentum, hΓ, ?_, hrank, hpair, haZero, hjetMomentum⟩
  intro w hw t
  exact (henergy w hw t).trans henergy₀

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
