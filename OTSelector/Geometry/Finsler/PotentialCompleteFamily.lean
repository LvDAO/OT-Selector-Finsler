import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.PotentialNormalData
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompleteMomentumRank
import OTSelector.Geometry.Finsler.CompletePairing
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialCompleteFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialCompleteFamily`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PotentialCompleteFamily

* **Conditions:** A smooth potential differential along an actual smooth position seed, matched to the central original momentum and normalized by its Finsler energy.
* **Objects:** One complete intrinsic potential family with exact scaled-df initial momentum, joint C2 tangent dependence, phase rank and level-set isotropy.
* **Proof detail:** Normalize the actual potential covector, compose one complete flow with that seed, and propagate seed immersion/isotropy using full phase rank and canonical conservation.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Complete intrinsic families from the actual potential differential

Normalize the actual differential of a smooth potential by the original Finsler energy,
then use one complete intrinsic family. Its initial momentum is exactly that scaled
differential; its actual tangent family is jointly C2 for all times. Wherever the position
seed is immersed, its actual momentum variation retains full phase rank in every chart.
An actual potential level set gives zero canonical pairing throughout the complete family.
-/

open Set Filter Function Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- A true potential differential produces a complete family with exact initial data,
constant energy, full phase rank wherever the initial position is immersed, and zero
canonical pairing at every time for actual level-set parameter directions. -/
theorem exists_complete_potentialFamily (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {f : E → ℝ} {σ : W → E} {Ω : Set E} {V : Set W} {w₀ : W}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hV : IsOpen V) (hw₀ : w₀ ∈ V) (hσ : ContDiffOn ℝ ∞ σ V) (hσΩ : MapsTo σ V Ω)
    {v₀ : E} (hz : (σ w₀, v₀) ∈ chartEnergyDomain initial)
    (hmatch : fderiv ℝ f (σ w₀) = fiberLegendre (F.chartEnergy initial) (σ w₀, v₀))
    (t₀ : ℝ) :
    ∃ (U : Set W) (v : W → E) (a : W → ℝ) (Γ : W → ℝ → M),
      IsOpen U ∧ w₀ ∈ U ∧ U ⊆ V ∧
      ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧ v w₀ = v₀ ∧ a w₀ = 1 ∧
      (∀ w ∈ U, (σ w, v w) ∈ chartEnergyDomain initial ∧ 0 < a w ∧
        F.chartEnergy initial (σ w, v w) = F.chartEnergy initial (σ w₀, v₀) ∧
        fiberLegendre (F.chartEnergy initial) (σ w, v w) = a w • fderiv ℝ f (σ w)) ∧
      (∀ w ∈ U, F.IsEulerLagrangeOn (Γ w) univ) ∧
      (∀ w ∈ U, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σ w, v w)) ∧
      (∀ w ∈ U, F.chartMomentumFamily initial Γ (w, t₀) =
        potentialConormalState f σ a w) ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (U ×ˢ univ) ∧
      (∀ w ∈ U, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) =
          F.chartEnergy initial (σ w₀, v₀)) ∧
      (∀ w ∈ U, Function.Injective (fderiv ℝ σ w) → ∀ (old : M) (t : ℝ),
        Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        Function.Injective (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w)) ∧
      ∀ w ∈ U, ∀ c : ℝ, (fun b ↦ f (σ b)) =ᶠ[𝓝 w] (fun _ ↦ c) →
        ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source → ∀ ξ η : W,
          canonicalPhasePairing
            (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w ξ)
            (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w η) = 0 := by
  obtain ⟨e, U, v, a, he, hzs, hsub, hInv, hU, hwU, hUV, hv, ha, hv₀, ha₀, hd⟩ :=
    hF.exists_constantEnergy_potentialNormalData initial hΩ hf hV hw₀ hσ hσΩ hz hmatch
  obtain ⟨Φ, hEL, hi, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial t₀
  let seed : W → E × E := fun w ↦ (σ w, v w)
  let Γ : W → ℝ → M := fun w ↦ Φ (seed w)
  have hs : ContDiffOn ℝ ∞ seed U := (hσ.mono hUV).prodMk hv
  have hm : MapsTo seed U (chartEnergyDomain initial) := fun w hw ↦ hsub (hd w hw).1
  have hΓ (w : W) (hw : w ∈ U) : F.IsEulerLagrangeOn (Γ w) univ := hEL _ (hm hw)
  have hΓi (w : W) (hw : w ∈ U) :
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (seed w) := hi _ (hm hw)
  have hS : ContDiffOn ℝ 2 (fun q : W × ℝ ↦ (seed q.1, q.2)) (U ×ˢ univ) :=
    ((hs.of_le (by simp)).comp contDiffOn_fst (fun q hq ↦ hq.1)).prodMk contDiffOn_snd
  have hΓG := hG.comp hS.contMDiffOn (fun q hq ↦ ⟨hm hq.1, mem_univ _⟩)
  refine ⟨U, v, a, Γ, hU, hwU, hUV, hv, ha, hv₀, ha₀,
    ?_, hΓ, hΓi, ?_, hΓG, ?_, ?_, ?_⟩
  · intro w hw
    exact ⟨hm hw, (hd w hw).2.1, (hd w hw).2.2.1, (hd w hw).2.2.2.1⟩
  · intro w hw
    change eulerLagrangePhaseLift _ _ _ = _
    rw [hF.chartMomentum_of_tangent_eq (hΓ w hw t₀ (mem_univ _)) initial (hm hw) (hΓi w hw)]
    exact Prod.ext rfl (hd w hw).2.2.2.1
  · intro w hw t
    calc
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) =
          F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩) := by
        unfold ContinuousFinslerNorm.energy
        rw [hF.speed_eq_of_isEulerLagrangeOn (hΓ w hw) isPreconnected_univ
          (mem_univ t) (mem_univ t₀)]
      _ = F.chartEnergy initial (σ w, v w) := congrArg F.energy (hΓi w hw)
      _ = F.chartEnergy initial (σ w₀, v₀) := (hd w hw).2.2.1
  · intro w hw himm old t hx
    have hsd := (hs.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
    have hσd := ((hσ.mono hUV).contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
    have hvd := (hv.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
    have hinj : Function.Injective (fderiv ℝ seed w) := by
      rw [(hσd.hasFDerivAt.prodMk hvd.hasFDerivAt).fderiv]
      intro u u' huu'
      exact himm (congrArg Prod.fst huu')
    exact hF.injective_fderiv_seeded_complete_chartMomentumFamily
      hcomplete initial t₀ hEL hi hG hsd hinj (hm hw) old t hx

  · intro w hw c hlevel old t hx ξ η
    rw [hF.chartMomentumFamily_parameter_pairing_eq_initial
      hU hΓ hΓG initial t₀ hm hΓi hw old t hx ξ η]
    have heq : parametricLegendre (F.chartEnergy initial) ∘ seed =ᶠ[𝓝 w]
        potentialConormalState f σ a := by
      filter_upwards [hU.mem_nhds hw] with b hb
      exact Prod.ext rfl (hd b hb).2.2.2.1
    rw [heq.fderiv_eq]
    have hfd := (hf.contDiffAt (hΩ.mem_nhds (hσΩ (hUV hw)))).of_le (by simp :
      (2 : ℕ∞ω) ≤ ∞)
    have hσd := (hσ.contDiffAt (hV.mem_nhds (hUV hw))).differentiableAt (by simp)
    have had := (ha.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
    rw [potentialConormalState_fderiv_pairing hfd hσd had]
    have hz' := fderiv_comp_eq_zero_of_eventually_constant
      (hfd.differentiableAt (by norm_num)) hσd hlevel
    have hξ := congrArg (fun D : W →L[ℝ] ℝ ↦ D ξ) hz'
    have hη := congrArg (fun D : W →L[ℝ] ℝ ↦ D η) hz'
    simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply] at hξ hη
    rw [hξ, hη]
    ring

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
