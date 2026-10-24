import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialCompleteFamily
import OTSelector.Geometry.Manifold.SmoothLevelChart
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompletePotentialLevel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompletePotentialLevel`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CompletePotentialLevel

* **Conditions:** A smooth potential with prescribed actual nonzero central Finsler momentum and a complete original length metric.
* **Objects:** An automatically constructed kernel level chart and a complete constant-energy potential family with correct dimension, immersion, rank and isotropy.
* **Proof detail:** Nonzero momentum gives a nonzero potential differential; apply the local level-chart theorem and then the same normalized complete-family construction.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Complete intrinsic families from an automatically constructed potential level

The original nonzero Finsler velocity forces its momentum to be nonzero. A smooth
potential with that actual differential therefore constructs its own level chart,
parameterized by the kernel of the differential. The parameter dimension and immersion
are conclusions. The same normalized complete family retains constant energy, full phase
rank and zero canonical pairing, without a supplied level chart or coordinate splitting.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original smooth potential data construct their own codimension-one level chart and
one complete Finsler family with actual energy, phase rank and pairing conclusions. -/
theorem exists_complete_potentialLevelFamily (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {f : E → ℝ} {Ω : Set E} {y₀ v₀ : E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hy₀ : y₀ ∈ Ω)
    (hz : (y₀, v₀) ∈ chartEnergyDomain initial)
    (hmatch : fderiv ℝ f y₀ = fiberLegendre (F.chartEnergy initial) (y₀, v₀))
    (t₀ : ℝ) :
    let p := fderiv ℝ f y₀
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
    ∃ (B₀ B : Set p.ker) (σ v : p.ker → E) (a : p.ker → ℝ)
      (Γ : p.ker → ℝ → M) (U : Set E),
      IsOpen B₀ ∧ IsOpen B ∧ (0 : p.ker) ∈ B ∧ B ⊆ B₀ ∧
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ σ B₀ ∧ σ 0 = y₀ ∧ MapsTo σ B₀ Ω ∧
      (∀ w ∈ B₀, f (σ w) = f y₀) ∧ HasFDerivAt σ p.ker.subtypeL 0 ∧
      InjOn σ B₀ ∧ σ '' B₀ = U ∩ {x | f x = f y₀} ∧
      ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧ v 0 = v₀ ∧ a 0 = 1 ∧
      (∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain initial ∧ 0 < a w) ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      (∀ w ∈ B, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σ w, v w)) ∧
      (∀ w ∈ B, F.chartMomentumFamily initial Γ (w, t₀) =
        potentialConormalState f σ a w) ∧
      ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) =
          F.chartEnergy initial (y₀, v₀)) ∧
      (∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        Function.Injective
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) 0)) ∧
      ∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        ∀ ξ η : p.ker, canonicalPhasePairing
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w ξ)
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w η) = 0 := by
  have hp : fderiv ℝ f y₀ ≠ 0 := by
    intro hzero
    have he := hF.chartEnergy_euler initial hz
    rw [← hmatch, hzero, _root_.zero_apply] at he
    have hpos := F.chartEnergy_pos initial hz
    linarith
  obtain ⟨B₀, σ, U, hB₀, h0, hσ, hσ0, hσΩ, hlevel, hD, himm, hinj,
    hU, hyU, hUΩ, himage, hdim⟩ := exists_smooth_levelChart hΩ hf hy₀ hp
  have hz' : (σ 0, v₀) ∈ chartEnergyDomain initial := by simpa only [hσ0] using hz
  have hm' : fderiv ℝ f (σ 0) = fiberLegendre (F.chartEnergy initial) (σ 0, v₀) := by
    simpa only [hσ0] using hmatch
  obtain ⟨B, v, a, Γ, hB, h0B, hBB₀, hv, ha, hv₀, ha₀, hd, hEL, hi, hm, hG,
    henergy, hrank, hpair⟩ :=
    hF.exists_complete_potentialFamily hcomplete initial hΩ hf hB₀ h0 hσ hσΩ hz' hm' t₀
  refine ⟨hdim, B₀, B, σ, v, a, Γ, U, hB₀, hB, h0B, hBB₀, hU, hyU, hUΩ,
    hσ, hσ0, hσΩ, hlevel, hD, hinj, himage, hv, ha, hv₀, ha₀,
    (fun w hw ↦ ⟨(hd w hw).1, (hd w hw).2.1⟩), hEL, hi, hm, hG, ?_,
    hrank 0 h0B himm, ?_⟩
  · simpa only [hσ0] using henergy
  · intro w hw old t hx ξ η
    apply hpair w hw (f y₀) _ old t hx ξ η
    filter_upwards [hB₀.mem_nhds (hBB₀ hw)] with b hb
    exact hlevel b hb

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
