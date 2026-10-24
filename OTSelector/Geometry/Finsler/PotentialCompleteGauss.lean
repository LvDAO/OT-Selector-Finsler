import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteGauss
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompletePotentialLevel
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialCompleteGauss.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialCompleteGauss`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PotentialCompleteGauss

* **Conditions:** The same complete constant-energy potential family with exact initial momentum a·df and an actual level-set germ.
* **Objects:** All-time momentum normality in every legal chart, with an existence interface constructing the entire normal potential-level family.
* **Proof detail:** Read the actual initial position derivative from the prescribed momentum state, annihilate it by the level identity and apply global Gauss conservation.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Global Gauss normality for actual potential level data

The normalized complete potential families already have one common intrinsic energy
and the exact initial momentum a df. The actual initial position derivative is read
from that same momentum identity. A level-set germ annihilates df, so the all-time,
chart-independent Gauss conservation theorem gives normality for the same family.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

/-- The actual initial potential momentum of a constant-energy complete family makes
its level-parameter position variations normal at every time and in every legal chart. -/
theorem chartMomentumFamily_gauss_zero_of_potential_initial (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = C)
    (initial : M) (t₀ : ℝ) {f : E → ℝ} {σ : W → E} {a : W → ℝ}
    (hinit : ∀ w ∈ B, F.chartMomentumFamily initial Γ (w, t₀) =
      potentialConormalState f σ a w)
    {w₀ : W} (hw : w₀ ∈ B)
    (hx₀ : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source)
    (hf : DifferentiableAt ℝ f (σ w₀)) (hσ : DifferentiableAt ℝ σ w₀)
    {c : ℝ} (hlevel : (fun w ↦ f (σ w)) =ᶠ[𝓝 w₀] fun _ ↦ c)
    (old : M) (t : ℝ) (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) (ξ : W) :
    (F.chartMomentumFamily old Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) = 0 := by
  rw [hF.chartMomentumFamily_gauss_eq hB hEL hG henergy hw initial old t₀ t hx₀ hx ξ]
  have heq : (fun w ↦ extChartAt 𝓘(ℝ, E) initial (Γ w t₀)) =ᶠ[𝓝 w₀] σ := by
    filter_upwards [hB.mem_nhds hw] with w hw'
    exact congrArg Prod.fst (hinit w hw')
  rw [heq.fderiv_eq, hinit w₀ hw]
  exact potentialConormalState_momentum_eq_zero hf hσ hlevel ξ

/-- A smooth potential matching one actual nonzero initial momentum constructs its own
level chart and a complete family with constant energy, phase rank, isotropy and Gauss
normality. All conclusions refer to that same intrinsic family. -/
theorem exists_complete_normalPotentialLevelFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {f : E → ℝ} {Ω : Set E} {y₀ v₀ : E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hy₀ : y₀ ∈ Ω)
    (hz : (y₀, v₀) ∈ chartEnergyDomain initial)
    (hmatch : fderiv ℝ f y₀ = fiberLegendre (F.chartEnergy initial) (y₀, v₀))
    (t₀ : ℝ) :
    let p := fderiv ℝ f y₀
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
    ∃ (B : Set p.ker) (σ : p.ker → E) (a : p.ker → ℝ) (Γ : p.ker → ℝ → M),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧
      ContDiffOn ℝ ∞ σ B ∧ σ 0 = y₀ ∧ MapsTo σ B Ω ∧
      (∀ w ∈ B, f (σ w) = f y₀) ∧ HasFDerivAt σ p.ker.subtypeL 0 ∧
      ContDiffOn ℝ ∞ a B ∧ a 0 = 1 ∧ (∀ w ∈ B, 0 < a w) ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ 0) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (y₀, v₀) ∧
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
      (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        ∀ ξ η : p.ker, canonicalPhasePairing
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w ξ)
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w η) = 0) ∧
      ∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        ∀ ξ : p.ker, (F.chartMomentumFamily old Γ (w, t)).2
          (fderiv ℝ (fun b ↦ extChartAt 𝓘(ℝ, E) old (Γ b t)) w ξ) = 0 := by
  obtain ⟨hdim, B₀, B, σ, v, a, Γ, U, hB₀, hB, h0, hBB₀, hU, hyU, hUΩ,
    hσ, hσ0, hσΩ, hlevel, hD, hinj, himage, hv, ha, hv₀, ha₀, hdata,
    hEL, hi, hm, hG, henergy, hrank, hpair⟩ :=
    hF.exists_complete_potentialLevelFamily hcomplete initial hΩ hf hy₀ hz hmatch t₀
  refine ⟨hdim, B, σ, a, Γ, hB, h0, hσ.mono hBB₀, hσ0,
    hσΩ.mono_left hBB₀, (fun w hw ↦ hlevel w (hBB₀ hw)), hD, ha, ha₀,
    (fun w hw ↦ (hdata w hw).2), hEL, ?_, hm, hG, henergy, hrank, hpair, ?_⟩
  · simpa only [hσ0, hv₀] using hi 0 h0
  · intro w hw old t hx ξ
    have hb : Γ w t₀ = (extChartAt 𝓘(ℝ, E) initial).symm (σ w) := by
      have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hi w hw)
      rw [tangentChart_symm_eq initial (hdata w hw).1.1] at h
      exact h
    have hx₀ : Γ w t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
      rw [hb]
      exact (extChartAt 𝓘(ℝ, E) initial).map_target (hdata w hw).1.1
    apply hF.chartMomentumFamily_gauss_zero_of_potential_initial
      hB hEL hG henergy initial t₀ hm hw hx₀
      ((hf.contDiffAt (hΩ.mem_nhds (hσΩ (hBB₀ hw)))).differentiableAt (by simp))
      ((hσ.contDiffAt (hB₀.mem_nhds (hBB₀ hw))).differentiableAt (by simp))
      (c := f y₀) _ old t hx ξ
    filter_upwards [hB₀.mem_nhds (hBB₀ hw)] with b hb'
    exact hlevel b hb'

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
