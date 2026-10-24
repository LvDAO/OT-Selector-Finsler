import Mathlib.Analysis.Normed.Module.Dual
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.TangentReadout
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompleteChartBox.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompleteChartBox`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CompleteChartBox

* **Conditions:** A jointly C2 actual intrinsic tangent family and a legal chart at a specified parameter/time point.
* **Objects:** A genuine local Legendre branch and a parameter/time box on which the actual momentum family and actual parameter derivative satisfy their respective ODEs.
* **Proof detail:** Shrink the continuous phase into one inverse target and use intrinsic Euler–Lagrange, Legendre injectivity and mixed differentiation.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual coordinate boxes along the same complete Finsler family

At any time and in any legal chart, joint regularity constructs a parameter-time box
inside one genuine Legendre inverse target. The original Hamiltonian equation and the
true parameter-variation equation hold throughout this box for the given intrinsic
family. No separately chosen local flow or inverse-branch compatibility is assumed.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

/-- The same actual intrinsic family supplies a genuine local Hamiltonian box and its
actual parameter-variation equation at every point of its full time domain. -/
theorem exists_chartMomentumFamily_box (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) (t₀ : ℝ)
    (hx : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))) (r : ℝ),
      let D := ball w₀ r ×ˢ Ioo (t₀ - r) (t₀ + r)
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old) ∧
      e.source ⊆ chartEnergyDomain old ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      0 < r ∧ ball w₀ r ⊆ B ∧
      (∀ q ∈ D, Γ q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) old).source) ∧
      ContDiffOn ℝ 2 (F.chartMomentumFamily old Γ) D ∧
      MapsTo (F.chartMomentumFamily old Γ) D e.target ∧
      ∀ q ∈ D,
        HasDerivAt (fun s ↦ F.chartMomentumFamily old Γ (q.1, s))
          (localHamiltonianVectorField (F.chartEnergy old) e
            (F.chartMomentumFamily old Γ q)) q.2 ∧
        ∀ ξ : W, HasDerivAt
          (fun s ↦ fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, s)) q.1 ξ)
          (fderiv ℝ (localHamiltonianVectorField (F.chartEnergy old) e)
            (F.chartMomentumFamily old Γ q)
            (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, q.2)) q.1 ξ)) q.2 := by
  let Ψ := F.chartMomentumFamily old Γ
  let D₀ := (B ×ˢ univ) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹'
    (extChartAt 𝓘(ℝ, E) old).source
  have hc : ContinuousOn (fun q : W × ℝ ↦ Γ q.1 q.2) (B ×ˢ univ) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn hG.continuousOn
  have hD₀ : IsOpen D₀ :=
    hc.isOpen_inter_preimage (hB.prod isOpen_univ) (isOpen_extChartAt_source old)
  have hΨ₀ : ContDiffOn ℝ 2 Ψ D₀ := hF.contDiffOn_chartMomentumFamily old
    (fun q hq ↦ hEL q.1 hq.1.1 q.2 (mem_univ _)) (hG.mono inter_subset_left)
    (fun _ hq ↦ hq.2)
  obtain ⟨_, hz⟩ := hF.chartTangent_of_isEulerLagrangeAt (hEL w₀ hw t₀ (mem_univ _)) old hx
  obtain ⟨e, he, _, hp, hsub, hi, _, hX, _⟩ := hF.exists_smooth_chartHamiltonian old hz
  let N := D₀ ∩ Ψ ⁻¹' e.target
  have hN : IsOpen N := hΨ₀.continuousOn.isOpen_inter_preimage hD₀ e.open_target
  have hq₀ : (w₀, t₀) ∈ N := ⟨⟨⟨hw, mem_univ _⟩, hx⟩, hp⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds hq₀)
  let D := ball w₀ r ×ˢ Ioo (t₀ - r) (t₀ + r)
  have hDN : D ⊆ N := by
    intro q hq
    apply hball
    rw [← ball_prod_same]
    exact ⟨hq.1, by simpa only [Real.ball_eq_Ioo] using hq.2⟩
  have hD : IsOpen D := isOpen_ball.prod isOpen_Ioo
  have hΨ : ContDiffOn ℝ 2 Ψ D := hΨ₀.mono (hDN.trans inter_subset_left)
  have hODE (q : W × ℝ) (hq : q ∈ D) :
      HasDerivAt (fun s ↦ Ψ (q.1, s))
        (localHamiltonianVectorField (F.chartEnergy old) e (Ψ q)) q.2 :=
    hF.hasDerivAt_chartMomentum old (hEL q.1 (hDN hq).1.1.1 q.2 (mem_univ _))
      (hDN hq).1.2 he hsub (hDN hq).2
  refine ⟨e, r, he, hsub, hi, hr, ?_, (fun q hq ↦ (hDN hq).1.2), hΨ,
    (fun q hq ↦ (hDN hq).2), ?_⟩
  · intro w hw'
    exact (hDN (show (w, t₀) ∈ D from ⟨hw', by constructor <;> linarith⟩)).1.1.1
  · intro q hq
    refine ⟨hODE q hq, ?_⟩
    intro ξ
    exact hasDerivAt_parameterVariation_of_nonautonomousODE
      (X := fun _ ↦ localHamiltonianVectorField (F.chartEnergy old) e) hD hΨ hODE hq
      ((hX.contDiffAt (e.open_target.mem_nhds (hDN hq).2)).differentiableAt (by simp)) ξ

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
