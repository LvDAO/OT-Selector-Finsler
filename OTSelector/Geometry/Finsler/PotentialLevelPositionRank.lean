import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompletePhaseJetMatching
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.PotentialLevelPositionRank

* **Conditions:** A given potential-level family and an ambient actual family have matching ordinary initial phase jets; the ambient derivative has its proved positive lower bound.
* **Objects:** Actual position rank of the same potential-level family throughout the calibrated interval.
* **Proof detail:** Match ordinary position derivatives through the original complete flow and restrict the ambient lower bound to the actual covector kernel.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialLevelPositionRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialLevelPositionRank`; the selected original proof blocks follow. -/
section

/-!
# Actual position rank of a given potential-level family

The given level family and an ambient family composed with its level chart have the
same ordinary initial phase jet. Their actual position derivatives therefore agree.
An established ambient derivative lower bound restricts to the covector kernel and
gives position rank for the same level family throughout its calibrated interval.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- A given complete level family with the normalized ordinary initial phase jet
inherits the ambient position derivative restricted to the initial covector kernel.
The positive ambient lower bound, already constructed on calibrated C1,1 cores,
passes to this actual derivative. Only an ordinary neighborhood of the level seed is
used to compare the two families; no density of a parameter preimage is required. -/
theorem potentialLevel_position_rank_of_initial_phase_jet
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {U : Set E} (hU : IsOpen U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {q : E → E →L[ℝ] ℝ} {A : E → ℝ → M}
    (hAEL : ∀ x ∈ U, F.IsEulerLagrangeOn (A x) univ)
    (hAinit : ∀ x ∈ U, A x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hAp : ∀ x ∈ U, F.chartMomentumFamily initial A (x, 0) = (x, q x))
    {x₀ : E} (hx₀ : x₀ ∈ U) {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hq : HasFDerivAt q H x₀)
    {σ : (q x₀).ker → E} (hσ₀ : σ 0 = x₀)
    (hσ : HasFDerivAt σ (q x₀).ker.subtypeL 0)
    {B : Set (q x₀).ker} (hB : IsOpen B) (h₀ : (0 : (q x₀).ker) ∈ B)
    {Γ : (q x₀).ker → ℝ → M}
    (hΓEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hΓsource : ∀ w ∈ B, Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) initial).source)
    (hjet : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ (w, 0))
      ((q x₀).ker.subtypeL.prod (H.comp (q x₀).ker.subtypeL)) 0)
    (hvalue : F.chartMomentumFamily initial Γ (0, 0) = (x₀, q x₀))
    {δ : ℝ}
    (hRank : ∀ (terminal : M) (t : ℝ), |t| < δ →
      A x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      DifferentiableAt ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t)) x₀ ∧
        ∃ c : ℝ, 0 < c ∧
          (∀ v : E, c * ‖v‖ ≤
            ‖fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t)) x₀ v‖) ∧
          Function.Injective
            (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t)) x₀)) :
    A x₀ = Γ 0 ∧ ∀ (terminal : M) (t : ℝ), |t| < δ →
      Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)) 0 =
        (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t)) x₀).comp
          (q x₀).ker.subtypeL ∧
      HasFDerivAt (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t))
        ((fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t)) x₀).comp
          (q x₀).ker.subtypeL) 0 ∧
      ∃ c : ℝ, 0 < c ∧
        (∀ w : (q x₀).ker, c * ‖w‖ ≤
          ‖fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (Γ z t)) 0 w‖) ∧
        Function.Injective
          (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)) 0) := by
  let J : (q x₀).ker →L[ℝ] E := (q x₀).ker.subtypeL
  let ΓA : (q x₀).ker → ℝ → M := fun w ↦ A (σ w)
  have hσU : ∀ᶠ w in 𝓝 (0 : (q x₀).ker), σ w ∈ U :=
    hσ.continuousAt (by simpa only [hσ₀] using hU.mem_nhds hx₀)
  have hnear : ∀ᶠ w in 𝓝 (0 : (q x₀).ker), w ∈ B ∧ σ w ∈ U := by
    filter_upwards [hB.mem_nhds h₀, hσU] with w hw hσw
    exact ⟨hw, hσw⟩
  obtain ⟨V, hVsub, hV, h₀V⟩ := mem_nhds_iff.mp hnear
  have hAjet : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial ΓA (w, 0))
      (J.prod (H.comp J)) 0 := by
    have hqσ : HasFDerivAt q H (σ 0) := by rw [hσ₀]; exact hq
    have hseed := hσ.prodMk (hqσ.comp 0 hσ)
    apply hseed.congr_of_eventuallyEq
    filter_upwards [hσU] with w hw
    exact hAp (σ w) hw
  have hsourceA : ∀ w ∈ V,
      ΓA w 0 ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    intro w hw
    change A (σ w) 0 ∈ _
    rw [hAinit (σ w) (hVsub hw).2]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target (hUt (hVsub hw).2)
  have hAvalue : F.chartMomentumFamily initial ΓA (0, 0) =
      F.chartMomentumFamily initial Γ (0, 0) := by
    change F.chartMomentumFamily initial A (σ 0, 0) = _
    rw [hσ₀, hAp x₀ hx₀, hvalue]
  obtain ⟨hcenter, hmatch⟩ := hF.same_position_firstJet_of_complete_initial_phase
    hcomplete initial 0 hV h₀V (fun w hw ↦ hAEL (σ w) (hVsub hw).2)
      (fun w hw ↦ hΓEL w (hVsub hw).1) hsourceA
      (fun w hw ↦ hΓsource w (hVsub hw).1) hAjet hjet hAvalue
  have hcenter' : A x₀ = Γ 0 := by simpa only [ΓA, hσ₀] using hcenter
  refine ⟨hcenter', fun terminal t ht hlegal ↦ ?_⟩
  have hlegalA : A x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    rw [hcenter']
    exact hlegal
  obtain ⟨hAdiff, c, hc, hbound, hinj⟩ := hRank terminal t ht hlegalA
  have hAσ : HasFDerivAt
      (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t))
      (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t)) x₀) (σ 0) := by
    rw [hσ₀]
    exact hAdiff.hasFDerivAt
  have hcomp := hAσ.comp 0 hσ
  obtain ⟨hΓA, hΓ⟩ := hmatch terminal t hlegal
  have heq : fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)) 0 =
      (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A x t)) x₀).comp J :=
    hΓA.fderiv.symm.trans hcomp.fderiv
  rw [heq] at hΓ
  refine ⟨heq, hΓ, c, hc, ?_, ?_⟩
  · intro w
    rw [heq]
    exact hbound (w : E)
  · rw [heq]
    exact hinj.comp Subtype.val_injective

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
