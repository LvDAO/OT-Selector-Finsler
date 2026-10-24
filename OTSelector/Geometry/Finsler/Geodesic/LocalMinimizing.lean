import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Calibration.ChartCurve
import OTSelector.Geometry.Finsler.Calibration.Flow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.GaussLemma
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
# Local minimizing segments of Finsler geodesics

Main declarations: exists_localMinimizingEulerLagrange; chartEulerLagrange_locally_minimizing.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.Minimizing`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A smooth strongly convex reversible Finsler structure on a finite-dimensional smooth manifold, and a nonzero chart or actual tangent state; regularity/Hausdorff assumptions as stated for local minimality.
* **Objects:** A smooth constant-speed local Euler–Lagrange curve whose sufficiently short ordered subsegments attain the genuine length distance.
* **Proof detail:** Use the constructed flow calibration, pull it to the manifold, derive a shortness/containment neighborhood and apply the calibration comparison. Bootstrap and use local uniqueness for any given C2 solution.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* J. C. Álvarez Paiva; A. C. Thompson, *Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)*, Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
  https://library.slmath.org/books/Book50/files/02AT.pdf#page=22
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49

**Relationship to the sources:** Construction of the local-minimizing implication in the spray/geodesic equivalence using the exact one-form calibration method.
-/

/-!
# Local minimizing geodesics for the original smooth Finsler structure

The constructed actual flow calibration gives a smooth, constant-speed Euler--Lagrange
curve through every prescribed nonzero tangent state. Every ordered pair of sufficiently
nearby times realizes the original Finsler length distance, whose infimum ranges over all
C1 competitors. Calibration, normal coordinates, containment and shortness are constructed
from the original data. No curvature, foliation, or global topological restriction is used.

A C2 actual Euler--Lagrange curve is first bootstrapped to smoothness; local uniqueness then
transfers the minimizing conclusion to any such given curve. The manifold existence theorem
uses only finite dimension, the ordinary Hausdorff manifold assumption and the original
smooth strongly convex Finsler structure. Global continuation, global minimizing existence,
intrinsic Jacobi geometry and the empirical selector remain separate dependencies.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- A nonzero original chart state initiates a smooth constant-speed Euler--Lagrange curve
whose every sufficiently short subsegment realizes the genuine Finsler length distance. -/
theorem exists_localMinimizing_chartEulerLagrange [RegularSpace M]
    (hF : F.IsSmoothStronglyConvex) (x₀ : M) {z : E × E}
    (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E,
      let c := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ
      γ t₀ = z.1 ∧ deriv γ t₀ = z.2 ∧
      ContDiffOn ℝ ∞ γ (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (Ioo (t₀ - ε) (t₀ + ε)) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        (γ t, deriv γ t) ∈ chartEnergyDomain x₀ ∧
        HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (γ s, deriv γ s))
          (baseEnergyDifferential (F.chartEnergy x₀) (γ t, deriv γ t)) t) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = F.chartLength x₀ z) ∧
      ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), s ≤ t →
        F.lengthEDist (c s) (c t) = Manifold.pathELength 𝓘(ℝ, E) c s t := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let p := fiberLegendre (F.chartEnergy x₀) z
  obtain ⟨g, ρ, τ, u, hρ, hτ, hsource, hcval, hct, hg, hu, htarget,
      hcenter, hphase, hupotential, hEL, hbound, hsat⟩ :=
    hF.exists_chartFlowCalibration x₀ hz t₀
  let γ : ℝ → E := fun t ↦ g (0, t)
  let S : Set ℝ := Ioo (t₀ - τ) (t₀ + τ)
  have ht₀ : t₀ ∈ S := ⟨by linarith, by linarith⟩
  have hq : ∀ t ∈ S, ((0 : p.ker), t) ∈ g.source := by
    intro t ht
    rw [hsource]
    exact ⟨mem_ball_self hρ, ht⟩
  have hγ₂ : ContDiffOn ℝ 2 γ S :=
    hg.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht ↦ hq t ht)
  have hγphase : ∀ t ∈ S, (γ t, deriv γ t) ∈ chartEnergyDomain x₀ :=
    fun t ht ↦ (hphase (0, t) (hq t ht)).1
  have hγEL : ∀ t ∈ S,
      HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (γ s, deriv γ s))
        (baseEnergyDifferential (F.chartEnergy x₀) (γ t, deriv γ t)) t :=
    fun t ht ↦ hEL (0, t) (hq t ht)
  have hγSmooth := hF.contDiffOn_chartEulerLagrange_of_contDiffOn_two x₀ isOpen_Ioo hγ₂ hγphase hγEL
  have hγ₁ : ContDiffOn ℝ 1 γ S := hγ₂.of_le (by norm_num)
  have hmap : MapsTo γ S g.target := fun t ht ↦ g.map_source (hq t ht)
  have hsaturation : ∀ t ∈ S,
      fderiv ℝ u (γ t) (deriv γ t) = (F.chartLength x₀ (γ t, deriv γ t) : ℝ) :=
    fun t ht ↦ hsat (0, t) (hq t ht)
  obtain ⟨ε, hε, hεS, hmin⟩ := F.exists_local_minimality_chartCurve_of_calibrated
    x₀ g.open_target htarget (hu.of_le (by norm_num)) hbound isOpen_Ioo ht₀ hγ₁ hmap hsaturation
  have hsub : Ioo (t₀ - ε) (t₀ + ε) ⊆ S := Ioo_subset_Icc_self.trans hεS
  have hcSmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ) S :=
    (contMDiffOn_extChartAt_symm x₀).comp hγSmooth.contMDiffOn (fun t ht ↦ htarget (hmap ht))
  refine ⟨ε, hε, γ, hcval, ?_, hγSmooth.mono hsub, hcSmooth.mono hsub,
    fun t ht ↦ ⟨hγphase t (hsub ht), hγEL t (hsub ht)⟩, ?_, hmin⟩
  · exact congrArg Prod.snd hcenter
  · intro t ht
    have hts := hsub ht
    have hd := (hγ₁.contDiffAt (isOpen_Ioo.mem_nhds hts)).differentiableAt one_ne_zero |>.hasDerivAt
    exact (F.toFun_chartCurve_velocity x₀ (htarget (hmap hts)) hd).trans
      (hphase (0, t) (hq t hts)).2

/-- Every nonzero tangent at a point of a Hausdorff smooth strongly convex Finsler manifold
has a genuine smooth constant-speed local minimizing Euler--Lagrange curve. -/
theorem exists_localMinimizingEulerLagrange [T2Space M]
    (hF : F.IsSmoothStronglyConvex) (x₀ : M) {v : E} (hv : v ≠ 0) (t₀ : ℝ) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ ε > (0 : ℝ), ∃ c : ℝ → M,
      c t₀ = x₀ ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        (⟨x₀, tangentFiberModelEquiv x₀ v⟩ : TangentBundle 𝓘(ℝ, E) M) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (Ioo (t₀ - ε) (t₀ + ε)) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
          F.toFun ⟨x₀, tangentFiberModelEquiv x₀ v⟩) ∧
      (∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), s ≤ t →
        F.lengthEDist (c s) (c t) = Manifold.pathELength 𝓘(ℝ, E) c s t) ∧
      ∃ γ : ℝ → E, c = (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ ∧
        ContDiffOn ℝ ∞ γ (Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          (γ t, deriv γ t) ∈ chartEnergyDomain x₀ ∧
          HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (γ s, deriv γ s))
            (baseEnergyDifferential (F.chartEnergy x₀) (γ t, deriv γ t)) t := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨ε, hε, γ, hγ₀, hdγ₀, hγ, hc, hEL, hspeed, hmin⟩ :=
    hF.exists_localMinimizing_chartEulerLagrange x₀
      (z := (extChartAt 𝓘(ℝ, E) x₀ x₀, v)) ⟨mem_extChartAt_target x₀, hv⟩ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hd := (hγ.contDiffAt (isOpen_Ioo.mem_nhds ht₀)).differentiableAt (by simp)
  refine ⟨ε, hε, (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ, ?_, ?_, hc, ?_, hmin,
    γ, rfl, hγ, hEL⟩
  · change (extChartAt 𝓘(ℝ, E) x₀).symm (γ t₀) = x₀
    rw [hγ₀]
    exact (extChartAt 𝓘(ℝ, E) x₀).left_inv (mem_extChartAt_source x₀)
  · rw [tangentMap_chart_symm_curve x₀ (hEL t₀ ht₀).1.1 hd.hasDerivAt,
      hγ₀, hdγ₀, tangentChart_symm_self]
    rfl
  · intro t ht
    change _ = F.toFun ⟨x₀, v⟩
    simpa only [chartLength, tangentChart_symm_self] using hspeed t ht

/-- Any actual C2 Euler--Lagrange curve with nonzero velocity is locally distance minimizing;
smoothness and equality with the constructed minimizing germ are derived. -/
theorem chartEulerLagrange_locally_minimizing [RegularSpace M]
    (hF : F.IsSmoothStronglyConvex) (x₀ : M) {γ : ℝ → E} {S : Set ℝ} {t₀ : ℝ}
    (hS : IsOpen S) (ht₀ : t₀ ∈ S) (hγ : ContDiffOn ℝ 2 γ S)
    (hphase : ∀ t ∈ S, (γ t, deriv γ t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ S, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀) (γ s, deriv γ s))
      (baseEnergyDifferential (F.chartEnergy x₀) (γ t, deriv γ t)) t) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    let c := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ
    ∃ δ > (0 : ℝ), Icc (t₀ - δ) (t₀ + δ) ⊆ S ∧
      ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), s ≤ t →
        F.lengthEDist (c s) (c t) = Manifold.pathELength 𝓘(ℝ, E) c s t := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hγSmooth := hF.contDiffOn_chartEulerLagrange_of_contDiffOn_two x₀ hS hγ hphase hEL
  obtain ⟨ε, hε, y, hy₀, hdy₀, hy, hc, hyEL, hspeed, hmin⟩ :=
    hF.exists_localMinimizing_chartEulerLagrange x₀ (hphase t₀ ht₀) t₀
  have htε : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have heq := hF.chartEulerLagrange_eventuallyEq_of_same_initial_data x₀
    hS isOpen_Ioo ht₀ htε hγSmooth hy hEL (fun t ht ↦ (hyEL t ht).2)
    (hphase t₀ ht₀) hy₀.symm hdy₀.symm
  obtain ⟨δ, hδ, hgood⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (hS.mem_nhds ht₀) (inter_mem (isOpen_Ioo.mem_nhds htε) heq))
  have hwindow : Icc (t₀ - δ) (t₀ + δ) ⊆ closedBall t₀ δ := by
    intro t ht
    rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hwindowS : Icc (t₀ - δ) (t₀ + δ) ⊆ S := fun _ ht ↦ (hgood (hwindow ht)).1
  have hwindowε : Icc (t₀ - δ) (t₀ + δ) ⊆ Icc (t₀ - ε) (t₀ + ε) :=
    fun _ ht ↦ Ioo_subset_Icc_self (hgood (hwindow ht)).2.1
  have heqwin : EqOn γ y (Icc (t₀ - δ) (t₀ + δ)) := fun _ ht ↦ (hgood (hwindow ht)).2.2
  refine ⟨δ, hδ, hwindowS, ?_⟩
  intro s hs t ht hst
  have hlength := Manifold.pathELength_congr (I := 𝓘(ℝ, E))
    (γ := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ)
    (γ' := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ y)
    (a := s) (b := t)
    (fun u hu ↦ congrArg (extChartAt 𝓘(ℝ, E) x₀).symm
      (heqwin ((Icc_subset_Icc hs.1 ht.2) hu)))
  rw [hlength]
  simpa only [Function.comp_apply, heqwin hs, heqwin ht] using
    hmin s (hwindowε hs) t (hwindowε ht) hst

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
