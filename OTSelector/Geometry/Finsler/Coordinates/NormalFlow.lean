import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.Flow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.C2Variation
import OTSelector.Geometry.Finsler.Hamiltonian.FlowCoordinates
import OTSelector.Geometry.Finsler.Hamiltonian.NormalVariation
import OTSelector.Geometry.Finsler.Variation.Lagrangian

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional smooth strongly convex Finsler data, one nonzero chart state and initial time.
* **Objects:** A genuine C2 position chart on an open kernel-by-time box, original equal-energy Euler–Lagrange time curves, identified initial phase and initial conormal momentum.
* **Proof detail:** Restrict the already constructed position coordinates to an actual open box. Identify the true time velocity with the flow Legendre inverse, apply Hamiltonian conservation, and recover Euler–Lagrange and initial phase identities on that branch.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 6.2, Lemma 6.2 and proof, pp. 190–191 (straightening out of vector fields).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=201
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 7, Definition 7.3 and Proposition 7.4, p. 31; Section 7.2, Propositions 7.14–7.15, p. 35.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
  https://www.jirka.org/ra/realanal2.pdf#page=51

**Relationship to the sources:** This is the local-domain assembly of Legendre Hamiltonian flow, conserved energy and transverse coordinates. Equal energy and initial conormality are conclusions of construction; no additional textbook normal-flow premise is imposed.
-/

/-!
# Actual constant-energy Finsler position flow on an open box

Restrict the already constructed genuine Finsler position coordinates to an open
parameter-time box. Its actual time derivative, energy, Euler--Lagrange equation and
initial momentum are identified using the very same Hamiltonian flow and Legendre
inverse branch. The target lies in the original base chart, and the central phase is
the originally prescribed nonzero position-velocity state.

Every neighborhood and initial datum is constructed from the given smooth strongly
convex Finsler structure. No prescribed family, constant-energy premise or geometric
splitting condition is required. The open box supplies the actual data for the Gauss
and calibration constructions; this module alone does not assert minimality.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- Original Finsler data produce a C2 local position chart with actual constant-energy
Euler--Lagrange time curves and common initial momentum kernel. -/
theorem exists_chartNormalPositionFlow (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let p := fiberLegendre L z
    ∃ (g : OpenPartialHomeomorph (p.ker × ℝ) E) (ρ τ : ℝ) (a : p.ker → ℝ),
      let phase := fun q : p.ker × ℝ ↦ (g q, deriv (fun t ↦ g (q.1, t)) q.2)
      0 < ρ ∧ 0 < τ ∧
      g.source = ball (0 : p.ker) ρ ×ˢ Ioo (t₀ - τ) (t₀ + τ) ∧
      (0, t₀) ∈ g.source ∧ z.1 ∈ g.target ∧
      g (0, t₀) = z.1 ∧ g.symm z.1 = (0, t₀) ∧
      ContDiffOn ℝ 2 g g.source ∧ ContDiffOn ℝ 2 g.symm g.target ∧
      g.target ⊆ (extChartAt 𝓘(ℝ, E) x₀).target ∧
      phase (0, t₀) = z ∧
      (∀ q ∈ g.source, phase q ∈ chartEnergyDomain x₀ ∧ L (phase q) = L z) ∧
      (∀ w ∈ ball (0 : p.ker) ρ, g (w, t₀) = z.1 + (w : E) ∧
        fiberLegendre L (phase (w, t₀)) = a w • p) ∧
      ∀ q ∈ g.source, HasDerivAt
        (fun t ↦ fiberLegendre L (phase (q.1, t)))
        (baseEnergyDifferential L (phase q)) q.2 := by
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  obtain ⟨U, v, a, ι, e, r, T, Φ, g, ρ, τ, hU, hzU, hv, ha, hv₀, ha₀, hp,
      hnormal, hι, he, hzs, hsub, hG, hr, hT, hflow, hmap, hC2,
      hg, hgc, hgt, hgcval, hgic, hgC2, hgiC2, hbaseU, hinitial, hinitialEnergy,
      hgbox, hρ, hτ, hτT, hbox⟩ := hF.exists_chartHamiltonian_normalCoordinates x₀ hz t₀
  let D : Set (p.ker × ℝ) := ball (0 : p.ker) (ρ : ℝ) ×ˢ Ioo (t₀ - τ) (t₀ + τ)
  have hD : IsOpen D := isOpen_ball.prod isOpen_Ioo
  have hDs : D ⊆ g.source := fun _ hq ↦ hbox ⟨ball_subset_closedBall hq.1, Ioo_subset_Icc_self hq.2⟩
  let g' := g.restr D
  have hsource : g'.source = D := by
    rw [OpenPartialHomeomorph.restr_source' g D hD]
    exact inter_eq_right.mpr hDs
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hc : (0, t₀) ∈ g'.source := by
    rw [hsource]
    exact ⟨mem_ball_self hρR, ⟨by linarith, by linarith⟩⟩
  have hcval : g' (0, t₀) = z.1 := hgcval
  have hct : z.1 ∈ g'.target := hcval ▸ g'.map_source hc
  have hci : g'.symm z.1 = (0, t₀) := by
    rw [← hcval]
    exact g'.left_inv hc
  have hforward : ContDiffOn ℝ 2 g' g'.source := hgC2.mono (fun _ hq ↦ hq.1)
  have hinverse : ContDiffOn ℝ 2 g'.symm g'.target := hgiC2.mono (fun _ hx ↦ hx.1)
  let phase := fun q : p.ker × ℝ ↦ (g' q, deriv (fun t ↦ g' (q.1, t)) q.2)
  have hg' : (g' : p.ker × ℝ → E) = hamiltonianFlowPositionMap (p := p) Φ ι := hg
  have hphase : ∀ q ∈ g'.source, phase q = e.symm (Φ (ι q.1, q.2)) := by
    intro q hq
    have hb := hgbox hq.1
    have h := variationPhase_hamiltonianPositionVariation he hflow hmap
      (ι := fun _ : ℝ ↦ ι q.1) (s := 0) hb.1 hb.2
    simpa only [phase, hg', variationPhase, variationVelocity,
      hamiltonianPositionVariation, hamiltonianFlowPositionMap] using h
  have hphase_initial : ∀ w ∈ ball (0 : p.ker) (ρ : ℝ),
      phase (w, t₀) = (z.1 + (w : E), v (z.1 + (w : E))) := by
    intro w hw
    have hwD : (w, t₀) ∈ g'.source := by
      rw [hsource]
      exact ⟨hw, ⟨by linarith, by linarith⟩⟩
    rw [hphase _ hwD, hflow.apply_initial _ (hgbox hwD.1).1]
    exact hinitial _ hwD.1
  have hadmissible : ∀ q ∈ g'.source,
      phase q ∈ chartEnergyDomain x₀ ∧ L (phase q) = L z := by
    intro q hq
    have hb := hgbox hq.1
    constructor
    · rw [hphase _ hq]
      exact hsub (e.map_target (hmap ⟨hb.1, Ioo_subset_Icc_self hb.2⟩))
    · have henergy := hF.chartEnergy_hamiltonianPositionVariation_eq_initial x₀ he hsub hG
        hflow hmap hT (ι := fun _ : ℝ ↦ ι q.1) (s := 0) hb.1 hb.2
      have hident : variationPhase (hamiltonianPositionVariation Φ (fun _ : ℝ ↦ ι q.1))
          (0, q.2) = phase q := by
        simp only [phase, hg', variationPhase, variationVelocity,
          hamiltonianPositionVariation, hamiltonianFlowPositionMap]
      rw [hident] at henergy
      exact henergy.trans (hinitialEnergy _ hq.1)
  have htarget : g'.target ⊆ (extChartAt 𝓘(ℝ, E) x₀).target := by
    intro x hx
    have h := (hadmissible (g'.symm x) (g'.map_target hx)).1.1
    change g' (g'.symm x) ∈ _ at h
    rwa [g'.right_inv hx] at h
  refine ⟨g', ρ, τ, (fun w ↦ a (z.1 + (w : E))), hρR, hτ, hsource,
    hc, hct, hcval, hci, hforward, hinverse, htarget, ?_, hadmissible, ?_, ?_⟩
  · change phase (0, t₀) = z
    rw [hphase_initial _ (mem_ball_self hρR)]
    simp only [ZeroMemClass.coe_zero, add_zero, hv₀, Prod.eta]
  · intro w hw
    have hwD : (w, t₀) ∈ g'.source := by
      rw [hsource]
      exact ⟨hw, ⟨by linarith, by linarith⟩⟩
    constructor
    · exact congrArg Prod.fst (hphase_initial w hw)
    · change fiberLegendre L (phase (w, t₀)) = a (z.1 + (w : E)) • p
      rw [hphase_initial w hw]
      exact (hnormal _ (hbaseU _ hwD.1)).2.2.2
  · intro q hq
    have hb := hgbox hq.1
    have h := hasDerivAt_eulerLagrange_hamiltonianPositionVariation he hflow hmap
      (ι := fun _ : ℝ ↦ ι q.1) (s := 0) hb.1 hb.2
    simpa only [phase, hg', variationPhase, variationVelocity,
      hamiltonianPositionVariation, hamiltonianFlowPositionMap] using h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
