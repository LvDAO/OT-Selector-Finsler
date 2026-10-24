import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Flow.C2
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.FlowCoordinates
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional smooth strongly convex Finsler data, one nonzero chart state and initial time.
* **Objects:** Smooth constant-energy normal initial data, their actual C2 Hamiltonian flow, and locally invertible C2 position coordinates over the kernel of central momentum.
* **Proof detail:** Construct normal data and a genuine C2 Hamiltonian flow, prove positive momentum/velocity transversality, then apply the position-flow inverse theorem. Restrict the parameter neighborhood so the chosen initial velocities belong to the actual inverse Legendre branch used by the flow.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1, Proposition 1.1, p. 3; Section 1.1, Definition 1.2 and Remarks 1.3(4), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=3
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 6.2, Lemma 6.2 and proof, pp. 190–191 (straightening out of vector fields).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=201
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
  https://www.jirka.org/ra/realanal2.pdf#page=51

**Relationship to the sources:** This combines Legendre conormal initialization with the transverse-section/inverse-function strategy of the flow-box proof. It is a derived local position-coordinate construction, not a claim of Riemannian exponential normal coordinates.
-/

/-!
# Actual Finsler position coordinates from normal initial data

Construct the constant-energy initial velocity field and the actual Hamiltonian flow
from the same original smooth strongly convex Finsler energy. The original positive
momentum-velocity pairing supplies the invertibility needed for local position
coordinates. The resulting map and its inverse are jointly C2 on open neighborhoods.

Normal-data construction and flow construction may choose different local Legendre
inverses. The parameter neighborhood is therefore restricted so that the actual initial
velocity belongs to the flow inverse's source. This identifies the initial phase on
that very branch and proves its original energy equals the central energy. No normal
field, coordinate invertibility, prescribed derivative bound or geometric foliation is
an input. Identifying the calibration differential and minimizing length remain separate.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- Original Finsler data construct genuine C2 position coordinates from constant-energy
Hamiltonian trajectories; the initial covectors all have the same kernel. -/
theorem exists_chartHamiltonian_normalCoordinates (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let p := fiberLegendre L z
    let q₀ := parametricLegendre L z
    ∃ (U : Set E) (v : E → E) (a : E → ℝ) (ι : p.ker → E × (E →L[ℝ] ℝ))
      (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (r : ℝ≥0) (T : ℝ) (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ))
      (g : OpenPartialHomeomorph (p.ker × ℝ) E) (ρ : ℝ≥0) (τ : ℝ),
      IsOpen U ∧ z.1 ∈ U ∧ ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧
      v z.1 = z.2 ∧ a z.1 = 1 ∧ 0 < p z.2 ∧
      (∀ x ∈ U, (x, v x) ∈ chartEnergyDomain x₀ ∧ 0 < a x ∧
        L (x, v x) = L z ∧ fiberLegendre L (x, v x) = a x • p) ∧
      (∀ w : p.ker, ι w = (z.1 + (w : E), a (z.1 + (w : E)) • p)) ∧
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ 0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ q₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall q₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      ContDiffOn ℝ 2 Φ (closedBall q₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) ∧
      (g : p.ker × ℝ → E) = hamiltonianFlowPositionMap (p := p) Φ ι ∧
      (0, t₀) ∈ g.source ∧ z.1 ∈ g.target ∧
      g (0, t₀) = z.1 ∧ g.symm z.1 = (0, t₀) ∧
      ContDiffOn ℝ 2 g g.source ∧ ContDiffOn ℝ 2 g.symm g.target ∧
      (∀ q ∈ g.source, z.1 + (q.1 : E) ∈ U) ∧
      (∀ q ∈ g.source, e.symm (ι q.1) =
        (z.1 + (q.1 : E), v (z.1 + (q.1 : E)))) ∧
      (∀ q ∈ g.source, L (e.symm (ι q.1)) = L z) ∧
      MapsTo (fun q : p.ker × ℝ ↦ (ι q.1, q.2)) g.source
        (closedBall q₀ r ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
      0 < ρ ∧ 0 < τ ∧ τ ≤ T ∧
      closedBall (0 : p.ker) ρ ×ˢ Icc (t₀ - τ) (t₀ + τ) ⊆ g.source := by
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  let q₀ := parametricLegendre L z
  obtain ⟨U, v, a, hU, hzU, hv, ha, hv₀, ha₀, hp, hnormal⟩ :=
    hF.exists_constantEnergy_normalData x₀ hz
  obtain ⟨e, r, T, Φ, he, hzs, hsub, hG, hr, hT, hflow, hmap, hC2, _⟩ :=
    hF.exists_chartHamiltonian_c2Flow x₀ hz t₀
  let β : p.ker → E := fun w ↦ z.1 + (w : E)
  let ι : p.ker → E × (E →L[ℝ] ℝ) := fun w ↦ (β w, a (β w) • p)
  have hβ : ContDiff ℝ ∞ β := contDiff_const.add p.ker.subtypeL.contDiff
  have hβ₀ : β 0 = z.1 := by simp [β]
  have haAt : ContDiffAt ℝ 2 a (β 0) := by
    rw [hβ₀]
    exact (ha.contDiffAt (hU.mem_nhds hzU)).of_le (by simp)
  have hβAt : ContDiffAt ℝ 2 β 0 := hβ.contDiffAt.of_le (by simp)
  have hι : ContDiffAt ℝ 2 ι 0 :=
    hβAt.prodMk ((haAt.comp 0 hβAt).smul contDiffAt_const)
  have hι₀ : ι 0 = q₀ := by
    dsimp only [ι]
    rw [hβ₀, ha₀, one_smul]
    rfl
  have hbase : ∀ᶠ w in 𝓝 (0 : p.ker), (ι w).1 = q₀.1 + (w : E) :=
    Filter.Eventually.of_forall (fun _ ↦ rfl)
  have hinv : e.symm q₀ = z := by
    change e.symm (parametricLegendre (F.chartEnergy x₀) z) = z
    rw [← he, e.left_inv hzs]
  have htrans : p (localHamiltonianVectorField L e q₀).1 ≠ 0 := by
    change p (e.symm q₀).2 ≠ 0
    rw [hinv]
    exact hp.ne'
  let W : Set (p.ker × ℝ) := interior {q | β q.1 ∈ U ∧
    (β q.1, v (β q.1)) ∈ e.source}
  have hW : IsOpen W := isOpen_interior
  have hbAt : ContinuousAt (fun q : p.ker × ℝ ↦ β q.1) (0, t₀) :=
    (hβ.continuous.comp continuous_fst).continuousAt
  have hvAt : ContinuousAt v (β 0) := by
    rw [hβ₀]
    exact (hv.contDiffAt (hU.mem_nhds hzU)).continuousAt
  have hW₀ : (0, t₀) ∈ W := by
    apply mem_interior_iff_mem_nhds.mpr
    apply inter_mem
    · exact hbAt.preimage_mem_nhds (by simpa only [hβ₀] using hU.mem_nhds hzU)
    · exact (hbAt.prodMk (hvAt.comp_of_eq hbAt rfl)).preimage_mem_nhds
        (e.open_source.mem_nhds (by simpa only [Function.comp_apply, hβ₀, hv₀, Prod.eta] using hzs))
  obtain ⟨g, ρ, τ, hg, hgc, hgt, hgcval, hgic, hgC2, hgiC2, hWsub,
      hgbox, hρ, hτ, hτT, hbox⟩ :=
    exists_hamiltonianFlowCoordinates hflow hC2 hr hT hι hι₀ hbase htrans hW hW₀
  have hbaseU : ∀ q ∈ g.source, β q.1 ∈ U :=
    fun _ hq ↦ (interior_subset (hWsub hq)).1
  have hinitial : ∀ q ∈ g.source, e.symm (ι q.1) = (β q.1, v (β q.1)) := by
    intro q hq
    have hsrc := (interior_subset (hWsub hq)).2
    have hιleg : ι q.1 = parametricLegendre L (β q.1, v (β q.1)) := by
      apply Prod.ext
      · rfl
      · exact (hnormal (β q.1) (hbaseU q hq)).2.2.2.symm
    rw [hιleg, ← he, e.left_inv hsrc]
  have hinitialEnergy : ∀ q ∈ g.source, L (e.symm (ι q.1)) = L z := by
    intro q hq
    rw [hinitial q hq]
    exact (hnormal (β q.1) (hbaseU q hq)).2.2.1
  exact ⟨U, v, a, ι, e, r, T, Φ, g, ρ, τ, hU, hzU, hv, ha, hv₀, ha₀, hp,
    hnormal, fun _ ↦ rfl, he, hzs, hsub, hG, hr, hT, hflow, hmap, hC2,
    hg, hgc, hgt, hgcval, hgic, hgC2, hgiC2, hbaseU, hinitial, hinitialEnergy,
    hgbox, hρ, hτ, hτT, hbox⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
