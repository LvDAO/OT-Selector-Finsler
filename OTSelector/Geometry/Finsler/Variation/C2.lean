import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Flow.C2
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.C2Variation
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow
import OTSelector.Geometry.Finsler.Variation.Lagrangian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC2Variation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC2Variation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Variation.C2

* **Conditions:** A smooth strongly convex Finsler norm, a nonzero initial velocity, and a C2 curve of phase initial data through its actual Legendre image.
* **Objects:** A joint C2 position variation, a constructed local inverse Legendre map, positive time/parameter radii and slit-domain flow confinement.
* **Proof detail:** Use a local Legendre inverse and smooth ODE dependence, then continuity shrinks the parameter curve into the constructed closed flow ball.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.

Source relation (derived): This is a local Finsler specialization of smooth dependence, with confinement and admissible radii constructed rather than assumed.
-/

/-!
# Actual C2 Finsler Euler--Lagrange variations

A C2 curve of phase-space initial data through the Legendre image of a nonzero
Finsler velocity gives an actual joint C2 position variation. Continuity constructs
a positive parameter interval on which the initial data stay in the constructed
closed flow ball. Every varied curve satisfies the original Euler--Lagrange equation,
and its true position-velocity phase stays in the original slit chart-energy domain.

The local Legendre map, flow, time interval and parameter interval all come from the
given Finsler data and initial curve. No flow confinement or initial-range condition
is assumed.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- A C2 initial-state curve through the actual Legendre image produces a joint C2
variation of genuine local Euler--Lagrange curves. Its parameter neighborhood and
flow confinement are constructed from the original Finsler data and continuity. -/
theorem exists_chartHamiltonian_c2Variation (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ)
    {S : Set ℝ} (hS : IsOpen S) {s₀ : ℝ} (hs₀ : s₀ ∈ S)
    {ι : ℝ → E × (E →L[ℝ] ℝ)} (hι : ContDiffOn ℝ 2 ι S)
    (hι₀ : ι s₀ = parametricLegendre (F.chartEnergy x₀) z) :
    let L := F.chartEnergy x₀
    let p₀ := parametricLegendre L z
    ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (r : ℝ≥0) (T δ : ℝ)
      (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ 0 < r ∧ 0 < T ∧ 0 < δ ∧
      Ioo (s₀ - δ) (s₀ + δ) ⊆ S ∧
      MapsTo ι (Ioo (s₀ - δ) (s₀ + δ)) (closedBall p₀ r) ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      ContDiffOn ℝ 2 Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) ∧
      let σ := hamiltonianPositionVariation Φ ι
      let D := Ioo (s₀ - δ) (s₀ + δ) ×ˢ Ioo (t₀ - T) (t₀ + T)
      ContDiffOn ℝ 2 σ D ∧
      (∀ q ∈ D, variationPhase σ q = e.symm (Φ (ι q.1, q.2))) ∧
      MapsTo (variationPhase σ) D (chartEnergyDomain x₀) ∧
      (∀ s ∈ Ioo (s₀ - δ) (s₀ + δ), ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
        HasDerivAt (fun u ↦ fiberLegendre L (variationPhase σ (s, u)))
          (baseEnergyDifferential L (variationPhase σ (s, t))) t) ∧
      (∀ s ∈ Ioo (s₀ - δ) (s₀ + δ),
        variationPhase σ (s, t₀) = e.symm (ι s)) ∧
      variationPhase σ (s₀, t₀) = z := by
  let L := F.chartEnergy x₀
  let p₀ := parametricLegendre L z
  obtain ⟨e, r, T, Φ, he, hzsource, hsource, hG, hr, hT, hflow, hmap, hC2, _⟩ :=
    hF.exists_chartHamiltonian_c2Flow x₀ hz t₀
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcont : ContinuousAt ι s₀ := (hι.contDiffAt (hS.mem_nhds hs₀)).continuousAt
  have hpre : ι ⁻¹' ball p₀ r ∈ 𝓝 s₀ :=
    hcont.preimage_mem_nhds (isOpen_ball.mem_nhds (by
      rw [hι₀]
      exact mem_ball_self hrR))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hS.mem_nhds hs₀) hpre)
  have hparam : Ioo (s₀ - δ) (s₀ + δ) ⊆ S ∩ ι ⁻¹' ball p₀ r := by
    simpa only [Real.ball_eq_Ioo] using hδsub
  have hparamS : Ioo (s₀ - δ) (s₀ + δ) ⊆ S := fun _ hs ↦ (hparam hs).1
  have hparamMap : MapsTo ι (Ioo (s₀ - δ) (s₀ + δ)) (closedBall p₀ r) :=
    fun _ hs ↦ ball_subset_closedBall (hparam hs).2
  have hphase : ∀ q ∈ Ioo (s₀ - δ) (s₀ + δ) ×ˢ Ioo (t₀ - T) (t₀ + T),
      variationPhase (hamiltonianPositionVariation Φ ι) q = e.symm (Φ (ι q.1, q.2)) :=
    fun _ hq ↦ variationPhase_hamiltonianPositionVariation he hflow hmap (hparamMap hq.1) hq.2
  have hinit : ∀ s ∈ Ioo (s₀ - δ) (s₀ + δ),
      variationPhase (hamiltonianPositionVariation Φ ι) (s, t₀) = e.symm (ι s) :=
    fun _ hs ↦ variationPhase_hamiltonianPositionVariation_initial he hflow hmap hT
      (hparamMap hs)
  refine ⟨e, r, T, δ, Φ, he, hzsource, hsource, hG, hr, hT, hδ, hparamS, hparamMap,
    hflow, hmap, hC2, ?_, hphase, ?_, ?_, hinit, ?_⟩
  · exact contDiffOn_hamiltonianPositionVariation hC2 (hι.mono hparamS) hparamMap
  · intro q hq
    rw [hphase q hq]
    exact hsource (e.map_target (hmap ⟨hparamMap hq.1, Ioo_subset_Icc_self hq.2⟩))
  · intro s hs t ht
    exact hasDerivAt_eulerLagrange_hamiltonianPositionVariation he hflow hmap
      (hparamMap hs) ht
  · rw [hinit s₀ ⟨by linarith, by linarith⟩, hι₀, ← he]
    exact e.left_inv hzsource

end ContinuousFinslerNorm.IsSmoothStronglyConvex

end OTSelector.Geometry

end
