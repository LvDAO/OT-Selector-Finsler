import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.C2Variation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerHamiltonianFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerHamiltonianFamily`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.HamiltonianFamily

* **Conditions:** A specified genuine local Hamiltonian flow with a normed-space C2 seed, or a given C2 phase family satisfying its genuine field equation.
* **Objects:** The seeded C2 phase family and its actual position–velocity/slit Euler–Lagrange properties.
* **Proof detail:** Compose flow and seed, use the inverse Legendre position identity to read velocity, and read the momentum component as the actual original Euler–Lagrange equation.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual Hamiltonian families and their position equations

A given jointly C2 phase family solving the genuine Hamiltonian equation supplies its
actual position-velocity phase and original Finsler energy Euler--Lagrange equation.
A second interface constructs such phase families from the same given local flow and
an arbitrary normed-space C2 seed. No position equation is supplied independently.
-/

open Set Metric Manifold
open scoped ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A C2 family of seeds in the initial ball gives a jointly C2 actual phase family,
its genuine Hamiltonian equation and range, using the same flow throughout. -/
theorem hamiltonianFlow_seededFamily
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {seed : W → E × (E →L[ℝ] ℝ)} {B : Set W} {p : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ}
    (hflow : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
      t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hΦ : ContDiffOn ℝ 2 Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)))
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hseed : ContDiffOn ℝ 2 seed B) (hmem : MapsTo seed B (closedBall p r)) :
    let Ψ := fun q : W × ℝ ↦ Φ (seed q.1, q.2)
    ContDiffOn ℝ 2 Ψ (B ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
      MapsTo Ψ (B ×ˢ Ioo (t₀ - T) (t₀ + T)) e.target ∧
      ∀ w ∈ B, ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
        HasDerivAt (fun s ↦ Ψ (w, s))
          (localHamiltonianVectorField L e (Ψ (w, t))) t := by
  have hs : ContDiffOn ℝ 2 (fun q : W × ℝ ↦ seed q.1)
      (B ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    hseed.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  refine ⟨hΦ.comp (hs.prodMk contDiffOn_snd)
    (fun _ hq ↦ ⟨hmem hq.1, Ioo_subset_Icc_self hq.2⟩), ?_, ?_⟩
  · intro q hq
    exact hmap ⟨hmem hq.1, Ioo_subset_Icc_self hq.2⟩
  · intro w hw t ht
    exact hasDerivAt_hamiltonianFlow_slice hflow (hmem hw) ht

namespace ContinuousFinslerNorm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- An actual Hamiltonian phase family gives its genuine slit position-velocity phase
and original energy Euler--Lagrange equation for every parameter and interior time. -/
theorem chartHamiltonianFamily_positionProperties (F : ContinuousFinslerNorm E M) (x₀ : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsub : e.source ⊆ chartEnergyDomain x₀)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {B : Set W} {I : Set ℝ}
    (hI : IsOpen I) (hΨ : ContDiffOn ℝ 2 Ψ (B ×ˢ I))
    (hmap : MapsTo Ψ (B ×ˢ I) e.target)
    (hODE : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt (fun s ↦ Ψ (w, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) e (Ψ (w, t))) t) :
    let γ := fun q : W × ℝ ↦ (Ψ q).1
    ContDiffOn ℝ 2 γ (B ×ˢ I) ∧
      (∀ w ∈ B, ∀ t ∈ I,
        (γ (w, t), deriv (fun s ↦ γ (w, s)) t) ∈ chartEnergyDomain x₀) ∧
      ∀ w ∈ B, ∀ t ∈ I, HasDerivAt
        (fun s ↦ fiberLegendre (F.chartEnergy x₀)
          (γ (w, s), deriv (fun u ↦ γ (w, u)) s))
        (baseEnergyDifferential (F.chartEnergy x₀)
          (γ (w, t), deriv (fun u ↦ γ (w, u)) t)) t := by
  refine ⟨hΨ.fst, ?_, ?_⟩
  · intro w hw t ht
    rw [← hamiltonian_inverse_eq_position_deriv he (hmap ⟨hw, ht⟩) (hODE w hw t ht)]
    exact hsub (e.map_target (hmap ⟨hw, ht⟩))
  · intro w hw t ht
    exact hasDerivAt_eulerLagrange_of_hamiltonian he hI
      (fun s hs ↦ hmap ⟨hw, hs⟩) (hODE w hw) ht

end ContinuousFinslerNorm
end OTSelector.Geometry

end
end
