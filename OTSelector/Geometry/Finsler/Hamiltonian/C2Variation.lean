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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Variation.Lagrangian

/-!
## Lemma skeleton

* **Conditions:** An actual local Hamiltonian flow staying in its Legendre target; joint C2 regularity when claiming joint C2 composition, and a C2 initial-state curve on an admissible parameter set.
* **Objects:** A genuine two-parameter position variation obtained by composing the phase flow with the initial-state curve, and its true position/velocity phase.
* **Proof detail:** Use the flow ODE on the interior time interval to recover the inverse Legendre velocity. Composition gives C2 regularity, inverse Legendre identities give the Euler–Lagrange equation, and the initial flow identity identifies the initial phase.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38

**Relationship to the sources:** This is the analytic realization of a varied Hamiltonian solution family. It combines the standard initial-data flow regularity and Legendre/Hamilton equivalence; its explicit domain/branch bookkeeping is local implementation.
-/

/-!
# Actual position variations from a jointly C2 Hamiltonian flow

Compose one actual phase flow with a C2 curve of initial states. Its position projection
is a joint C2 variation, and its true time velocity is the inverse Legendre velocity.
On the interior time interval, the closed-interval flow equation gives ordinary
derivatives and hence the original Euler--Lagrange equation for every varied curve.
This module supplies the analytic composition; the Finsler instance constructs its
admissible parameter neighborhood from the original data.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Position variation obtained from a given curve of phase-space initial states. -/
def hamiltonianPositionVariation
    (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ))
    (ι : ℝ → E × (E →L[ℝ] ℝ)) (q : ℝ × ℝ) : E :=
  (Φ (ι q.1, q.2)).1

/-- Restriction to interior time turns the actual flow's within derivative into an
ordinary derivative; no derivative equation is supplied separately for the slice. -/
theorem hasDerivAt_hamiltonianFlow_slice
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {p q : E × (E →L[ℝ] ℝ)} {r : ℝ≥0} {t₀ T t : ℝ}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
      t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hq : q ∈ closedBall p r) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    HasDerivAt (fun u ↦ Φ (q, u)) (localHamiltonianVectorField L e (Φ (q, t))) t :=
  (hΦ.hasDerivWithinAt q hq t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Joint C2 regularity is preserved under an actual C2 initial-state curve. -/
theorem contDiffOn_hamiltonianPositionVariation
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : ℝ → E × (E →L[ℝ] ℝ)} {p : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ} {S : Set ℝ}
    (hΦ : ContDiffOn ℝ 2 Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)))
    (hι : ContDiffOn ℝ 2 ι S) (hmem : MapsTo ι S (closedBall p r)) :
    ContDiffOn ℝ 2 (hamiltonianPositionVariation Φ ι)
      (S ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hιfst : ContDiffOn ℝ 2 (fun q : ℝ × ℝ ↦ ι q.1)
      (S ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    hι.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  exact (hΦ.comp (hιfst.prodMk contDiffOn_snd)
    (fun _ hq ↦ ⟨hmem hq.1, Ioo_subset_Icc_self hq.2⟩)).fst

/-- The actual position-velocity phase equals the inverse Legendre image of the flow. -/
theorem variationPhase_hamiltonianPositionVariation
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : ℝ → E × (E →L[ℝ] ℝ)} {p : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T s t : ℝ}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
      t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hs : ι s ∈ closedBall p r) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    variationPhase (hamiltonianPositionVariation Φ ι) (s, t) =
      e.symm (Φ (ι s, t)) := by
  exact (hamiltonian_inverse_eq_position_deriv he
    (hmap ⟨hs, Ioo_subset_Icc_self ht⟩)
    (hasDerivAt_hamiltonianFlow_slice hΦ hs ht)).symm

/-- Every interior time slice of the varied actual Hamiltonian flow satisfies the
true Euler--Lagrange equation for the original coordinate Lagrangian. -/
theorem hasDerivAt_eulerLagrange_hamiltonianPositionVariation
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : ℝ → E × (E →L[ℝ] ℝ)} {p : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T s t : ℝ}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
      t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hs : ι s ∈ closedBall p r) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    HasDerivAt
      (fun u ↦ fiberLegendre L (variationPhase (hamiltonianPositionVariation Φ ι) (s, u)))
      (baseEnergyDifferential L
        (variationPhase (hamiltonianPositionVariation Φ ι) (s, t))) t := by
  exact hasDerivAt_eulerLagrange_of_hamiltonian he isOpen_Ioo
    (fun u hu ↦ hmap ⟨hs, Ioo_subset_Icc_self hu⟩)
    (fun u hu ↦ hasDerivAt_hamiltonianFlow_slice hΦ hs hu) ht

/-- The varied phase recovers the true inverse Legendre initial state. -/
theorem variationPhase_hamiltonianPositionVariation_initial
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : ℝ → E × (E →L[ℝ] ℝ)} {p : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T s : ℝ}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
      t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hT : 0 < T) (hs : ι s ∈ closedBall p r) :
    variationPhase (hamiltonianPositionVariation Φ ι) (s, t₀) = e.symm (ι s) := by
  rw [variationPhase_hamiltonianPositionVariation he hΦ hmap hs
    (show t₀ ∈ Ioo (t₀ - T) (t₀ + T) from ⟨by linarith, by linarith⟩),
    hΦ.apply_initial (ι s) hs]

end OTSelector.Geometry
