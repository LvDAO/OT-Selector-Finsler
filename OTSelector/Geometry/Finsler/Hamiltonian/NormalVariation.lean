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
import OTSelector.Analysis.Calculus.VariationDerivatives
import OTSelector.Analysis.CompactParameterIntegral
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.C2Variation
import OTSelector.Geometry.Finsler.Variation.Lagrangian

/-!
## Lemma skeleton

* **Conditions:** A C2 scalar Lagrangian on an open phase domain and a C2 two-parameter variation with equal energy throughout an open variation domain; its central curve satisfies the actual Euler–Lagrange equation. Finsler conservation helpers instead assume an actual admissible local Hamiltonian flow.
* **Objects:** The actual action on a segment and the endpoint values of the momentum/variation-field pairing; constant-energy Finsler flow families.
* **Proof detail:** Equal family energy makes action locally constant. Apply the proved first-variation boundary formula and Euler–Lagrange equation, giving equal endpoint momentum pairings; reverse endpoints for either time direction. Hamiltonian conservation supplies the equal-family-energy premise from constant initial energy.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, p. 238, equations (8.33)–(8.36); Problem 8.7, p. 241.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 7, Definition 7.3 and Proposition 7.4, p. 31; Section 7.2, Propositions 7.14–7.15, p. 35.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31

**Relationship to the sources:** The endpoint identity is a locally derived corollary of first variation, not a textbook Gauss lemma imported as a hypothesis. Generic normed-space and either-time versions extend the finite-dimensional fixed-endpoint exposition.
-/

/-!
# Equal-energy variations and actual Finsler Hamiltonian energy

Equal actual energy on an open variation domain makes the action locally constant.
For a C2 variation whose central curve satisfies the true Euler--Lagrange equation,
the first-variation formula therefore equates the two actual endpoint momentum
pairings. Swapping the endpoints covers either time orientation; zero initial pairing
propagates to every endpoint of the segment.

For the original smooth strongly convex Finsler energy, conservation along an actual
local Hamiltonian flow identifies the energy with that of its inverse Legendre initial
state. Constant initial energy consequently supplies the equal-family-energy premise.
The conservation helpers require no regularity of the initial-state curve. No inner
product, finite dimensionality, normal-coordinate assumption or pairing identity is
supplied to the endpoint theorem.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equal actual energy on an open neighborhood of a compact central trace makes
the actual action locally constant in the variation parameter. -/
theorem eventuallyEq_lagrangianAction_const_of_energy
    {L : E × E → ℝ} {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) {s₀ a b E₀ : ℝ}
    (htrace : ∀ t ∈ uIcc a b, (s₀, t) ∈ D)
    (henergy : ∀ q ∈ D, L (variationPhase σ q) = E₀) :
    lagrangianAction L σ a b =ᶠ[𝓝 s₀] (fun _ ↦ (b - a) * E₀) := by
  obtain ⟨r, hr, hstrip⟩ :=
    exists_pos_compact_parameter_strip (a := min a b) (b := max a b) hD htrace
  have hparam : Icc (s₀ - r) (s₀ + r) ∈ 𝓝 s₀ :=
    Icc_mem_nhds (by linarith) (by linarith)
  filter_upwards [hparam] with s hs
  change (∫ t in a..b, L (variationPhase σ (s, t))) = (b - a) * E₀
  calc
    _ = ∫ _ in a..b, E₀ := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact henergy (s, t) (hstrip ⟨hs, ht⟩)
    _ = (b - a) * E₀ := by simp

/-- For an increasing time segment, equal actual energy and the central
Euler--Lagrange equation equate the actual endpoint momentum pairings. -/
theorem fiberLegendre_variationField_eq_of_equal_energy_of_le
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b E₀ : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b, variationPhase σ (s₀, t) ∈ U)
    (hEL : ∀ t ∈ Icc a b, HasDerivAt
      (fun u ↦ fiberLegendre L (variationPhase σ (s₀, u)))
      (baseEnergyDifferential L (variationPhase σ (s₀, t))) t)
    (henergy : ∀ q ∈ D, L (variationPhase σ q) = E₀) :
    fiberLegendre L (variationPhase σ (s₀, b)) (variationField σ s₀ b) =
      fiberLegendre L (variationPhase σ (s₀, a)) (variationField σ s₀ a) := by
  have hconst := eventuallyEq_lagrangianAction_const_of_energy (s₀ := s₀) (a := a) (b := b) hD
    (by simpa only [uIcc_of_le hab] using htrace) henergy
  have hderiv : HasDerivAt (lagrangianAction L σ a b) 0 s₀ :=
    (hasDerivAt_const s₀ ((b - a) * E₀)).congr_of_eventuallyEq hconst
  have hzero : (∫ t in a..b,
      (baseEnergyDifferential L (variationPhase σ (s₀, t)) -
        deriv (fun u ↦ fiberLegendre L (variationPhase σ (s₀, u))) t)
          (variationField σ s₀ t)) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [(hEL t ((uIcc_of_le hab) ▸ ht)).deriv]
        simp
      _ = 0 := by simp
  have hfirst := hasDerivAt_lagrangianAction_firstVariation hU hL hD hσ hab htrace hphase
  rw [hzero, add_zero] at hfirst
  exact sub_eq_zero.mp (hfirst.unique hderiv)

/-- Equal-energy variations of a genuine Euler--Lagrange curve preserve the
endpoint momentum pairing in either time orientation. -/
theorem fiberLegendre_variationField_eq_of_equal_energy
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b E₀ : ℝ}
    (htrace : ∀ t ∈ uIcc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ uIcc a b, variationPhase σ (s₀, t) ∈ U)
    (hEL : ∀ t ∈ uIcc a b, HasDerivAt
      (fun u ↦ fiberLegendre L (variationPhase σ (s₀, u)))
      (baseEnergyDifferential L (variationPhase σ (s₀, t))) t)
    (henergy : ∀ q ∈ D, L (variationPhase σ q) = E₀) :
    fiberLegendre L (variationPhase σ (s₀, b)) (variationField σ s₀ b) =
      fiberLegendre L (variationPhase σ (s₀, a)) (variationField σ s₀ a) := by
  rcases le_total a b with hab | hba
  · exact fiberLegendre_variationField_eq_of_equal_energy_of_le hU hL hD hσ hab
      (by simpa only [uIcc_of_le hab] using htrace)
      (by simpa only [uIcc_of_le hab] using hphase)
      (by simpa only [uIcc_of_le hab] using hEL) henergy
  · exact (fiberLegendre_variationField_eq_of_equal_energy_of_le hU hL hD hσ hba
      (by simpa only [uIcc_of_ge hba] using htrace)
      (by simpa only [uIcc_of_ge hba] using hphase)
      (by simpa only [uIcc_of_ge hba] using hEL) henergy).symm

/-- A zero initial momentum pairing propagates along an equal-energy variation
of a genuine Euler--Lagrange curve, with either time orientation. -/
theorem fiberLegendre_variationField_eq_zero_of_equal_energy
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b E₀ : ℝ}
    (htrace : ∀ t ∈ uIcc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ uIcc a b, variationPhase σ (s₀, t) ∈ U)
    (hEL : ∀ t ∈ uIcc a b, HasDerivAt
      (fun u ↦ fiberLegendre L (variationPhase σ (s₀, u)))
      (baseEnergyDifferential L (variationPhase σ (s₀, t))) t)
    (henergy : ∀ q ∈ D, L (variationPhase σ q) = E₀)
    (hzero : fiberLegendre L (variationPhase σ (s₀, a)) (variationField σ s₀ a) = 0) :
    fiberLegendre L (variationPhase σ (s₀, b)) (variationField σ s₀ b) = 0 :=
  (fiberLegendre_variationField_eq_of_equal_energy hU hL hD hσ htrace hphase hEL henergy).trans
    hzero

variable
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- The actual Finsler energy of a Hamiltonian position variation equals the energy
of its genuine inverse Legendre initial state. -/
theorem chartEnergy_hamiltonianPositionVariation_eq_initial (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsource : e.source ⊆ chartEnergyDomain x₀)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : ℝ → E × (E →L[ℝ] ℝ)} {p : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T s t : ℝ}
    (hΦ : LocalFlow.IsLocalFlow
      (fun _ ↦ localHamiltonianVectorField (F.chartEnergy x₀) e)
      t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hT : 0 < T) (hs : ι s ∈ closedBall p r)
    (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    F.chartEnergy x₀ (variationPhase (hamiltonianPositionVariation Φ ι) (s, t)) =
      F.chartEnergy x₀ (e.symm (ι s)) := by
  have ht₀ : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  have henergy := hF.chartEnergy_eq_of_integralCurve x₀ he hsource hG
    (γ := fun u ↦ Φ (ι s, u)) isOpen_Ioo
    (convex_Ioo (t₀ - T) (t₀ + T)).isPreconnected
    (fun u hu ↦ hmap ⟨hs, Ioo_subset_Icc_self hu⟩)
    (fun u hu ↦ hasDerivAt_hamiltonianFlow_slice hΦ hs hu) ht ht₀
  change F.chartEnergy x₀ (variationPhase (hamiltonianPositionVariation Φ ι) (s, t)) =
    F.chartEnergy x₀ (variationPhase (hamiltonianPositionVariation Φ ι) (s, t₀)) at henergy
  rw [variationPhase_hamiltonianPositionVariation_initial he hΦ hmap hT hs] at henergy
  exact henergy

/-- Constant original Finsler energy on the inverse Legendre initial states gives
constant actual energy on the entire parameter-time product. -/
theorem chartEnergy_hamiltonianPositionVariation_eq_const (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsource : e.source ⊆ chartEnergyDomain x₀)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {ι : ℝ → E × (E →L[ℝ] ℝ)} {p : E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ} {S : Set ℝ} {E₀ : ℝ}
    (hΦ : LocalFlow.IsLocalFlow
      (fun _ ↦ localHamiltonianVectorField (F.chartEnergy x₀) e)
      t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hT : 0 < T) (hι : MapsTo ι S (closedBall p r))
    (henergy : ∀ s ∈ S, F.chartEnergy x₀ (e.symm (ι s)) = E₀) :
    ∀ q ∈ S ×ˢ Ioo (t₀ - T) (t₀ + T),
      F.chartEnergy x₀ (variationPhase (hamiltonianPositionVariation Φ ι) q) = E₀ := by
  intro q hq
  exact (hF.chartEnergy_hamiltonianPositionVariation_eq_initial x₀ he hsource hG
    hΦ hmap hT (hι hq.1) hq.2).trans (henergy q.1 hq.1)

end ContinuousFinslerNorm.IsSmoothStronglyConvex

end OTSelector.Geometry
