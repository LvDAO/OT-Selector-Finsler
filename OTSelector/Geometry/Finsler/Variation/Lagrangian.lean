import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import OTSelector.Analysis.Calculus.CovectorIntegrationByParts
import OTSelector.Analysis.Calculus.VariationDerivatives
import OTSelector.Analysis.CompactParameterIntegral
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance

/-!
## Lemma skeleton

* **Conditions:** A C2 Lagrangian and C2 variation whose compact time trace stays inside an open phase domain.
* **Objects:** The first variation of the action with covector boundary term and Euler–Lagrange interior residual.
* **Proof detail:** Differentiate the two-variable composition, commute mixed variation derivatives, move the parameter derivative under the compact integral and integrate by parts.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters).
  https://www.jirka.org/ra/html/sec_diffunderint.html
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 225E (absolutely continuous functions as indefinite integrals), 225F (integration by parts).
  https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29

**Relationship to the sources:** This is the directly proved covector-valued formulation of the standard action variation; complete normed-space and explicit open-domain hypotheses are retained.
-/

/-!
# First variation of the actual Lagrangian action

The variation has C2 regularity on an open neighborhood of a compact time segment.
Only the central position-velocity trace must lie in the open C2 energy domain;
continuity and compactness supply admissibility and domination for nearby parameters.
The velocity, variation field and momentum are all actual derivatives of the given data.

Mixed-partial symmetry and differentiation under the integral give the first formula.
Covector-vector integration by parts yields the endpoint terms and the residual
`D_x L - d/dt D_v L`. Genuine fixed-endpoint variations of an Euler--Lagrange solution
therefore have zero first action derivative. The model space is arbitrary real normed;
no inner product, finite dimensionality, strong convexity, supplied derivative bounds
or independent integrability premises are needed. Stationarity alone does not assert
energy or length minimization.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual position and time velocity of a two-parameter variation. -/
def variationPhase (σ : ℝ × ℝ → E) (z : ℝ × ℝ) : E × E :=
  (σ z, variationVelocity σ z)

/-- Integrate the original scalar Lagrangian along each actual varied curve. -/
def lagrangianAction (L : E × E → ℝ) (σ : ℝ × ℝ → E) (a b s : ℝ) : ℝ :=
  ∫ t in a..b, L (variationPhase σ (s, t))

/-- A C2 variation has a C1 actual position-velocity map. -/
theorem contDiffOn_variationPhase {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) :
    ContDiffOn ℝ 1 (variationPhase σ) D :=
  (hσ.of_le (by norm_num)).prodMk (contDiffOn_variationVelocity hD hσ)

/-- The parameter derivative of the original energy uses the actual variation field. -/
theorem hasDerivAt_lagrangianVariation
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ t : ℝ}
    (hz : (s₀, t) ∈ D) (hphase : variationPhase σ (s₀, t) ∈ U) :
    HasDerivAt (fun s ↦ L (variationPhase σ (s, t)))
      (baseEnergyDifferential L (variationPhase σ (s₀, t)) (variationField σ s₀ t) +
        fiberLegendre L (variationPhase σ (s₀, t)) (deriv (variationField σ s₀) t)) s₀ := by
  have hσat := (hσ.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
  have hx : HasDerivAt (fun s ↦ σ (s, t)) (variationField σ s₀ t) s₀ :=
    (hσat.comp s₀ (differentiableAt_id.prodMk (differentiableAt_const t))).hasDerivAt
  have hv := hasDerivAt_variationVelocity hD hσ hz
  have hLat := (hL.contDiffAt (hU.mem_nhds hphase)).differentiableAt (by norm_num)
  have hc := hLat.hasFDerivAt.comp_hasDerivAt s₀ (hx.prodMk hv)
  rw [fderiv_energy_split hLat] at hc
  exact hc

/-- First differentiation of the actual action on an open neighborhood of a compact segment. -/
theorem hasDerivAt_lagrangianAction
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b, variationPhase σ (s₀, t) ∈ U) :
    HasDerivAt (lagrangianAction L σ a b)
      (∫ t in a..b,
        baseEnergyDifferential L (variationPhase σ (s₀, t)) (variationField σ s₀ t) +
          fiberLegendre L (variationPhase σ (s₀, t)) (deriv (variationField σ s₀) t)) s₀ := by
  let O := D ∩ (variationPhase σ) ⁻¹' U
  have hQ := contDiffOn_variationPhase hD hσ
  have hO : IsOpen O := hQ.continuousOn.isOpen_inter_preimage hD hU
  have hf : ContDiffOn ℝ 1 (fun z ↦ L (variationPhase σ z)) O :=
    (hL.of_le (by norm_num)).comp (hQ.mono inter_subset_left) (fun _ hz ↦ hz.2)
  have h := hasDerivAt_intervalIntegral_of_contDiffOn hO hf hab
    (fun t ht ↦ ⟨htrace t ht, hphase t ht⟩)
  have heq : (∫ t in a..b, deriv (fun s ↦ L (variationPhase σ (s, t))) s₀) =
      ∫ t in a..b,
        baseEnergyDifferential L (variationPhase σ (s₀, t)) (variationField σ s₀ t) +
          fiberLegendre L (variationPhase σ (s₀, t)) (deriv (variationField σ s₀) t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (hasDerivAt_lagrangianVariation hU hL hD hσ (htrace t ht) (hphase t ht)).deriv
  rw [heq] at h
  exact h

/-- First variation of the actual action: endpoint pairing plus the Euler--Lagrange residual. -/
theorem hasDerivAt_lagrangianAction_firstVariation
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b, variationPhase σ (s₀, t) ∈ U) :
    HasDerivAt (lagrangianAction L σ a b)
      (fiberLegendre L (variationPhase σ (s₀, b)) (variationField σ s₀ b) -
        fiberLegendre L (variationPhase σ (s₀, a)) (variationField σ s₀ a) +
        ∫ t in a..b,
          (baseEnergyDifferential L (variationPhase σ (s₀, t)) -
            deriv (fun u ↦ fiberLegendre L (variationPhase σ (s₀, u))) t)
              (variationField σ s₀ t)) s₀ := by
  let O := D ∩ (variationPhase σ) ⁻¹' U
  have hQ := contDiffOn_variationPhase hD hσ
  have hO : IsOpen O := hQ.continuousOn.isOpen_inter_preimage hD hU
  let I : Set ℝ := {t | (s₀, t) ∈ O}
  have hI : IsOpen I := hO.preimage (continuous_const.prodMk continuous_id)
  have hsub : Icc a b ⊆ I := fun t ht ↦ ⟨htrace t ht, hphase t ht⟩
  let p := fun t ↦ fiberLegendre L (variationPhase σ (s₀, t))
  let B := fun t ↦ baseEnergyDifferential L (variationPhase σ (s₀, t))
  let W := variationField σ s₀
  have hQI : ContDiffOn ℝ 1 (fun t ↦ variationPhase σ (s₀, t)) I :=
    hQ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht ↦ ht.1)
  have hp : ContDiffOn ℝ 1 p I := by
    intro t ht
    exact ((contDiffAt_fiberLegendre_one_of_two
      (hL.contDiffAt (hU.mem_nhds ht.2))).comp t
        (hQI.contDiffAt (hI.mem_nhds ht))).contDiffWithinAt
  have hB : ContDiffOn ℝ 1 B I := by
    intro t ht
    exact ((contDiffAt_baseEnergyDifferential_one_of_two
      (hL.contDiffAt (hU.mem_nhds ht.2))).comp t
        (hQI.contDiffAt (hI.mem_nhds ht))).contDiffWithinAt
  have hW : ContDiffOn ℝ 1 W I :=
    (contDiffOn_variationField hD hσ s₀).mono (fun _ ht ↦ ht.1)
  have hBp : IntervalIntegrable (fun t ↦ B t (W t)) volume a b :=
    ((hB.continuousOn.clm_apply hW.continuousOn).mono hsub).intervalIntegrable_of_Icc hab
  have hpW : IntervalIntegrable (fun t ↦ p t (deriv W t)) volume a b :=
    ((hp.continuousOn.clm_apply (hW.continuousOn_deriv_of_isOpen hI le_rfl)).mono
      hsub).intervalIntegrable_of_Icc hab
  have hp'W : IntervalIntegrable (fun t ↦ deriv p t (W t)) volume a b :=
    (((hp.continuousOn_deriv_of_isOpen hI le_rfl).clm_apply hW.continuousOn).mono
      hsub).intervalIntegrable_of_Icc hab
  have hIBP := integral_covector_deriv_eq_boundary_sub_integral_deriv hI hab hsub hp hW
  have hres : (∫ t in a..b, (B t - deriv p t) (W t)) =
      (∫ t in a..b, B t (W t)) - ∫ t in a..b, deriv p t (W t) := by
    simp only [sub_apply]
    exact intervalIntegral.integral_sub hBp hp'W
  apply (hasDerivAt_lagrangianAction hU hL hD hσ hab htrace hphase).congr_deriv
  change (∫ t in a..b, B t (W t) + p t (deriv W t)) =
    p b (W b) - p a (W a) + ∫ t in a..b, (B t - deriv p t) (W t)
  rw [intervalIntegral.integral_add hBp hpW, hIBP, hres]
  ring

/-- Genuine fixed-endpoint variations of an Euler--Lagrange curve have stationary action. -/
theorem hasDerivAt_lagrangianAction_zero_of_eulerLagrange
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b, variationPhase σ (s₀, t) ∈ U)
    (hEL : ∀ t ∈ Icc a b, HasDerivAt
      (fun u ↦ fiberLegendre L (variationPhase σ (s₀, u)))
      (baseEnergyDifferential L (variationPhase σ (s₀, t))) t)
    (hfixed_a : (fun s ↦ σ (s, a)) =ᶠ[𝓝 s₀] (fun _ ↦ σ (s₀, a)))
    (hfixed_b : (fun s ↦ σ (s, b)) =ᶠ[𝓝 s₀] (fun _ ↦ σ (s₀, b))) :
    HasDerivAt (lagrangianAction L σ a b) 0 s₀ := by
  have ha : variationField σ s₀ a = 0 := by
    change deriv (fun s ↦ σ (s, a)) s₀ = 0
    rw [hfixed_a.deriv_eq]
    simp
  have hb : variationField σ s₀ b = 0 := by
    change deriv (fun s ↦ σ (s, b)) s₀ = 0
    rw [hfixed_b.deriv_eq]
    simp
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
  apply (hasDerivAt_lagrangianAction_firstVariation hU hL hD hσ hab htrace hphase).congr_deriv
  rw [ha, hb, hzero]
  simp

end OTSelector.Geometry
