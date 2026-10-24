import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import OTSelector.Analysis.Calculus.DensityOneDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.EikonalDensityJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.EikonalDensityJet`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual covector field satisfies the energy constraint on a density-one set and has the stated derivative at the point.

Objects: Vanishing derivative of the energy graph and first-jet preservation by energy normalization at energy one-half.

Proof detail: Use density-one derivative uniqueness on the constant energy graph, then differentiate (2K)^(-1/2)p and cancel the scalar derivative.

Sources: D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Matias Dahl, Section 7, Definition 7.3 and Proposition 7.4, p. 31; Section 7.2, Propositions 7.14–7.15, p. 35 (https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31).
Relation: Pointwise eikonal jet consequence; it assumes no global energy equation off the density-one constraint set.
-/

/-!
# Eikonal first jets at genuine density-one points

For a differentiable covector field, an energy constraint on a density-one set forces
the actual differential of the energy graph to vanish. Consequently normalizing the
field by the inverse square root of twice its energy preserves its entire first jet
at a point of energy one half. These are pointwise statements requiring no open-set
eikonal identity and no global smoothness of the energy or the covector field.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- A constant energy on a genuine density-one set forces its actual derivative
along the covector graph to vanish at that point. -/
theorem energyGraph_differential_eq_zero_of_density_one
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {K : (E × (E →L[ℝ] ℝ)) → ℝ} {p : E → E →L[ℝ] ℝ}
    {D : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hK : HasFDerivAt K D (x, p x)) (hp : HasFDerivAt p B x)
    {c : ℝ} (heq : ∀ y ∈ s, K (y, p y) = c) :
    D.comp ((ContinuousLinearMap.id ℝ E).prod B) = 0 := by
  apply hasFDerivAt_eq_zero_of_density_one μ hx (hK.comp x ((hasFDerivAt_id x).prodMk hp))
  intro y hy
  exact (heq y hy).trans (heq x hxs).symm

/-- The energy graph has zero actual Frechet derivative at the density-one point. -/
theorem hasFDerivAt_energyGraph_zero_of_density_one
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {K : (E × (E →L[ℝ] ℝ)) → ℝ} {p : E → E →L[ℝ] ℝ}
    {D : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hK : HasFDerivAt K D (x, p x)) (hp : HasFDerivAt p B x)
    {c : ℝ} (heq : ∀ y ∈ s, K (y, p y) = c) :
    HasFDerivAt (fun y ↦ K (y, p y)) (0 : E →L[ℝ] ℝ) x := by
  have h := hK.comp x ((hasFDerivAt_id x).prodMk hp)
  rwa [energyGraph_differential_eq_zero_of_density_one μ hx hxs hK hp heq] at h

/-- The rough eikonal first-jet identity holds in every direction, using the actual
energy differential and actual derivative of the covector field. -/
theorem energyGraph_direction_eq_zero_of_density_one
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {K : (E × (E →L[ℝ] ℝ)) → ℝ} {p : E → E →L[ℝ] ℝ}
    {D : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hK : HasFDerivAt K D (x, p x)) (hp : HasFDerivAt p B x)
    {c : ℝ} (heq : ∀ y ∈ s, K (y, p y) = c) (v : E) : D (v, B v) = 0 := by
  have h := congrArg (fun A : E →L[ℝ] ℝ ↦ A v)
    (energyGraph_differential_eq_zero_of_density_one μ hx hxs hK hp heq)
  simpa using h

/-- Normalizing an actual covector field by the square root of twice its energy
preserves its value and full derivative at a density-one point of energy one half. -/
theorem normalizedEnergyCovector_firstJet_of_density_one
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {K : (E × (E →L[ℝ] ℝ)) → ℝ} {p : E → E →L[ℝ] ℝ}
    {D : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hK : HasFDerivAt K D (x, p x)) (hp : HasFDerivAt p B x)
    (heq : ∀ y ∈ s, K (y, p y) = (1 / 2 : ℝ)) :
    let n : E → E →L[ℝ] ℝ := fun y ↦ (Real.sqrt (2 * K (y, p y)))⁻¹ • p y
    n x = p x ∧ HasFDerivAt n B x := by
  have hc : 2 * K (x, p x) = 1 := by rw [heq x hxs]; norm_num
  have hq := hasFDerivAt_energyGraph_zero_of_density_one μ hx hxs hK hp heq
  have htwo : HasFDerivAt (fun y ↦ 2 * K (y, p y)) (0 : E →L[ℝ] ℝ) x := by
    simpa only [Pi.smul_apply, smul_eq_mul, smul_zero] using! hq.const_smul (2 : ℝ)
  have hsqrt : HasFDerivAt (fun y ↦ Real.sqrt (2 * K (y, p y))) (0 : E →L[ℝ] ℝ) x := by
    simpa only [smul_zero] using htwo.sqrt (by rw [hc]; exact one_ne_zero)
  have hroot : Real.sqrt (2 * K (x, p x)) = 1 := by rw [hc, Real.sqrt_one]
  have hinv : HasFDerivAt (fun y ↦ (Real.sqrt (2 * K (y, p y)))⁻¹)
      (0 : E →L[ℝ] ℝ) x := by
    simpa only [smul_zero, Function.comp_apply] using!
      (hasDerivAt_inv (by rw [hroot]; exact one_ne_zero)).comp_hasFDerivAt x hsqrt
  constructor
  · simp only [hroot, inv_one, one_smul]
  · simpa only [Pi.smul_apply, hroot, inv_one, one_smul,
      ContinuousLinearMap.zero_smulRight, add_zero] using! hinv.smul hp

end OTSelector.Geometry

end
end
