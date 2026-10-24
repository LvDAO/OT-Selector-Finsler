import OTSelector.Analysis.Calculus.EikonalDensityJet
import OTSelector.Analysis.Calculus.SecondJetPolynomial
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SmoothEikonalJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SmoothEikonalJet`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual rough second jet and the density-one energy differential identity at its center.

Objects: A smooth polynomial with the same two-jet and a normalized smooth covector seed with the same first phase jet.

Proof detail: Construct the jet polynomial, transfer the energy graph derivative at the center and differentiate its scalar normalization.

Sources: Hassler Whitney, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Matias Dahl, Section 7, Definition 7.3 and Proposition 7.4, p. 31; Section 7.2, Propositions 7.14–7.15, p. 35 (https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31).
Relation: Pointwise smooth jet replacement. The polynomial is not asserted to solve the eikonal equation away from the center.
-/

/-!
# Normalizing a smooth potential while preserving its rough second jet

Realize the actual second jet by the explicit smooth polynomial. The density-one energy
identity is used only for the original rough covector field. Its vanishing energy-graph
differential transfers to the polynomial graph through their identical first jets.
Normalizing the polynomial differential therefore preserves its central value and
full derivative. No energy identity on a density-one set is asserted for the polynomial.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At energy one half, a vanishing actual energy-graph derivative makes normalization
preserve the entire covector first jet. No density-set or neighborhood energy identity
is needed for this purely pointwise calculus step. -/
theorem normalizedEnergyCovector_firstJet_of_energyGraph_zero
    {K : (E × (E →L[ℝ] ℝ)) → ℝ} {q : E → E →L[ℝ] ℝ}
    {x : E} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hq : HasFDerivAt q B x) (henergy : K (x, q x) = (1 / 2 : ℝ))
    (hzero : HasFDerivAt (fun y ↦ K (y, q y)) (0 : E →L[ℝ] ℝ) x) :
    let n : E → E →L[ℝ] ℝ := fun y ↦ (Real.sqrt (2 * K (y, q y)))⁻¹ • q y
    n x = q x ∧ HasFDerivAt n B x := by
  have hc : 2 * K (x, q x) = 1 := by rw [henergy]; norm_num
  have htwo : HasFDerivAt (fun y ↦ 2 * K (y, q y)) (0 : E →L[ℝ] ℝ) x := by
    simpa only [Pi.smul_apply, smul_eq_mul, smul_zero] using! hzero.const_smul (2 : ℝ)
  have hsqrt : HasFDerivAt (fun y ↦ Real.sqrt (2 * K (y, q y)))
      (0 : E →L[ℝ] ℝ) x := by
    simpa only [smul_zero] using htwo.sqrt (by rw [hc]; exact one_ne_zero)
  have hroot : Real.sqrt (2 * K (x, q x)) = 1 := by rw [hc, Real.sqrt_one]
  have hinv : HasFDerivAt (fun y ↦ (Real.sqrt (2 * K (y, q y)))⁻¹)
      (0 : E →L[ℝ] ℝ) x := by
    simpa only [smul_zero, Function.comp_apply] using!
      (hasDerivAt_inv (by rw [hroot]; exact one_ne_zero)).comp_hasFDerivAt x hsqrt
  constructor
  · simp only [hroot, inv_one, one_smul]
  · simpa only [Pi.smul_apply, hroot, inv_one, one_smul,
      ContinuousLinearMap.zero_smulRight, add_zero] using! hinv.smul hq

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- A genuine rough second jet satisfying the energy constraint on a density-one set
has a globally smooth representative whose normalized differential has exactly that
same first jet. The density argument applies to the rough field, and the resulting
zero derivative transfers to the smooth graph by its already proved jet identities. -/
theorem exists_smooth_normalized_secondJet_of_density_one
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hsecond : HasFDerivAt f' B x)
    {K : (E × (E →L[ℝ] ℝ)) → ℝ} {D : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ}
    (hK : HasFDerivAt K D (x, f' x))
    (heq : ∀ y ∈ s, K (y, f' y) = (1 / 2 : ℝ)) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = f x ∧
      HasFDerivAt P (f' x) x ∧ HasFDerivAt (fderiv ℝ P) B x ∧
      fderiv ℝ P x = fderiv ℝ f x ∧
      fderiv ℝ (fderiv ℝ P) x = fderiv ℝ (fderiv ℝ f) x ∧
      HasFDerivAt (fun y ↦ K (y, fderiv ℝ P y)) (0 : E →L[ℝ] ℝ) x ∧
      let n : E → E →L[ℝ] ℝ := fun y ↦
        (Real.sqrt (2 * K (y, fderiv ℝ P y)))⁻¹ • fderiv ℝ P y
      n x = f' x ∧ HasFDerivAt n B x := by
  obtain ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂⟩ :=
    exists_smooth_matching_secondJet hfirst hsecond
  have hzero := energyGraph_differential_eq_zero_of_density_one μ hx hxs hK hsecond heq
  have hKP : HasFDerivAt K D (x, fderiv ℝ P x) := by
    rw [hD.fderiv]
    exact hK
  have hgraph : HasFDerivAt (fun y ↦ K (y, fderiv ℝ P y))
      (0 : E →L[ℝ] ℝ) x := by
    have h := hKP.comp x ((hasFDerivAt_id x).prodMk hD₂)
    rwa [hzero] at h
  have henergy : K (x, fderiv ℝ P x) = (1 / 2 : ℝ) := by
    rw [hD.fderiv]
    exact heq x hxs
  obtain ⟨hvalue, hnorm⟩ :=
    normalizedEnergyCovector_firstJet_of_energyGraph_zero hD₂ henergy hgraph
  exact ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂, hgraph,
    hvalue.trans hD.fderiv, hnorm⟩

end OTSelector.Geometry

end
end
