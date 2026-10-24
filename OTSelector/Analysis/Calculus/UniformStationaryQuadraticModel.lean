import OTSelector.Analysis.Calculus.QuadraticExpansionUniqueness
import OTSelector.Analysis.Calculus.UniformStationaryCompositionJet
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformStationaryQuadraticModel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformStationaryQuadraticModel`; the selected original proof blocks follow. -/
section

/-!
Conditions: A degree-two homogeneous pointwise model and two state germs with the same actual first jet, in the stated stationary action family.

Objects: Transfer and uniqueness of the uniform compact quadratic model.

Proof detail: Subtract Taylor expansions, apply same-first-jet quadratic transfer and evaluate homogeneous differences along shrinking scalar lines.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37).
Relation: Locally proved homogeneous-model uniqueness/transfer; the model is explicit and is not selected by a statistical criterion.
-/

/-!
# Uniform stationary models from matching actual first jets

A homogeneous pointwise quadratic coefficient of one state germ determines the
uniform compact-parameter coefficient for every germ sharing its first jet.
-/

open Set Filter Asymptotics
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry
variable {P Z W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A pointwise homogeneous quadratic model of one state germ is the uniform model
of every other germ with the same value and first derivative. -/
theorem uniform_stationary_composition_of_shared_jet_model
    {f : P × Z → ℝ} {T : Set P} (hT : IsCompact T) {z₀ : Z}
    (hf : ∀ p ∈ T, ContDiffAt ℝ 3 f (p, z₀))
    (hstationary : ∀ p ∈ T, HasFDerivAt (fun z ↦ f (p, z)) (0 : Z →L[ℝ] ℝ) z₀)
    {X Y : W → Z} {D : W →L[ℝ] Z}
    (hX : HasFDerivAt X D 0) (hX₀ : X 0 = z₀)
    (hY : HasFDerivAt Y D 0) (hY₀ : Y 0 = z₀)
    {q : P → W → ℝ}
    (hq : ∀ p ∈ T, ∀ (a : ℝ) (w : W), q p (a • w) = a ^ 2 * q p w)
    (hmodel : ∀ p ∈ T,
      (fun w ↦ f (p, Y w) - f (p, z₀) - q p w) =o[𝓝 (0 : W)] fun w ↦ ‖w‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ p ∈ T, ∀ w, ‖w‖ < r →
      ‖f (p, X w) - f (p, z₀) - q p w‖ ≤ ε * ‖w‖ ^ 2 := by
  let B : P → W → ℝ := fun p w ↦
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (p, z₀) (0, D w) (0, D w)
  have hB (p : P) (a : ℝ) (w : W) : B p (a • w) = a ^ 2 * B p w := by
    have hd : ((0, D (a • w)) : P × Z) = a • (0, D w) := by simp
    dsimp only [B]
    rw [hd, map_smul]
    simp only [smul_apply, map_smul, smul_eq_mul]
    ring
  have hboundY := uniform_parameterized_stationary_composition_of_hasFDerivAt
    hT hf hstationary hY hY₀
  have heq (p : P) (hp : p ∈ T) : ∀ w, B p w = q p w := by
    apply quadratic_expansion_unique (hB p) (hq p hp) ?_ (hmodel p hp)
    apply isLittleO_norm_sq_of_remainder_bound
    intro ε hε
    obtain ⟨r, hr, hb⟩ := hboundY ε hε
    exact ⟨r, hr, fun w hw ↦ hb p hp w hw⟩
  intro ε hε
  obtain ⟨r, hr, hb⟩ := uniform_parameterized_stationary_composition_of_hasFDerivAt
    hT hf hstationary hX hX₀ ε hε
  refine ⟨r, hr, ?_⟩
  intro p hp w hw
  have hh := hb p hp w hw
  change ‖f (p, X w) - f (p, z₀) - B p w‖ ≤ _ at hh
  rwa [heq p hp w] at hh

end OTSelector.Geometry

end
end
