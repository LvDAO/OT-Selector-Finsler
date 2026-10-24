import OTSelector.Analysis.Calculus.CompactUniformFirstJet
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CompactUniformLabelJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CompactUniformLabelJet`; the selected original proof blocks follow. -/
section

/-!
Conditions: A family is C1 near a compact parameter slice at label zero with the stated joint derivative continuity.

Objects: A uniform linear bound and common o(label) first-order remainder.

Proof detail: Thicken the compact slice, bound the label derivative and use its uniform continuity in a mean-value estimate.

Sources: Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Compact-uniform first-order Taylor consequence; external parameters need only the actual continuity hypotheses.
-/

/-!
# Uniform label derivatives of a compact C1 family

The actual derivative in the label variable has a common linear bound and a
uniform first-order remainder on compact parameter sets. Parameters are frozen
when labels move; their dependence on any external index need only be continuous.
-/

open Set
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A joint C1 map supplies uniform linear control and the actual label derivative
on a compact parameter set, without finite-dimensionality or convexity. -/
theorem exists_uniform_label_firstJet
    {g : P × W → Z} {U : Set (P × W)} {K : Set P}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (hK : IsCompact K)
    (hKU : ∀ p ∈ K, (p, (0 : W)) ∈ U) :
    let D : P → W →L[ℝ] Z := fun p ↦
      (fderiv ℝ g (p, 0)).comp (ContinuousLinearMap.inr ℝ P W)
    (∃ A ≥ 0, ∃ R > 0, ∀ p ∈ K, ∀ w : W, ‖w‖ < R →
      (p, w) ∈ U ∧ ‖g (p, w) - g (p, 0)‖ ≤ A * ‖w‖ ∧ ‖D p w‖ ≤ A * ‖w‖) ∧
    ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ p ∈ K, ∀ w : W, ‖w‖ < r →
      ‖g (p, w) - g (p, 0) - D p w‖ ≤ η * ‖w‖ := by
  let C := (fun p : P ↦ (p, (0 : W))) '' K
  have hC : IsCompact C := hK.image (continuous_id.prodMk continuous_const)
  have hCU : C ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hKU p hp
  have hD : ContinuousOn (fderiv ℝ g) C :=
    (hg.continuousOn_fderiv_of_isOpen hU (by rfl)).mono hCU
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hD
  let A := max B 0 + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrem : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ p ∈ K, ∀ w : W, ‖w‖ < r →
      (p, w) ∈ U ∧
        ‖g (p, w) - g (p, 0) - (fderiv ℝ g (p, 0)) (0, w)‖ ≤ η * ‖w‖ := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := exists_uniform_firstOrder_remainder_of_contDiffOn
      hU hg hC hCU hη
    refine ⟨r, hr, ?_⟩
    intro p hp w hw
    simpa using hb (p, 0) (mem_image_of_mem _ hp) (0, w) (by simpa using hw)
  dsimp only
  refine ⟨?_, ?_⟩
  · obtain ⟨R, hR, hb⟩ := hrem 1 zero_lt_one
    refine ⟨A, hA, R, hR, ?_⟩
    intro p hp w hw
    have hDw : ‖(fderiv ℝ g (p, 0)) (0, w)‖ ≤ max B 0 * ‖w‖ := by
      calc
        _ ≤ ‖fderiv ℝ g (p, 0)‖ * ‖((0 : P), w)‖ :=
          (fderiv ℝ g (p, 0)).le_opNorm _
        _ ≤ max B 0 * ‖w‖ := by
          simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg w)]
          exact mul_le_mul_of_nonneg_right
            ((hB _ (mem_image_of_mem _ hp)).trans (le_max_left _ _)) (norm_nonneg _)
    have hm := hb p hp w hw
    refine ⟨hm.1, ?_, ?_⟩
    · calc
        _ ≤ ‖g (p, w) - g (p, 0) - (fderiv ℝ g (p, 0)) (0, w)‖ +
            ‖(fderiv ℝ g (p, 0)) (0, w)‖ := norm_le_norm_sub_add _ _
        _ ≤ 1 * ‖w‖ + max B 0 * ‖w‖ := add_le_add hm.2 hDw
        _ = A * ‖w‖ := by dsimp [A]; ring
    · exact hDw.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
  · intro η hη
    obtain ⟨r, hr, hb⟩ := hrem η hη
    exact ⟨r, hr, fun p hp w hw ↦ (hb p hp w hw).2⟩

end OTSelector.Geometry

end
end
