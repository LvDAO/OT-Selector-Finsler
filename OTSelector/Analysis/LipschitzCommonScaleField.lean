import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import OTSelector.Finite.LatticePairCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CommonScalePhaseField.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CommonScalePhaseField`; the selected original proof blocks follow. -/
section

/-!
Conditions: A positive common position/momentum scaling and the stated actual field measurability or Lipschitz hypotheses.

Objects: Exact common-scale field/curve identities, preservation of Lipschitz constant and rescaling of node errors and physical phase equations.

Proof detail: Cancel the two scalar factors, use absolute homogeneity of norms and continuous-linear commutation with scalar multiplication.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Explicit scaling algebra; it changes no law and introduces no statistical normalization criterion.
-/

/-! Common position/momentum scaling preserves the original field Lipschitz
constant and rescales actual node error and physical phase identities exactly. -/
open Set Function MeasureTheory
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Position and momentum use the same deterministic positive phase scale. -/
def commonScalePhaseField (δ : ℝ) (P : V → V) (x : V) : V :=
  δ⁻¹ • P (δ • x)

/-- The literal old curve is scaled, without selecting a new inverse curve. -/
def commonScalePhaseCurve {I : Type*} (δ : ℝ) (γ : I → V) (r : I) : V := δ⁻¹ • γ r

theorem commonScalePhaseField_at_scaled {δ : ℝ} (hδ : 0 < δ) (P : V → V) (x : V) :
    commonScalePhaseField δ P (δ⁻¹ • x) = δ⁻¹ • P x := by
  simp only [commonScalePhaseField, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]

theorem commonScalePhaseField_zero (δ : ℝ) (P : V → V) :
    commonScalePhaseField δ P 0 = δ⁻¹ • P 0 := by simp [commonScalePhaseField]

theorem measurable_commonScalePhaseField
    [MeasurableSpace V] [BorelSpace V] {Ω : Type*} [MeasurableSpace Ω]
    {P : Ω → V → V} (hP : Measurable (uncurry P)) (δ : ℝ) :
    Measurable (fun a : Ω × V ↦ commonScalePhaseField δ (P a.1) a.2) := by
  have hs : Measurable (fun a : Ω × V ↦ (a.1, δ • a.2)) :=
    measurable_fst.prodMk (((continuous_const.smul continuous_id).measurable).comp measurable_snd)
  exact (continuous_const.smul continuous_id).measurable.comp (hP.comp hs)

/-- The same global norm Lipschitz bound holds after common phase scaling. -/
theorem commonScalePhaseField_norm_lipschitz {δ L : ℝ} (hδ : 0 < δ) {P : V → V}
    (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖commonScalePhaseField δ P x - commonScalePhaseField δ P y‖ ≤ L * ‖x - y‖ := by
  intro x y
  have h := mul_le_mul_of_nonneg_left (hP (δ • x) (δ • y)) (inv_nonneg.mpr hδ.le)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at h
  have key : δ⁻¹ * (L * (δ * ‖x - y‖)) = L * ‖x - y‖ := by
    field_simp [hδ.ne']
  calc
    ‖commonScalePhaseField δ P x - commonScalePhaseField δ P y‖
        = δ⁻¹ * ‖P (δ • x) - P (δ • y)‖ := by
          simp only [commonScalePhaseField, ← smul_sub, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hδ)]
    _ ≤ δ⁻¹ * (L * (δ * ‖x - y‖)) := h
    _ = L * ‖x - y‖ := key

theorem lipschitzWith_commonScalePhaseField {δ : ℝ} (hδ : 0 < δ) {L : ℝ≥0}
    {P : V → V} (hP : LipschitzWith L P) :
    LipschitzWith L (commonScalePhaseField δ P) := by
  apply LipschitzWith.of_dist_le_mul
  simpa only [dist_eq_norm] using
    commonScalePhaseField_norm_lipschitz hδ (fun x y ↦ by
      simpa only [dist_eq_norm] using hP.dist_le_mul x y)

/-- An actual node error is divided by the same physical phase scale. -/
theorem commonScalePhaseField_node_error {δ b : ℝ} (hδ : 0 < δ)
    (P : V → V) {z p : V} (hnode : ‖p - P z‖ ≤ b) :
    ‖δ⁻¹ • p - commonScalePhaseField δ P (δ⁻¹ • z)‖ ≤ b / δ := by
  rw [commonScalePhaseField_at_scaled hδ, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hδ)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hnode (inv_nonneg.mpr hδ.le)

/-- The unchanged physical phase relation scales literally, including its mobility. -/
theorem commonScalePhase_physical_identity (δ : ℝ) (R : V →L[ℝ] V) (z p : V) :
    δ⁻¹ • z + R (δ⁻¹ • p) = δ⁻¹ • (z + R p) := by
  simp only [map_smul, smul_add]

/-- The doubled coordinate vector uses the same common scalar on both components. -/
theorem phasePairVector_common_smul {q : ℕ} (a : ℝ) (z p : Fin q → ℝ) :
    phasePairVector (a • z) (a • p) = a • phasePairVector z p := by
  funext i
  simp only [phasePairVector, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> rfl

theorem commonScalePhaseCurve_norm {I : Type*} {δ : ℝ} (hδ : 0 < δ)
    (γ : I → V) (r : I) :
    ‖commonScalePhaseCurve δ γ r‖ = ‖γ r‖ / δ := by
  rw [commonScalePhaseCurve, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
  ring

theorem commonScalePhaseCurve_sub_norm {I : Type*} {δ : ℝ} (hδ : 0 < δ)
    (γ : I → V) (r s : I) :
    ‖commonScalePhaseCurve δ γ r - commonScalePhaseCurve δ γ s‖ = ‖γ r - γ s‖ / δ := by
  rw [commonScalePhaseCurve, commonScalePhaseCurve, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
  ring

end OTSelector.Reconstruction

end
end
