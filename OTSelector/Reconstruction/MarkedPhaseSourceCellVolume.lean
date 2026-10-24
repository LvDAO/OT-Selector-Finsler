import OTSelector.MeasureTheory.LinearPhaseCell
import OTSelector.Reconstruction.PhaseSourceCellPullback
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
Conditions: An invertible matrix, positive-semidefinite mobility, nonnegative radius and vectors in the given norm balls.

Objects: An explicit marked linear-phase cell and containment of the actual transformed position.

Proof detail: Apply the previously proved (1+U) inverse norm bound to z−Up and insert the actual affine cell definition.

Sources: Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Explicit phase-cell definition and membership algebra. No volume/intensity conclusion from the original file is included.
-/

/-!
# Original marked source-cell volume from the actual leg determinant

The marked envelope is defined by a Borel inverse-compliance inequality. Its
physical product-intensity is exactly the integrated original determinant, even
when its spatial extent is unbounded near an original clock endpoint.
-/
open Set Function Matrix MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



private theorem measurable_matrixInverse {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix ι ι ℝ} (hA : Measurable A) : Measurable (fun x ↦ (A x)⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((continuous_id.matrix_det.measurable.comp hA).inv).smul
    (continuous_id.matrix_adjugate.measurable.comp hA)

/-- The source envelope is a fixed measurable original point set, before observing any matching. -/
theorem measurableSet_markedPhaseSourceCell
    (L : Matrix ι ι ℝ) {U : ℝ → Matrix ι ι ℝ} (hU : Measurable U)
    {c : ℝ → (ι → ℝ)} (hc : Measurable c) {B : Set ℝ} (hB : MeasurableSet B) (R : ℝ) :
    MeasurableSet (markedPhaseSourceCell L U c B R) := by
  have hsum : Measurable (fun a ↦ (1 : Matrix ι ι ℝ) + U a) := by
    apply Measurable.of_eval_matrix
    intro i j
    exact measurable_const.add (hU.eval.eval)
  have hA : Measurable (fun v : (ι → ℝ) × ℝ ↦ (1 + U v.2)⁻¹) :=
    measurable_matrixInverse (hsum.comp measurable_snd)
  have hx : Measurable (fun v : (ι → ℝ) × ℝ ↦ L⁻¹ *ᵥ (v.1 - c v.2)) := by
    exact (Matrix.toLin' L⁻¹).continuous_of_finiteDimensional.measurable.comp
      (measurable_fst.sub (hc.comp measurable_snd))
  have hm : Measurable (fun v : (ι → ℝ) × ℝ ↦
      (1 + U v.2)⁻¹ *ᵥ (L⁻¹ *ᵥ (v.1 - c v.2))) := by
    apply measurable_pi_lambda
    intro i
    exact Finset.measurable_sum _ (fun j _ ↦ (hA.eval.eval).mul (hx.eval))
  exact (hB.preimage measurable_snd).inter (measurableSet_le hm.norm measurable_const)

/-- A fixed mark section is exactly a translate of the compact linear phase envelope. -/
theorem section_markedPhaseSourceCell
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hU : ∀ a, (U a).PosSemidef) (c : ℝ → (ι → ℝ)) (B : Set ℝ) (R a : ℝ) :
    (fun x : ι → ℝ ↦ (x, a)) ⁻¹' markedPhaseSourceCell L U c B R =
      if a ∈ B then (fun x ↦ c a + x) '' ((Matrix.toLin' L) '' phaseSourceCell (U a) R)
      else ∅ := by
  classical
  by_cases ha : a ∈ B
  · rw [ite_eq_left ha]
    ext x
    change (a ∈ B ∧ _) ↔ _
    rw [and_iff_right ha, ← mem_phaseSourceCell_iff (hU a)]
    constructor
    · intro hx
      refine ⟨x - c a, ⟨L⁻¹ *ᵥ (x - c a), hx, ?_⟩, ?_⟩
      · change L *ᵥ (L⁻¹ *ᵥ (x - c a)) = x - c a
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL, Matrix.one_mulVec]
      · abel_nf
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change L⁻¹ *ᵥ ((c a + L *ᵥ z) - c a) ∈ _
      simpa only [add_sub_cancel_left, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hL, Matrix.one_mulVec] using hz
  · simp [markedPhaseSourceCell, ha]



/-- Exact physical Haar intensity of each original marked phase-cell section. -/
theorem volume_section_markedPhaseSourceCell
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hU : ∀ a, (U a).PosSemidef) (c : ℝ → (ι → ℝ)) (B : Set ℝ) (R a : ℝ) :
    volume ((fun x : ι → ℝ ↦ (x, a)) ⁻¹' markedPhaseSourceCell L U c B R) =
      if a ∈ B then ENNReal.ofReal |L.det| * ENNReal.ofReal (1 + U a).det *
        volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R)) else 0 := by
  classical
  rw [section_markedPhaseSourceCell hL hU]
  split_ifs with ha
  · have htrans (S : Set (ι → ℝ)) :
        (fun x ↦ c a + x) '' S = (fun x ↦ -c a + x) ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [mem_preimage, neg_add_cancel_left] using hy
      · intro hx
        refine ⟨-c a + x, hx, ?_⟩
        simp
    rw [htrans, measure_preimage_add, volume_linearImage_phaseSourceCell _ (hU a)]
  · exact measure_empty

/-- The full marked source intensity is the true integrated determinant of its original leg. -/
theorem prod_volume_markedPhaseSourceCell
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hUm : Measurable U) (hU : ∀ a, (U a).PosSemidef)
    {c : ℝ → (ι → ℝ)} (hc : Measurable c) {B : Set ℝ} (hB : MeasurableSet B)
    (μ : Measure ℝ) [SFinite μ] (R : ℝ) :
    ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U c B R) =
      (ENNReal.ofReal |L.det| *
        volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R))) *
      ∫⁻ a, ENNReal.ofReal (B.indicator (fun a ↦ (1 + U a).det) a) ∂μ := by
  classical
  rw [Measure.prod_apply_symm (measurableSet_markedPhaseSourceCell L hUm hc hB R)]
  simp_rw [volume_section_markedPhaseSourceCell hL hU c B R]
  have hfin : ENNReal.ofReal |L.det| *
      volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R)) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (isCompact_closedBall _ _).measure_lt_top).ne
  rw [← lintegral_const_mul' _ _ hfin]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ B
  · simp only [ite_eq_left ha, indicator_of_mem ha]
    ring
  · simp [ha]

/-- The original determinant moment gives finite physical intensity of the entire source envelope. -/
theorem prod_volume_markedPhaseSourceCell_lt_top
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hUm : Measurable U) (hU : ∀ a, (U a).PosSemidef)
    {c : ℝ → (ι → ℝ)} (hc : Measurable c) {B : Set ℝ} (hB : MeasurableSet B)
    (μ : Measure ℝ) [SFinite μ] (R : ℝ)
    (hdet : Integrable (B.indicator (fun a ↦ (1 + U a).det)) μ) :
    ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U c B R) < ∞ := by
  rw [prod_volume_markedPhaseSourceCell hL hUm hU hc hB μ R]
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (isCompact_closedBall _ _).measure_lt_top
  · exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hdet.2

end OTSelector.Reconstruction
