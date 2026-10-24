import OTSelector.Reconstruction.BirthResidueNormalizedMomentum
import OTSelector.Reconstruction.FocalNormalizedMobility

/-!
# The genuine birth scale controls the same pole on a dyadic clock band

The short elapsed time is s and the endpoint distance is t. The actual scale
s I + (s/t²) G is used throughout, with its own canonical normalizer.
-/
open Set Matrix
open scoped Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The actual birth matrix is the short elapsed time times the fixed dyadic pole model. -/
theorem birthResidueScale_eq_smul_model (G : Matrix ι ι ℝ) (t s : ℝ) :
    birthResidueScale G t s = s • ((t ^ 2)⁻¹ • G + 1) := by
  simp only [birthResidueScale, smul_add, smul_smul, div_eq_mul_inv]
  module

omit [Fintype ι] in
/-- The lower pole model on an entire dyadic band uses the unchanged residue. -/
theorem positivePole_dyadic_model_lower {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hrt : r ≤ 4 * t) :
    (((r ^ 2)⁻¹ • G + 1) - (1 / 16 : ℝ) • ((t ^ 2)⁻¹ • G + 1)).PosSemidef := by
  have hsq : r ^ 2 ≤ 16 * t ^ 2 := by nlinarith
  have hdiv := one_div_le_one_div_of_le (sq_pos_of_pos hr) hsq
  have heq : (1 : ℝ) / (16 * t ^ 2) = (1 / 16 : ℝ) * (t ^ 2)⁻¹ := by
    field_simp
  have hcoeff : 0 ≤ (r ^ 2)⁻¹ - (1 / 16 : ℝ) * (t ^ 2)⁻¹ := by
    rw [heq] at hdiv
    exact sub_nonneg.mpr (by simpa only [one_div] using hdiv)
  have h := (hG.smul hcoeff).add (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 15 / 16))
  convert h using 1
  module

omit [Fintype ι] in
/-- The upper pole model on the same band has a fixed factor four. -/
theorem positivePole_dyadic_model_upper {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t r : ℝ} (ht : 0 < t) (htr : t / 2 ≤ r) :
    ((4 : ℝ) • ((t ^ 2)⁻¹ • G + 1) - ((r ^ 2)⁻¹ • G + 1)).PosSemidef := by
  have hr : 0 < r := lt_of_lt_of_le (half_pos ht) htr
  have hsq : t ^ 2 ≤ 4 * r ^ 2 := by nlinarith
  have hdiv : (1 : ℝ) / r ^ 2 ≤ 4 / t ^ 2 :=
    (div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos ht)).mpr (by nlinarith)
  have hcoeff : 0 ≤ 4 * (t ^ 2)⁻¹ - (r ^ 2)⁻¹ := by
    simp only [div_eq_mul_inv, one_mul] at hdiv
    linarith
  have h := (hG.smul hcoeff).add (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 3))
  convert h using 1
  module

omit [Fintype ι] in
/-- Actual two-sided pole comparison gives physical mobility bounds in the birth scale. -/
theorem birthResidueScale_physical_mobility_bounds
    {G W : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s r c C : ℝ}
    (ht : 0 < t) (hs : 0 ≤ s) (hr : r ∈ Icc (t / 2) (4 * t))
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : (W - c • ((r ^ 2)⁻¹ • G + 1)).PosSemidef)
    (hupper : (C • ((r ^ 2)⁻¹ • G + 1) - W).PosSemidef) :
    (s • W - (c / 16) • birthResidueScale G t s).PosSemidef ∧
      ((4 * C) • birthResidueScale G t s - s • W).PosSemidef := by
  have hl := (hlower.add
    ((positivePole_dyadic_model_lower hG ht
      (lt_of_lt_of_le (half_pos ht) hr.1) hr.2).smul hc)).smul hs
  have hu := (hupper.add ((positivePole_dyadic_model_upper hG ht hr.1).smul hC)).smul hs
  constructor
  · convert hl using 1
    rw [birthResidueScale_eq_smul_model]
    module
  · convert hu using 1
    rw [birthResidueScale_eq_smul_model]
    module

/-- The canonical birth normalizer gives uniform lower and upper mobility bounds. -/
theorem birth_normalized_mobility_bounds
    {G W : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s r c C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hr : r ∈ Icc (t / 2) (4 * t))
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : (W - c • ((r ^ 2)⁻¹ • G + 1)).PosSemidef)
    (hupper : (C • ((r ^ 2)⁻¹ • G + 1) - W).PosSemidef) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    (s • (T * W * Tᵀ) - (c / 16) • 1).PosSemidef ∧
      ((4 * C) • 1 - s • (T * W * Tᵀ)).PosSemidef := by
  obtain ⟨hl, hu⟩ := birthResidueScale_physical_mobility_bounds hG ht hs.le hr hc hC hlower hupper
  have hscale := birthResidueScale_posDef (t := t) hG hs
  constructor
  · simpa only [Matrix.mul_smul, Matrix.smul_mul] using
      posSemidef_positiveMatrixNormalizer_congruence_lower hscale hl
  · have h := hu.mul_mul_conjTranspose_same (positiveMatrixNormalizer (birthResidueScale G t s))
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, (positiveMatrixNormalizer_spec hscale).2] using h

/-- One true pole constant controls the canonical birth-normalized mobility norm at every
short elapsed scale, uniformly in its endpoint distance and the residue rank. -/
theorem exists_norm_bound_birth_normalized_mobility (C : ℝ) :
    ∃ B ≥ 0, ∀ {G W : Matrix ι ι ℝ}, G.PosSemidef → W.PosSemidef →
      ∀ {t s r : ℝ}, 0 < t → 0 < s → r ∈ Icc (t / 2) (4 * t) → 0 ≤ C →
      (C • ((r ^ 2)⁻¹ • G + 1) - W).PosSemidef →
      ‖s • (positiveMatrixNormalizer (birthResidueScale G t s) * W *
        (positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_posSemidef_trace_le
    (n := ι) (4 * C * (Fintype.card ι : ℝ))
  refine ⟨B, hB, fun {G W} hG hW {t s r} ht hs hr hC hupper ↦ ?_⟩
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  have hN : (s • (T * W * Tᵀ)).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hW.mul_mul_conjTranspose_same T).smul hs.le
  have hlower : (W - (0 : ℝ) • ((r ^ 2)⁻¹ • G + 1)).PosSemidef := by simpa using hW
  have hu := (birth_normalized_mobility_bounds hG ht hs hr le_rfl hC hlower hupper).2
  have htrace := hu.trace_nonneg
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at htrace
  apply hbound _ hN
  rw [Matrix.trace_smul, smul_eq_mul]
  linarith

end OTSelector.Reconstruction
