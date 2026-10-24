import OTSelector.Analysis.Sobolev.BoxTraceCompactness
import OTSelector.Analysis.Sobolev.ProductBoxPoincare
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeCollarMeanBound.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeCollarMeanBound`; the selected original proof blocks follow. -/
section

/-!
Conditions: C1 functions on nondegenerate product boxes and a mean-zero unit-cube function for the normalized trace bounds.

Objects: Collar mean-square bounds, bulk Poincaré, face trace energy and subcell-average control.

Proof detail: Apply integral Cauchy–Schwarz to means, interval FTC in the normal direction and product-box Poincaré; integrate over faces and subcells.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Terence Tao, Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19).
Relation: Elementary collar/trace estimates with explicit dimension constants, derived without invoking a general trace theorem.
-/

/-! Actual collar mean and unit-cube trace bounds from original gradient energy. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- Finite-measure Jensen obtained from the actual nonnegative square integral. -/
theorem integral_mean_sq_le_of_volume_pos
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x ↦ (f x)^2) μ)
    (hV : 0 < μ.real univ) :
    ((μ.real univ)⁻¹ * (∫ x, f x ∂μ))^2 ≤
      (μ.real univ)⁻¹ * (∫ x, (f x)^2 ∂μ) := by
  let V := μ.real univ
  let I := ∫ x, f x ∂μ
  have hVpos : 0 < V := hV
  have hn : 0 ≤ ∫ x, (V * f x - I)^2 ∂μ := integral_nonneg (fun _ ↦ sq_nonneg _)
  have he : (∫ x, (V * f x - I)^2 ∂μ) =
      V * (V * (∫ x, (f x)^2 ∂μ) - I^2) := by
    calc
      _ = ∫ x, (V^2 * (f x)^2 - (2*V*I)*f x) + I^2 ∂μ := by
        congr 1
        funext x
        ring
      _ = _ := by
        rw [integral_add
          (f := fun x ↦ V^2 * (f x)^2 - (2*V*I)*f x)
          (g := fun _ ↦ I^2) ((hf2.const_mul _).sub (hf.const_mul _)) (integrable_const _),
          integral_sub (f := fun x ↦ V^2 * (f x)^2) (g := fun x ↦ (2*V*I)*f x)
            (hf2.const_mul _) (hf.const_mul _),
          integral_const_mul, integral_const_mul, integral_const]
        simp only [smul_eq_mul]
        dsimp only [V, I]
        ring
  rw [he] at hn
  have hCS : I^2 ≤ V * (∫ x, (f x)^2 ∂μ) := by
    have : 0 ≤ V * (∫ x, (f x)^2 ∂μ) - I^2 := nonneg_of_mul_nonneg_right hn hV
    linarith
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hV)).mp
  have he1 : V^2 * (V⁻¹ * I)^2 = I^2 := by field_simp [hVpos.ne']
  have he2 : V^2 * (V⁻¹ * (∫ x, (f x)^2 ∂μ)) =
      V * (∫ x, (f x)^2 ∂μ) := by field_simp [hVpos.ne']
  change V^2 * (V⁻¹ * I)^2 ≤ V^2 * (V⁻¹ * (∫ x, (f x)^2 ∂μ))
  rw [he1, he2]
  exact hCS

/-- The square of the literal smooth collar-cell mean is bounded by its own L2 average. -/
theorem smooth_product_box_mean_sq_le
    {q : ℕ} {a b : Fin q → ℝ} (hab : ∀ i, a i < b i)
    {c d : ℝ} (hcd : c < d)
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ((volume.real (Icc a b ×ˢ Icc c d))⁻¹ *
      (∫ p in Icc a b ×ˢ Icc c d, f p))^2 ≤
        (volume.real (Icc a b ×ˢ Icc c d))⁻¹ *
          (∫ p in Icc a b ×ˢ Icc c d, (f p)^2) := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  let : IsFiniteMeasure (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    isFiniteMeasure_restrict.mpr hcompact.measure_lt_top.ne
  have hint {g : (Fin q → ℝ) × ℝ → ℝ} (hg : Continuous g) :
      IntegrableOn g (Icc a b ×ˢ Icc c d) volume := by
    rw [← Icc_prod_eq (a,c) (b,d)]
    exact hg.continuousOn.integrableOn_Icc
  have hV : 0 < volume.real (Icc a b ×ˢ Icc c d) := by
    rw [Measure.volume_eq_prod, measureReal_prod_prod]
    apply mul_pos
    · rw [measureReal_def, Real.volume_Icc_pi_toReal (fun i ↦ (hab i).le)]
      exact Finset.prod_pos (fun i _ ↦ sub_pos.mpr (hab i))
    · rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hcd.le)]
      exact sub_pos.mpr hcd
  have h := integral_mean_sq_le_of_volume_pos (hint hf.continuous)
    (hint (hf.continuous.pow 2)) (by simpa only [measureReal_restrict_apply_univ] using hV)
  simpa only [measureReal_restrict_apply_univ] using h

/-- The unit full cube with zero actual mean has its true bulk L2 energy
controlled by the original tangential and normal gradient energies. -/
theorem smooth_unit_product_box_bulk_sq_le_of_mean_zero
    {q : ℕ} {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hmean : (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p) = 0) :
    2 * (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (f p)^2) ≤
      ((q + 1 : ℕ) : ℝ) *
        ((∑ i : Fin q, ∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          (fderiv ℝ f p (Pi.single i 1, 0))^2) +
          (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            (fderiv ℝ f p (0, 1))^2)) := by
  have h := smooth_product_box_poincare_sq_of_side_le (a := (0 : Fin q → ℝ)) (b := 1)
    (c := 0) (d := 1) (by intro i; norm_num) (by norm_num) hf
    (h := 1) (by norm_num) (by intro i; norm_num) (by norm_num)
  simpa only [hmean, mul_zero, sub_zero, one_pow, mul_one] using h

/-- The actual full unit face trace is bounded by the original full-cube gradient
energy for every smooth function with zero actual cube mean. -/
theorem smooth_unit_product_face_trace_sq_le_of_mean_zero
    {q : ℕ} {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hmean : (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p) = 0) :
    (∫ y in Icc (0 : Fin q → ℝ) 1, (f (y, 0))^2) ≤
      ((q + 2 : ℕ) : ℝ) *
        ((∑ i : Fin q, ∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          (fderiv ℝ f p (Pi.single i 1, 0))^2) +
          (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            (fderiv ℝ f p (0, 1))^2)) := by
  have hbulk := smooth_unit_product_box_bulk_sq_le_of_mean_zero hf hmean
  have htrace := smooth_box_face_trace_sq_le_h1 (a := (0 : Fin q → ℝ)) (b := 1) hf
  have hsum : 0 ≤ ∑ i : Fin q,
      ∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        (fderiv ℝ f p (Pi.single i 1, 0))^2 :=
    Finset.sum_nonneg (fun i _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hbulk ⊢
  nlinarith

/-- Every actual nondegenerate subcell mean is bounded uniformly on the smooth
zero-mean unit-gradient ball; the coefficient uses the true subcell volume. -/
theorem smooth_product_subcell_mean_sq_le_of_unit_energy
    {q : ℕ} {a b : Fin q → ℝ} (hab : ∀ i, a i < b i)
    {c d : ℝ} (hcd : c < d)
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsub : Icc a b ×ˢ Icc c d ⊆ Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (hmean : (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p) = 0)
    (henergy :
      ((∑ i : Fin q, ∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        (fderiv ℝ f p (Pi.single i 1, 0))^2) +
        (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          (fderiv ℝ f p (0, 1))^2)) ≤ 1) :
    ((volume.real (Icc a b ×ˢ Icc c d))⁻¹ *
      (∫ p in Icc a b ×ˢ Icc c d, f p))^2 ≤
        (volume.real (Icc a b ×ˢ Icc c d))⁻¹ * (((q + 1 : ℕ) : ℝ) / 2) := by
  have hbulk := smooth_unit_product_box_bulk_sq_le_of_mean_zero hf hmean
  have hbulk1 : (∫ p in Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (f p)^2) ≤
      ((q + 1 : ℕ) : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg (q + 1))
    nlinarith
  have hint : IntegrableOn (fun p ↦ (f p)^2)
      (Icc (0 : Fin q → ℝ) 1 ×ˢ Icc (0 : ℝ) 1) volume := by
    rw [← Icc_prod_eq ((0 : Fin q → ℝ), (0 : ℝ)) (1,1)]
    exact (hf.continuous.pow 2).continuousOn.integrableOn_Icc
  have hmono := setIntegral_mono_set hint (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.of_forall hsub)
  exact (smooth_product_box_mean_sq_le hab hcd hf).trans
    (mul_le_mul_of_nonneg_left (hmono.trans hbulk1) (by positivity))

end OTSelector.Reconstruction

end
end
