import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Analysis.Sobolev.UnitCubeW11

Conditions: A smooth scalar function on the unit cube, with the stated finite dimension and Hölder-conjugate exponent.

Objects: An interval control, coordinate line controls, and an endpoint W1,1-type unit-cube norm bound by value and derivative L1 integrals.

Proof detail: Use interval FTC to bound each point by its line average and derivative integral, multiply the coordinate controls, then apply iterative Hölder/Fubini in the Loomis–Whitney argument.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=257): Section 1.14, Exercise 1.14.21, pp. 248–249, and Lemma 1.14.9 (Endpoint Sobolev inequality), p. 249.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=32): Sections 473F–473H, pp. 32–34, especially 473G (iterated Hölder) and 473H (Gagliardo–Nirenberg–Sobolev).
- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=200): Section 5.3.1, Theorem 5.3.1, pp. 200–201.

Source relation: Unit-cube derived version of the endpoint FTC/Loomis–Whitney proof, including its L1 value term and explicit ENNReal encoding.
-/

/-! Actual bounded-cube W1,1 Sobolev estimates from one-dimensional FTC and grid lines. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- A genuine C1 interval value is bounded by the average function and derivative norms. -/
theorem smooth_unit_interval_enorm_le_lintegral_add_deriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖f s‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖f t‖ₑ + ‖deriv f t‖ₑ := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖f s - f t‖ₑ ≤ ∫⁻ r in Icc (0 : ℝ) 1, ‖deriv f r‖ₑ := by
    rcases le_total t s with hts | hst
    · exact (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn hts).trans
        (lintegral_mono_set (Icc_subset_Icc ht.1 hs.2))
    · rw [enorm_sub_rev]
      exact (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn hst).trans
        (lintegral_mono_set (Icc_subset_Icc hs.1 ht.2))
  have hh : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖f s‖ₑ ≤ ‖f t‖ₑ + ∫⁻ r in Icc (0 : ℝ) 1, ‖deriv f r‖ₑ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    calc
      ‖f s‖ₑ = ‖f s - f t + f t‖ₑ := by rw [sub_add_cancel]
      _ ≤ ‖f s - f t‖ₑ + ‖f t‖ₑ := enorm_add_le _ _
      _ ≤ _ := (add_le_add (hd t ht) le_rfl).trans_eq (add_comm _ _)
  have h := lintegral_mono_ae hh
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc] at h
  norm_num at h
  exact h.trans_eq (lintegral_add_left hf.continuous.measurable.enorm _).symm

/-- Each actual cube slice has the grid-line upper bound with the true full derivative. -/
theorem smooth_unit_cube_enorm_le_lintegral_line
    {q : ℕ} {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    {x : Fin q → ℝ} (hx : x ∈ Icc (0 : Fin q → ℝ) 1) (i : Fin q) :
    ‖u x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
      ‖u (update x i t)‖ₑ + ‖fderiv ℝ u (update x i t)‖ₑ := by
  have hf : ContDiff ℝ 1 (u ∘ update x i) := hu.comp (contDiff_update 1 x i)
  have hh := smooth_unit_interval_enorm_le_lintegral_add_deriv hf ⟨hx.1 i, hx.2 i⟩
  simp only [Function.comp_apply, Function.update_eq_self] at hh
  apply hh.trans
  apply lintegral_mono
  intro t
  refine add_le_add le_rfl ?_
  calc
    ‖deriv (u ∘ update x i) t‖ₑ =
        ‖fderiv ℝ u (update x i t) (deriv (update x i) t)‖ₑ := by
      rw [fderiv_comp_deriv _ (hu.differentiable one_ne_zero).differentiableAt
        (hasDerivAt_update x i t).differentiableAt]
    _ ≤ ‖fderiv ℝ u (update x i t)‖ₑ * ‖deriv (update x i) t‖ₑ :=
      ContinuousLinearMap.le_opENorm _ _
    _ ≤ _ := by simp [deriv_update, Pi.enorm_single]

/-- Critical bounded-cube W1,1 Sobolev estimate. The lower-order term is produced by actual
interval averaging rather than a compact-support or extension assumption. -/
theorem smooth_unit_cube_lintegral_pow_le_pow_lintegral_add_fderiv
    {q : ℕ} {p : ℝ} (hp : Real.HolderConjugate (q : ℝ) p)
    {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    (∫⁻ x in Icc (0 : Fin q → ℝ) 1, ‖u x‖ₑ ^ p) ≤
      (∫⁻ x in Icc (0 : Fin q → ℝ) 1, (‖u x‖ₑ + ‖fderiv ℝ u x‖ₑ)) ^ p := by
  have hq : (1 : ℝ) < q := hp.lt
  have hμ : Measure.pi (fun _ : Fin q ↦ volume.restrict (Icc (0 : ℝ) 1)) =
      volume.restrict (Icc (0 : Fin q → ℝ) 1) := by
    rw [← Measure.restrict_pi_pi, ← volume_pi, pi_univ_Icc]
    rfl
  calc
    _ = ∫⁻ x in Icc (0 : Fin q → ℝ) 1,
        (‖u x‖ₑ ^ (1 / (q - 1 : ℝ))) ^ (q : ℝ) := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.rpow_mul, hp.conjugate_eq]
      congr 1
      field_simp
    _ = ∫⁻ x in Icc (0 : Fin q → ℝ) 1,
        ∏ _i : Fin q, ‖u x‖ₑ ^ (1 / (q - 1 : ℝ)) := by
      apply lintegral_congr
      intro x
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      norm_cast
    _ ≤ ∫⁻ x in Icc (0 : Fin q → ℝ) 1,
        ∏ i : Fin q, (∫⁻ t in Icc (0 : ℝ) 1,
          (‖u (update x i t)‖ₑ + ‖fderiv ℝ u (update x i t)‖ₑ)) ^ (1 / (q - 1 : ℝ)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      apply Finset.prod_le_prod'
      intro i _
      exact ENNReal.rpow_le_rpow (smooth_unit_cube_enorm_le_lintegral_line hu hx i)
        (by positivity)
    _ ≤ _ := by
      rw [← hμ]
      have hh := lintegral_prod_lintegral_pow_le
        (fun _ : Fin q ↦ volume.restrict (Icc (0 : ℝ) 1))
        (by simpa using hp) (f := fun x ↦ ‖u x‖ₑ + ‖fderiv ℝ u x‖ₑ)
        (hu.continuous.measurable.enorm.add (hu.continuous_fderiv (by norm_num)).measurable.enorm)
      simpa only [Fintype.card_fin, hμ] using hh

/-- The genuine bounded-cube critical W1,1 estimate in eLpNorm form. -/
theorem smooth_unit_cube_eLpNorm_le_lintegral_add_fderiv
    {q : ℕ} {p : ℝ≥0} (hp : NNReal.HolderConjugate (q : ℝ≥0) p)
    {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    eLpNorm u p (volume.restrict (Icc (0 : Fin q → ℝ) 1)) ≤
      ∫⁻ x in Icc (0 : Fin q → ℝ) 1, (‖u x‖ₑ + ‖fderiv ℝ u x‖ₑ) := by
  apply (ENNReal.rpow_le_rpow_iff hp.coe.symm.pos).mp
  rw [eLpNorm_nnreal_pow_eq_lintegral hp.symm.pos.ne']
  exact smooth_unit_cube_lintegral_pow_le_pow_lintegral_add_fderiv hp.coe hu

end OTSelector.Reconstruction
