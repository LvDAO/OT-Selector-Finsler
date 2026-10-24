import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pi
import OTSelector.Analysis.Convex.ProductVarianceTensorization
import OTSelector.Analysis.Sobolev.IntervalPoincare
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalSmoothBoxPoincare.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalSmoothBoxPoincare`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C1 scalar function on a translated nondegenerate finite product box.

Objects: Actual mean-zero/centered box Poincaré inequalities, with coordinate side lengths and a dimension factor.

Proof detail: Represent normalized box measure as a product of interval laws, apply the finite-coordinate variance bound and the one-dimensional FTC energy bound, then undo normalization.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Rick Durrett, Section 1.6.3, variance identities (1.6.2)–(1.6.4), p. 33; Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=41); D. H. Fremlin, Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14).
Relation: Tensorized elementary estimate with its stated dimension factor; no sharp Poincaré constant is claimed.
-/

/-! Actual smooth Poincare inequality on arbitrary translated boxes. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The product of actual normalized interval restrictions is the normalized box volume. -/
theorem pi_cond_intervals_eq_smul_box {q : ℕ} (a b : Fin q → ℝ) :
    Measure.pi (fun i ↦ ProbabilityTheory.cond volume (Icc (a i) (b i))) =
      (∏ i : Fin q, (volume (Icc (a i) (b i)))⁻¹) • volume.restrict (Icc a b) := by
  let μ : Fin q → Measure ℝ := fun i ↦ ProbabilityTheory.cond volume (Icc (a i) (b i))
  have he : Measure.pi μ = (∏ i : Fin q, (volume (Icc (a i) (b i)))⁻¹) •
      Measure.pi (fun i ↦ volume.restrict (Icc (a i) (b i))) := by
    apply Measure.pi_eq
    intro s hs
    simp only [Measure.smul_apply, Measure.pi_pi, μ, ProbabilityTheory.cond, smul_eq_mul,
      Finset.prod_mul_distrib]
  rw [← Measure.restrict_pi_pi, ← volume_pi, pi_univ_Icc] at he
  exact he

/-- The actual multidimensional zero-mean Poincare inequality for a C1 function
on any translated rectangular box. Every coordinate energy is the original
Fréchet derivative in the corresponding unit coordinate direction. -/
theorem smooth_box_poincare_sq_of_mean_zero
    {q : ℕ} {a b : Fin q → ℝ} (hab : ∀ i, a i < b i)
    {f : (Fin q → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hmean : (∫ x in Icc a b, f x) = 0) :
    2 * (∫ x in Icc a b, (f x)^2) ≤ (q : ℝ) *
      ∑ i : Fin q, (b i - a i)^2 *
        (∫ x in Icc a b, (fderiv ℝ f x (Pi.single i 1))^2) := by
  classical
  let μ : Fin q → Measure ℝ := fun i ↦ ProbabilityTheory.cond volume (Icc (a i) (b i))
  let ν : Measure (Fin q → ℝ) := Measure.pi μ
  let κ : ℝ≥0∞ := ∏ i : Fin q, (volume (Icc (a i) (b i)))⁻¹
  have hvolpos (i : Fin q) : (volume : Measure ℝ) (Icc (a i) (b i)) ≠ 0 := by
    simpa only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos] using hab i
  have hvolfin (i : Fin q) : (volume : Measure ℝ) (Icc (a i) (b i)) ≠ ∞ := by simp
  let (i : Fin q) : IsProbabilityMeasure (μ i) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (hvolpos i) (hvolfin i)
  have hκ0 : κ ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ ENNReal.inv_ne_zero.mpr (hvolfin i))
  have hκfin : κ ≠ ∞ := by
    exact ENNReal.prod_ne_top (fun i _ ↦ ENNReal.inv_ne_top.mpr (hvolpos i))
  have hκpos : 0 < κ.toReal := ENNReal.toReal_pos hκ0 hκfin
  have hν : ν = κ • volume.restrict (Icc a b) := pi_cond_intervals_eq_smul_box a b
  have hint {g : (Fin q → ℝ) → ℝ} (hg : Continuous g) : Integrable g ν := by
    rw [hν]
    exact hg.continuousOn.integrableOn_Icc.smul_measure hκfin
  have hdf (i : Fin q) : Continuous (fun x ↦ fderiv ℝ f x (Pi.single i 1)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  let g : Fin q → (Fin q → ℝ) → ℝ :=
    fun i x ↦ (b i - a i)^2 * (fderiv ℝ f x (Pi.single i 1))^2
  have hg (i : Fin q) : Integrable (g i) ν := hint ((hdf i).pow 2 |>.const_mul _)
  have hbox : ∀ᵐ x ∂ν, x ∈ Icc a b := by
    change ∀ᵐ x ∂Measure.pi μ, x ∈ Icc a b
    have hcoords : ∀ i : Fin q, ∀ᵐ x ∂Measure.pi μ, x i ∈ Icc (a i) (b i) := by
      intro i
      exact (measurePreserving_eval μ i).quasiMeasurePreserving.tendsto_ae
        (ProbabilityTheory.ae_cond_mem measurableSet_Icc)
    filter_upwards [ae_all_iff.mpr hcoords] with x hx
    exact ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩
  have hpairs : ∀ᵐ p : (Fin q → ℝ) × (Fin q → ℝ) ∂ν.prod ν,
      p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b := by
    filter_upwards [(measurePreserving_fst (μ := ν) (ν := ν)).quasiMeasurePreserving.tendsto_ae hbox,
      (measurePreserving_snd (μ := ν) (ν := ν)).quasiMeasurePreserving.tendsto_ae hbox] with p hx hy
    exact ⟨hx, hy⟩
  have hcoord (i : Fin q) : ∀ᵐ p : (Fin q → ℝ) × (Fin q → ℝ) ∂ν.prod ν,
      (f (cubeCoordinateMix (i.val + 1) p.1 p.2) -
        f (cubeCoordinateMix i.val p.1 p.2))^2 ≤
          ∫ t, g i (Function.update (cubeCoordinateMix i.val p.1 p.2) i t) ∂μ i := by
    filter_upwards [hpairs] with p hp
    let z := cubeCoordinateMix i.val p.1 p.2
    have hslice : ContDiff ℝ 1 (fun t : ℝ ↦ f (Function.update z i t)) :=
      hf.comp (contDiff_update 1 z i)
    have hd (t : ℝ) : deriv (fun r : ℝ ↦ f (Function.update z i r)) t =
        fderiv ℝ f (Function.update z i t) (Pi.single i 1) :=
      ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update z i t)).deriv
    have h := smooth_interval_sub_sq_le_energy hslice (hab i).le
      ⟨hp.1.1 i, hp.1.2 i⟩ ⟨hp.2.1 i, hp.2.2 i⟩
    have hza : Function.update z i (p.1 i) = z := by
      have hz : z i = p.1 i := by simp [z, cubeCoordinateMix]
      rw [← hz, Function.update_eq_self]
    rw [hza] at h
    rw [cubeCoordinateMix_succ]
    change (f (Function.update z i (p.2 i)) - f z)^2 ≤ _
    have he : (∫ t, g i (Function.update z i t) ∂μ i) =
        (b i - a i) * (∫ r in a i..b i,
          (deriv (fun t : ℝ ↦ f (Function.update z i t)) r)^2) := by
      simp only [μ, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc,
        ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr (hab i).le), smul_eq_mul]
      rw [integral_const_mul]
      rw [intervalIntegral.integral_of_le (hab i).le, ← integral_Icc_eq_integral_Ioc]
      simp only [hd]
      field_simp [(sub_pos.mpr (hab i)).ne']
    rw [he]
    exact h
  have h := cube_tensorization_integrated_energy_sq_le μ (hint hf.continuous)
    (hint (hf.continuous.pow 2)) hg hcoord
  change 2 * ((∫ x, (f x)^2 ∂ν) - (∫ x, f x ∂ν)^2) ≤
    (q : ℝ) * ∑ i : Fin q, ∫ x, g i x ∂ν at h
  simp only [hν, integral_smul_measure, smul_eq_mul, hmean, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
    sub_zero, g, integral_const_mul] at h
  have hh : κ.toReal * (2 * (∫ x in Icc a b, (f x)^2)) ≤
      κ.toReal * ((q : ℝ) * ∑ i : Fin q, (b i - a i)^2 *
        (∫ x in Icc a b, (fderiv ℝ f x (Pi.single i 1))^2)) := by
    calc
      _ = 2 * (κ.toReal * (∫ x in Icc a b, (f x)^2)) := by ring
      _ ≤ (q : ℝ) * ∑ i : Fin q, (b i - a i)^2 *
          (κ.toReal * (∫ x in Icc a b, (fderiv ℝ f x (Pi.single i 1))^2)) := h
      _ = _ := by
        conv_rhs => rw [mul_left_comm κ.toReal (q : ℝ)]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  exact (mul_le_mul_iff_right₀ hκpos).mp hh

/-- The literal box average is a valid finite-dimensional constant approximant,
with error controlled by the original coordinate gradient energies. -/
theorem smooth_box_poincare_sq
    {q : ℕ} {a b : Fin q → ℝ} (hab : ∀ i, a i < b i)
    {f : (Fin q → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) :
    2 * (∫ x in Icc a b,
      (f x - (volume.real (Icc a b))⁻¹ * (∫ y in Icc a b, f y))^2) ≤ (q : ℝ) *
      ∑ i : Fin q, (b i - a i)^2 *
        (∫ x in Icc a b, (fderiv ℝ f x (Pi.single i 1))^2) := by
  let c := (volume.real (Icc a b))⁻¹ * (∫ y in Icc a b, f y)
  have hvolpos : 0 < volume.real (Icc a b) := by
    rw [measureReal_def, Real.volume_Icc_pi_toReal (fun i ↦ (hab i).le)]
    exact Finset.prod_pos (fun i _ ↦ sub_pos.mpr (hab i))
  have hmean : (∫ x in Icc a b, (f x - c)) = 0 := by
    rw [integral_sub (f := f) (g := fun _ ↦ c) (μ := volume.restrict (Icc a b))
      hf.continuous.continuousOn.integrableOn_Icc (continuous_const.continuousOn.integrableOn_Icc : IntegrableOn (fun _ : Fin q → ℝ ↦ c) (Icc a b) volume),
      setIntegral_const]
    simp only [smul_eq_mul]
    dsimp only [c]
    field_simp [hvolpos.ne']
    ring
  have h := smooth_box_poincare_sq_of_mean_zero hab (hf.sub contDiff_const) hmean
  simpa only [fderiv_sub_const] using h

/-- Uniform side-length form of the actual centered box approximation estimate. -/
theorem smooth_box_poincare_sq_of_side_le
    {q : ℕ} {a b : Fin q → ℝ} (hab : ∀ i, a i < b i)
    {f : (Fin q → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {h : ℝ} (hh : 0 ≤ h) (hside : ∀ i, b i - a i ≤ h) :
    2 * (∫ x in Icc a b,
      (f x - (volume.real (Icc a b))⁻¹ * (∫ y in Icc a b, f y))^2) ≤
        (q : ℝ) * h^2 * ∑ i : Fin q,
          (∫ x in Icc a b, (fderiv ℝ f x (Pi.single i 1))^2) := by
  apply (smooth_box_poincare_sq hab hf).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (sub_nonneg.mpr (hab i).le) hh).mpr (hside i))
    (integral_nonneg (fun _ ↦ sq_nonneg _))

end OTSelector.Reconstruction

end
end
