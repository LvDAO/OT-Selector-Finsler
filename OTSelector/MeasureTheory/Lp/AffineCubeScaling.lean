import OTSelector.MeasureTheory.Integral.AffineCube
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeSobolevPoincareScaleMeasure.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeSobolevPoincareScaleMeasure`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.AffineCubeScaling

## Lemma skeleton

* **Conditions:** Positive affine side length on finite coordinate cubes; arbitrary real readout and a finite nonnegative exponent p including the library p=0 convention.
* **Objects:** Exact affine Haar pushforwards and finite-exponent eLpNorm scaling by the determinant power.
* **Proof detail:** Use translation/dilation volume identities for the affine map and inverse, restrict to the exact cube image and apply scalar-measure Lp scaling.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22): Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=211): Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).

Source relation (composition): Measure/seminorm scaling only. This module does not assert a new Sobolev–Poincare inequality, despite its old filename.
-/

/-! Actual Haar measure and finite-exponent seminorm scaling on translated raw cubes. -/
open Set Function MeasureTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

private theorem affine_raw_measurableEmbedding {q : ℕ} (a : Fin q → ℝ)
    {L : ℝ} (hL : 0 < L) : MeasurableEmbedding (fun y : Fin q → ℝ ↦ a + L • y) :=
  (measurableEmbedding_addLeft a).comp (measurableEmbedding_const_smul₀ hL.ne')

private theorem map_affine_raw_volume {q : ℕ} (a : Fin q → ℝ)
    {L : ℝ} (hL : 0 < L) :
    Measure.map (fun y : Fin q → ℝ ↦ a + L • y) volume =
      ENNReal.ofReal ((L ^ q)⁻¹) • volume := by
  change Measure.map ((fun z : Fin q → ℝ ↦ a + z) ∘ (fun y ↦ L • y)) volume = _
  have hadd : Measurable (fun z : Fin q → ℝ ↦ a + z) := by fun_prop
  rw [← Measure.map_map hadd (measurable_const_smul L),
    Measure.map_addHaar_smul volume hL.ne', Measure.map_smul, map_add_left_eq_self]
  simp only [Module.finrank_pi, Fintype.card_fin, abs_of_nonneg (inv_nonneg.mpr
    (pow_nonneg hL.le q))]

private theorem map_affine_raw_restrict {q : ℕ} (a : Fin q → ℝ)
    {L : ℝ} (hL : 0 < L) (s : Set (Fin q → ℝ)) :
    Measure.map (fun y : Fin q → ℝ ↦ a + L • y) (volume.restrict s) =
      ENNReal.ofReal ((L ^ q)⁻¹) • volume.restrict
        ((fun y : Fin q → ℝ ↦ a + L • y) '' s) := by
  have hA := affine_raw_measurableEmbedding a hL
  calc
    _ = (Measure.map (fun y : Fin q → ℝ ↦ a + L • y) volume).restrict
        ((fun y : Fin q → ℝ ↦ a + L • y) '' s) := by
      rw [hA.restrict_map, preimage_image_eq s hA.injective]
    _ = _ := by rw [map_affine_raw_volume a hL, Measure.restrict_smul]

/-- The actual positive affine map sends unit-cube volume to the inverse-Jacobian multiple
of volume restricted to the translated cube. -/
theorem map_affine_unit_cube_volume {q : ℕ} (a : Fin q → ℝ)
    {L : ℝ} (hL : 0 < L) :
    Measure.map (fun y : Fin q → ℝ ↦ a + L • y)
        (volume.restrict (Icc (0 : Fin q → ℝ) 1)) =
      ENNReal.ofReal ((L ^ q)⁻¹) • volume.restrict (Icc a (a + L • 1)) := by
  rw [map_affine_raw_restrict a hL, image_affine_unit_cube_box a hL]

/-- The inverse affine map sends the true translated-cube volume to its physical volume
factor times unit-cube volume. -/
theorem map_inverse_affine_cube_volume {q : ℕ} (a : Fin q → ℝ)
    {L : ℝ} (hL : 0 < L) :
    Measure.map (fun x : Fin q → ℝ ↦ -(L⁻¹ • a) + L⁻¹ • x)
        (volume.restrict (Icc a (a + L • 1))) =
      ENNReal.ofReal (L ^ q) • volume.restrict (Icc (0 : Fin q → ℝ) 1) := by
  rw [map_affine_raw_restrict (-(L⁻¹ • a)) (inv_pos.mpr hL), inv_pow, inv_inv]
  congr 2
  rw [← image_affine_unit_cube_box a hL, image_image]
  have hcomp : (fun x : Fin q → ℝ ↦ -(L⁻¹ • a) + L⁻¹ • x) ∘
      (fun y : Fin q → ℝ ↦ a + L • y) = id := by
    funext y
    simp [smul_add, smul_smul, hL.ne']
  change (((fun x : Fin q → ℝ ↦ -(L⁻¹ • a) + L⁻¹ • x) ∘
    (fun y : Fin q → ℝ ↦ a + L • y)) '' Icc 0 1) = Icc 0 1
  rw [hcomp, image_id]

/-- Pulling a function to the unit cube gives the actual inverse-volume factor in its
finite-exponent seminorm, without a measurability assumption on the function. -/
theorem eLpNorm_affine_unit_cube {q : ℕ} (u : (Fin q → ℝ) → ℝ)
    (p : ℝ≥0) (a : Fin q → ℝ) {L : ℝ} (hL : 0 < L) :
    eLpNorm (fun y ↦ u (a + L • y)) p (volume.restrict (Icc (0 : Fin q → ℝ) 1)) =
      ENNReal.ofReal ((L ^ q)⁻¹) ^ (1 / (p : ℝ)) *
        eLpNorm u p (volume.restrict (Icc a (a + L • 1))) := by
  have hnorm := (affine_raw_measurableEmbedding a hL).eLpNorm_map_measure
    (g := u) (p := (p : ℝ≥0∞)) (μ := volume.restrict (Icc (0 : Fin q → ℝ) 1))
  rw [map_affine_unit_cube_volume a hL,
    eLpNorm_smul_measure_of_ne_top (by simp)] at hnorm
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.coe_toReal, smul_eq_mul,
    Function.comp_def] using hnorm.symm

/-- The physical translated-cube seminorm equals its genuine volume scaling times the
unit-cube pullback seminorm. This holds for every finite nonnegative exponent. -/
theorem eLpNorm_affine_cube_eq_pow_mul {q : ℕ} (u : (Fin q → ℝ) → ℝ)
    (p : ℝ≥0) (a : Fin q → ℝ) {L : ℝ} (hL : 0 < L) :
    eLpNorm u p (volume.restrict (Icc a (a + L • 1))) =
      ENNReal.ofReal (L ^ q) ^ (1 / (p : ℝ)) *
        eLpNorm (fun y ↦ u (a + L • y)) p (volume.restrict (Icc (0 : Fin q → ℝ) 1)) := by
  have hB := affine_raw_measurableEmbedding (-(L⁻¹ • a)) (inv_pos.mpr hL)
  have hnorm := hB.eLpNorm_map_measure (g := fun y ↦ u (a + L • y))
    (p := (p : ℝ≥0∞)) (μ := volume.restrict (Icc a (a + L • 1)))
  rw [map_inverse_affine_cube_volume a hL,
    eLpNorm_smul_measure_of_ne_top (by simp)] at hnorm
  have hcomp : (fun y ↦ u (a + L • y)) ∘
      (fun x : Fin q → ℝ ↦ -(L⁻¹ • a) + L⁻¹ • x) = u := by
    funext x
    simp [smul_add, smul_smul, hL.ne']
  rw [hcomp] at hnorm
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.coe_toReal, smul_eq_mul]
    using hnorm.symm

end OTSelector.Reconstruction

end
end
