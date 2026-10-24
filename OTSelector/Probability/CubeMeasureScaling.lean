import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.ProductMeasure
import OTSelector.MeasureTheory.CubeBlockDecomposition
import OTSelector.Probability.PoissonCubePressure

/-!
# Homotheties of the uniform cube law

For a positive natural number `m`, the dilation `x ↦ m * x` pushes the uniform
probability law on the interval `(0, m⁻¹)` forward to the uniform law on `(0, 1)`.
Taking coordinatewise products yields the corresponding statement for the uniform
cube law on `(Fin q → ℝ)`, and taking infinite products gives the corresponding
statement for iid sequences of cube points.  Together with the Poisson count, which
is left unchanged, this identifies the law of a dilated Poisson cloud on the small
cube `(0, m⁻¹)^q` with the unit-cube Poisson cloud law.

These identities are the self-similarity input of the dyadic block comparison:
a block of side length `m⁻¹` rescaled by `m` is distributed like the unit block.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OTSelector.Probability

/-- The dilation `x ↦ m * x` pushes the uniform law on `(0, m⁻¹)` to the uniform law
on `(0, 1)`. -/
theorem map_mul_uniformInterval (m : ℕ) (hm : 0 < m) :
    Measure.map (fun x : ℝ => (m : ℝ) * x) (uniformInterval ((m : ℝ)⁻¹)) =
      uniformInterval 1 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hemb : MeasurableEmbedding (fun x : ℝ => (m : ℝ) * x) :=
    measurableEmbedding_const_smul₀ hmne
  have himage : (fun x : ℝ => (m : ℝ) * x) '' Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹)
      = Set.Ioo (0 : ℝ) 1 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      have hlt : (m : ℝ) * x < (m : ℝ) * (m : ℝ)⁻¹ :=
        mul_lt_mul_of_pos_left hx1 hmpos
      rw [mul_inv_cancel₀ hmne] at hlt
      exact ⟨mul_pos hmpos hx0, hlt⟩
    · rintro ⟨hy0, hy1⟩
      refine ⟨(m : ℝ)⁻¹ * y, ⟨?_, ?_⟩, ?_⟩
      · exact mul_pos (inv_pos.mpr hmpos) hy0
      · simpa using mul_lt_mul_of_pos_left hy1 (inv_pos.mpr hmpos)
      · show (m : ℝ) * ((m : ℝ)⁻¹ * y) = y
        rw [← mul_assoc, mul_inv_cancel₀ hmne, one_mul]
  have hpre : (fun x : ℝ => (m : ℝ) * x) ⁻¹' Set.Ioo (0 : ℝ) 1
      = Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹) := by
    rw [← himage, Set.preimage_image_eq _ hemb.injective]
  have hvol : volume (Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹)) = (m : ℝ≥0∞)⁻¹ := by
    rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_inv_of_pos hmpos, ENNReal.ofReal_natCast]
  have hrestrict : Measure.map (fun x : ℝ => (m : ℝ) * x)
        (volume.restrict (Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹)))
      = (volume.map (fun x : ℝ => (m : ℝ) * x)).restrict (Set.Ioo (0 : ℝ) 1) := by
    rw [← hpre]
    exact (hemb.restrict_map volume (Set.Ioo (0 : ℝ) 1)).symm
  have hmap : Measure.map (fun x : ℝ => (m : ℝ) * x)
        (volume.restrict (Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹)))
      = (m : ℝ≥0∞)⁻¹ • volume.restrict (Set.Ioo (0 : ℝ) 1) := by
    rw [hrestrict, Real.map_volume_mul_left hmne, Measure.restrict_smul,
      abs_of_pos (inv_pos.mpr hmpos), ENNReal.ofReal_inv_of_pos hmpos,
      ENNReal.ofReal_natCast]
  calc
    Measure.map (fun x : ℝ => (m : ℝ) * x) (uniformInterval ((m : ℝ)⁻¹))
        = (volume (Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹)))⁻¹ •
            Measure.map (fun x : ℝ => (m : ℝ) * x)
              (volume.restrict (Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹))) := by
          rw [uniformInterval, Measure.map_smul]
    _ = (volume (Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹)))⁻¹ •
          ((m : ℝ≥0∞)⁻¹ • volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
          rw [hmap]
    _ = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
          rw [hvol, smul_smul, inv_inv,
            ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hm.ne') (ENNReal.natCast_ne_top m),
            one_smul]
    _ = uniformInterval 1 := by
          rw [uniformInterval, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, inv_one,
            one_smul]

/-- The coordinatewise dilation `x ↦ (m * x l)` pushes the uniform law on the cube
`(0, m⁻¹)^q` to the uniform law on the unit cube. -/
theorem map_mul_cubeMeasure (q : ℕ) (m : ℕ) (hm : 0 < m) :
    Measure.map (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l)
      (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) = cubeMeasure (Fin q) 1 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hprob : IsProbabilityMeasure (uniformInterval ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_uniformInterval (inv_pos.mpr hmpos)
  have hmapProb : ∀ _ : Fin q,
      IsProbabilityMeasure ((uniformInterval ((m : ℝ)⁻¹)).map (fun x : ℝ => (m : ℝ) * x)) :=
    fun _ => Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable
  have h := Measure.pi_map_pi (μ := fun _ : Fin q => uniformInterval ((m : ℝ)⁻¹))
    (f := fun _ (x : ℝ) => (m : ℝ) * x)
    (fun _ => (measurable_const_mul _).aemeasurable)
  simpa only [cubeMeasure, map_mul_uniformInterval m hm] using h

/-- The coordinatewise dilation of an iid sequence of uniform points on the cube of
side `m⁻¹` has the law of an iid sequence of uniform points on the unit cube. -/
theorem map_mul_cubeSeqLaw (q : ℕ) (m : ℕ) (hm : 0 < m) :
    Measure.map (fun w : ℕ → Fin q → ℝ => fun i l => (m : ℝ) * w i l)
      (Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) ((m : ℝ)⁻¹))) =
      cubeSeqLaw q := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hprob : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure (inv_pos.mpr hmpos)
  have hprobSeq : ∀ _ : ℕ, IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    fun _ => hprob
  have h := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => cubeMeasure (Fin q) ((m : ℝ)⁻¹))
    (f := fun _ (x : Fin q → ℝ) => fun l => (m : ℝ) * x l)
    (fun _ => by fun_prop)
  simpa only [map_mul_cubeMeasure q m hm, cubeSeqLaw] using h

/-- Dilation of a Poisson cloud whose points are uniform on the small cube
`(0, m⁻¹)^q` produces the Poisson cloud with points uniform on the unit cube; the
Poisson count is unchanged.

Note: the source law is the cloud of the small cube, i.e. the product of the Poisson
count with the iid sequence law of `cubeMeasure (Fin q) m⁻¹`.  Dilating the unit-cube
cloud `poissonCubeLaw q r` itself would instead produce the cloud of the cube of side
`m`, so an invariance statement for `poissonCubeLaw q r` on both sides is false for
`m ≠ 1`. -/
theorem map_mul_cubeSeqLaw_cloud (q : ℕ) (m : ℕ) (hm : 0 < m) (r : ℝ≥0) :
    Measure.map (fun z : PoissonCloudSpace q => (z.1, fun i l => (m : ℝ) * z.2 i l))
      ((poissonMeasure r).prod
        (Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) ((m : ℝ)⁻¹)))) =
      poissonCubeLaw q r := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hprob : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure (inv_pos.mpr hmpos)
  have hprobSeq : ∀ _ : ℕ, IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    fun _ => hprob
  have hg : Measurable (fun w : ℕ → Fin q → ℝ => fun i l => (m : ℝ) * w i l) := by
    fun_prop
  rw [poissonCubeLaw]
  change Measure.map (Prod.map id (fun w : ℕ → Fin q → ℝ => fun i l => (m : ℝ) * w i l))
      ((poissonMeasure r).prod
        (Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) ((m : ℝ)⁻¹)))) =
      (poissonMeasure r).prod (cubeSeqLaw q)
  rw [← Measure.map_prod_map (poissonMeasure r)
      (Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) ((m : ℝ)⁻¹)))
      measurable_id hg, Measure.map_id, map_mul_cubeSeqLaw q m hm]

/-- The inverse dilation `x ↦ (m⁻¹ * x l)` pushes the uniform law on the unit cube
to the uniform law on the cube `(0, m⁻¹)^q`. -/
theorem map_div_cubeMeasure (q : ℕ) (m : ℕ) (hm : 0 < m) :
    Measure.map (fun x : Fin q → ℝ => fun l => ((m : ℝ)⁻¹) * x l)
      (cubeMeasure (Fin q) 1) = cubeMeasure (Fin q) ((m : ℝ)⁻¹) := by
  have hmne : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hgf : (fun x : Fin q → ℝ => fun l => ((m : ℝ)⁻¹) * x l) ∘
      (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l) = id := by
    funext x l
    simp only [Function.comp_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hmne, one_mul]
    rfl
  have hg : Measurable (fun x : Fin q → ℝ => fun l => ((m : ℝ)⁻¹) * x l) := by
    fun_prop
  have hf : Measurable (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l) := by
    fun_prop
  calc
    Measure.map (fun x : Fin q → ℝ => fun l => ((m : ℝ)⁻¹) * x l)
        (cubeMeasure (Fin q) 1)
        = Measure.map (fun x : Fin q → ℝ => fun l => ((m : ℝ)⁻¹) * x l)
            (Measure.map (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l)
              (cubeMeasure (Fin q) ((m : ℝ)⁻¹))) := by
          rw [map_mul_cubeMeasure q m hm]
    _ = Measure.map ((fun x : Fin q → ℝ => fun l => ((m : ℝ)⁻¹) * x l) ∘
          (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l))
          (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) := by
          exact Measure.map_map hg hf
    _ = Measure.map id (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) := by
          rw [hgf]
    _ = cubeMeasure (Fin q) ((m : ℝ)⁻¹) := Measure.map_id

end OTSelector.Probability
