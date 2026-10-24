import OTSelector.MeasureTheory.Integral.CommonShell
import OTSelector.Probability.CavitySemidiscreteRootedWitness
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Translation boundary error of actual multidimensional Haar roots

A bounded observable of any fixed original environment is averaged over a
spatial cube. Translating that root changes only a concrete boundary shell.
The normalized shell mass vanishes at every diverging real cube radius.
-/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- A common geometric core compares two actual Haar set integrals using only
mass in their common outer shell. -/
theorem norm_setIntegral_sub_le_common_shell
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s t core outer : Set X} (hcore : MeasurableSet core)
    (hfinite : μ outer < ∞) (hcs : core ⊆ s) (hct : core ⊆ t)
    (hso : s ⊆ outer) (hto : t ⊆ outer)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ‖ ≤
      2 * C * (μ.real outer - μ.real core) := by
  exact OTSelector.Probability.norm_setIntegral_sub_le_common_shell_banach μ
    hcore hfinite hcs hct hso hto hf.aestronglyMeasurable hC hbound

variable (ι : Type*) [Fintype ι]

/-- The actual centered spatial root cube in all transverse dimensions. -/
def haarRootCube (R : ℝ) : Set (ι → ℝ) := Icc (fun _ ↦ -R) (fun _ ↦ R)

/-- The same original normalized restricted Haar measure used for physical
scene rooting, specialized to its actual finite-volume cube. -/
def haarCubeRootLaw (R : ℝ) : Measure (ι → ℝ) :=
  cavityRootMeasure volume (haarRootCube ι R) ((2 * R) ^ Fintype.card ι)

@[simp]
theorem volume_haarRootCube {R : ℝ} (hR : 0 ≤ R) :
    volume (haarRootCube ι R) = ENNReal.ofReal ((2 * R) ^ Fintype.card ι) := by
  simp only [haarRootCube, Real.volume_Icc_pi, sub_neg_eq_add,
    ← two_mul, Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * R)]

@[simp]
theorem volume_real_haarRootCube {R : ℝ} (hR : 0 ≤ R) :
    volume.real (haarRootCube ι R) = (2 * R) ^ Fintype.card ι := by
  rw [measureReal_def, volume_haarRootCube ι hR, ENNReal.toReal_ofReal (by positivity)]

theorem isProbabilityMeasure_haarCubeRootLaw {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (haarCubeRootLaw ι R) :=
  isProbabilityMeasure_cavityRootMeasure volume (haarRootCube ι R)
    ((2 * R) ^ Fintype.card ι) (by positivity) (volume_haarRootCube ι hR.le)

theorem integral_haarCubeRootLaw {R : ℝ} (hR : 0 ≤ R) (f : (ι → ℝ) → ℝ) :
    (∫ z, f z ∂haarCubeRootLaw ι R) =
      ((2 * R) ^ Fintype.card ι)⁻¹ * ∫ z in haarRootCube ι R, f z := by
  rw [haarCubeRootLaw, cavityRootMeasure, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

omit [Fintype ι] in
/-- Every fixed root shift fits between one inner and one outer actual cube. -/
theorem haarRootCube_shift_shell (v : ι → ℝ) {R S : ℝ}
    (hS : 0 ≤ S) (hv : ∀ i, |v i| ≤ S) :
    haarRootCube ι (R - S) ⊆ haarRootCube ι R ∧
    haarRootCube ι (R - S) ⊆ (fun z ↦ z + v) '' haarRootCube ι R ∧
    haarRootCube ι R ⊆ haarRootCube ι (R + S) ∧
    (fun z ↦ z + v) '' haarRootCube ι R ⊆ haarRootCube ι (R + S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    constructor <;> intro i <;> have h := hz.1 i <;> have h' := hz.2 i <;> dsimp at * <;> linarith
  · intro z hz
    refine ⟨z - v, ?_, sub_add_cancel z v⟩
    constructor <;> intro i <;> have h := hz.1 i <;> have h' := hz.2 i <;>
      have hi := abs_le.mp (hv i) <;> dsimp at * <;> linarith
  · intro z hz
    constructor <;> intro i <;> have h := hz.1 i <;> have h' := hz.2 i <;> dsimp at * <;> linarith
  · rintro z ⟨x, hx, rfl⟩
    constructor <;> intro i <;> have h := hx.1 i <;> have h' := hx.2 i <;>
      have hi := abs_le.mp (hv i) <;> dsimp at * <;> linarith

/-- A concrete shell estimate for the actual root's translated bounded
observable, valid in any finite transverse dimension. -/
theorem norm_integral_haarCubeRootLaw_shift_sub_le
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖f z‖ ≤ C) (v : ι → ℝ) {R S : ℝ}
    (hS : 0 ≤ S) (hRS : S ≤ R) (hv : ∀ i, |v i| ≤ S) :
    ‖(∫ z, f (z + v) ∂haarCubeRootLaw ι R) - ∫ z, f z ∂haarCubeRootLaw ι R‖ ≤
      2 * C * (((2 * (R + S)) ^ Fintype.card ι -
        (2 * (R - S)) ^ Fintype.card ι) / (2 * R) ^ Fintype.card ι) := by
  have hR : 0 ≤ R := hS.trans hRS
  have hshape := haarRootCube_shift_shell ι v (R := R) hS hv
  have houter : volume (haarRootCube ι (R + S)) < ∞ := isCompact_Icc.measure_lt_top
  have hset := norm_setIntegral_sub_le_common_shell volume
    (s := (fun z ↦ z + v) '' haarRootCube ι R) (t := haarRootCube ι R)
    (core := haarRootCube ι (R - S)) (outer := haarRootCube ι (R + S))
    measurableSet_Icc houter hshape.2.1 hshape.1 hshape.2.2.2 hshape.2.2.1 hf hC hbound
  rw [(measurePreserving_add_right volume v).setIntegral_image_emb
    (MeasurableEquiv.addRight v).measurableEmbedding] at hset
  rw [volume_real_haarRootCube ι (by linarith),
    volume_real_haarRootCube ι (sub_nonneg.mpr hRS)] at hset
  rw [integral_haarCubeRootLaw ι hR, integral_haarCubeRootLaw ι hR,
    ← mul_sub, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((2 * R) ^ Fintype.card ι)⁻¹ *
        (2 * C * ((2 * (R + S)) ^ Fintype.card ι -
          (2 * (R - S)) ^ Fintype.card ι)) :=
      mul_le_mul_of_nonneg_left hset (by positivity)
    _ = _ := by ring

/-- The explicit normalized finite-dimensional shell mass vanishes along all
real root radii. No stationarity assumption on the environment is involved. -/
theorem tendsto_haarCube_boundaryError (q : ℕ) (C S : ℝ) :
    Tendsto (fun R : ℝ ↦ 2 * C *
      (((2 * (R + S)) ^ q - (2 * (R - S)) ^ q) / (2 * R) ^ q))
      atTop (𝓝 0) := by
  have hsmall : Tendsto (fun R : ℝ ↦ S / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h : Tendsto (fun R : ℝ ↦ (1 + S / R) ^ q - (1 - S / R) ^ q) atTop (𝓝 (0 : ℝ)) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add hsmall).pow q).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).pow q)
  have hzero : Tendsto (fun R : ℝ ↦
      2 * C * ((1 + S / R) ^ q - (1 - S / R) ^ q)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul h
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  congr 1
  rw [sub_div, ← div_pow, ← div_pow]
  have hp : 2 * (R + S) / (2 * R) = 1 + S / R := by field_simp
  have hm : 2 * (R - S) / (2 * R) = 1 - S / R := by field_simp
  rw [hp, hm]

end OTSelector.Reconstruction
