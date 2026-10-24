import OTSelector.PointProcess.RootedCampbell
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Actual multidimensional Campbell/Palm factorization

An invariant location-rooted mark measure factors through its actual unit-cube
Palm readout. The coefficient is proved from the original finite unit-cube
mass, in the full transverse dimension rather than a scalar replacement.
-/
open Set Function MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable (ι : Type*) [Fintype ι]

/-- The physical unit spatial cube, whose Haar mass is exactly one. -/
def palmUnitCube : Set (ι → ℝ) := Icc (fun _ ↦ 0) (fun _ ↦ 1)

theorem measurableSet_palmUnitCube : MeasurableSet (palmUnitCube ι) := measurableSet_Icc

@[simp]
theorem volume_palmUnitCube : volume (palmUnitCube ι) = 1 := by
  simp [palmUnitCube, Real.volume_Icc_pi]

/-- An invariant actual spatial measure with finite mass on the physical unit
cube is locally finite in every transverse dimension. -/
theorem locallyFinite_of_invariant_unitCube
    (ν : Measure (ι → ℝ)) [ν.IsAddLeftInvariant]
    (hunit : ν (palmUnitCube ι) < ∞) : IsLocallyFiniteMeasure ν := by
  have hball : Metric.ball (fun _ : ι ↦ (1 / 2 : ℝ)) (1 / 2) ⊆ palmUnitCube ι := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hi (i : ι) : |y i - 1 / 2| < 1 / 2 := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (y - fun _ ↦ (1 / 2 : ℝ)) i).trans_lt hy
    constructor <;> intro i <;> have h := abs_lt.mp (hi i) <;> dsimp <;> linarith
  constructor
  intro x
  let a : ι → ℝ := fun i ↦ 1 / 2 - x i
  let U : Set (ι → ℝ) := Metric.ball (fun _ ↦ (1 / 2 : ℝ)) (1 / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have haM : Measurable (fun y : ι → ℝ ↦ a + y) := measurable_const.add measurable_id
  refine ⟨(fun y ↦ a + y) ⁻¹' U, ?_, ?_⟩
  · apply (hU.preimage (continuous_const.add continuous_id)).mem_nhds
    have hx : a + x = fun _ ↦ (1 / 2 : ℝ) := by funext i; dsimp [a]; ring
    change a + x ∈ U
    rw [hx]
    exact Metric.mem_ball_self (by norm_num)
  · have heq : ν ((fun y ↦ a + y) ⁻¹' U) = ν U := by
      rw [← Measure.map_apply haM hU.measurableSet,
        IsAddLeftInvariant.map_add_left_eq_self]
    rw [heq]
    exact (measure_mono hball).trans_lt hunit

/-- Haar uniqueness determines the exact scalar from the actual physical
unit-cube mass. -/
theorem invariant_eq_unitCube_smul_volume
    (ν : Measure (ι → ℝ)) [ν.IsAddLeftInvariant]
    (hunit : ν (palmUnitCube ι) < ∞) :
    ν = ν (palmUnitCube ι) • (volume : Measure (ι → ℝ)) := by
  let := locallyFinite_of_invariant_unitCube ι ν hunit
  have h := isAddLeftInvariant_eq_smul ν (volume : Measure (ι → ℝ))
  have hc : ν (palmUnitCube ι) = (ν.addHaarScalarFactor volume : ℝ≥0∞) := by
    have hh := congrArg (fun μ : Measure (ι → ℝ) ↦ μ (palmUnitCube ι)) h
    simpa using hh
  simpa only [hc, ENNReal.smul_def] using h

variable {M : Type*} [MeasurableSpace M]

/-- The actual unnormalized Palm law read from the physical spatial unit cube. -/
def cubePalm (C : Measure ((ι → ℝ) × M)) : Measure M :=
  (C.restrict (palmUnitCube ι ×ˢ univ)).map Prod.snd

omit [Fintype ι] in
theorem cubePalm_apply (C : Measure ((ι → ℝ) × M)) {B : Set M} (hB : MeasurableSet B) :
    cubePalm ι C B = C (palmUnitCube ι ×ˢ B) := by
  rw [cubePalm, Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  exact and_comm

/-- Spatial mass for any retained rooted mark class. -/
def cubeMarkedSpatialMeasure (C : Measure ((ι → ℝ) × M)) (B : Set M) : Measure (ι → ℝ) :=
  (C.restrict (Prod.snd ⁻¹' B)).map Prod.fst

omit [Fintype ι] in
theorem cubeMarkedSpatialMeasure_apply (C : Measure ((ι → ℝ) × M)) (B : Set M)
    {A : Set (ι → ℝ)} (hA : MeasurableSet A) :
    cubeMarkedSpatialMeasure ι C B A = C (A ×ˢ B) := by
  rw [cubeMarkedSpatialMeasure, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  rfl

omit [Fintype ι] in
/-- Original spatial invariance passes to each actual mark class. -/
theorem invariant_cubeMarkedSpatialMeasure (C : Measure ((ι → ℝ) × M))
    (hstat : ∀ a : ι → ℝ, MeasurePreserving (fun z : (ι → ℝ) × M ↦ (a + z.1, z.2)) C C)
    {B : Set M} (hB : MeasurableSet B) :
    (cubeMarkedSpatialMeasure ι C B).IsAddLeftInvariant := by
  constructor
  intro a
  have ha : Measurable (fun x : ι → ℝ ↦ a + x) := measurable_const.add measurable_id
  ext A hA
  rw [Measure.map_apply ha hA, cubeMarkedSpatialMeasure_apply ι C B (ha hA),
    cubeMarkedSpatialMeasure_apply ι C B hA]
  have h := congrArg (fun μ : Measure ((ι → ℝ) × M) ↦ μ (A ×ˢ B)) (hstat a).map_eq
  rw [Measure.map_apply (hstat a).measurable (hA.prod hB)] at h
  exact h

/-- The multidimensional Campbell factorization is produced from actual
spatial invariance and one finite unit-cube moment. -/
theorem campbell_eq_volume_prod_cubePalm (C : Measure ((ι → ℝ) × M))
    (hstat : ∀ a : ι → ℝ, MeasurePreserving (fun z : (ι → ℝ) × M ↦ (a + z.1, z.2)) C C)
    (hunit : C (palmUnitCube ι ×ˢ univ) < ∞) :
    C = (volume : Measure (ι → ℝ)).prod (cubePalm ι C) := by
  have : IsFiniteMeasure (cubePalm ι C) := by
    constructor
    rwa [cubePalm_apply ι C MeasurableSet.univ]
  symm
  apply Measure.prod_eq
  intro A B hA hB
  let := invariant_cubeMarkedSpatialMeasure ι C hstat hB
  have hCube : MeasurableSet (palmUnitCube ι) := measurableSet_Icc
  have hfinite : cubeMarkedSpatialMeasure ι C B (palmUnitCube ι) < ∞ := by
    rw [cubeMarkedSpatialMeasure_apply ι C B hCube]
    exact (measure_mono (prod_mono_right (subset_univ B))).trans_lt hunit
  have h := congrArg (fun μ : Measure (ι → ℝ) ↦ μ A)
    (invariant_eq_unitCube_smul_volume ι (cubeMarkedSpatialMeasure ι C B) hfinite)
  simpa only [cubeMarkedSpatialMeasure_apply ι C B hA, Measure.smul_apply, smul_eq_mul,
    cubeMarkedSpatialMeasure_apply ι C B hCube, cubePalm_apply ι C hB,
    mul_comm] using h

end OTSelector.Reconstruction
