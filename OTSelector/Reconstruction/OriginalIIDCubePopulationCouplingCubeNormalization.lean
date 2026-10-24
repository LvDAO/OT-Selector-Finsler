import OTSelector.Probability.PoissonCubePressure
import OTSelector.Probability.InfiniteProductLaw
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingPhysicalGeometry

/-! The actual open unit-cube sampler enters the closed cube without changing
any coordinate on its full-measure support. -/

open MeasureTheory Set
open OTSelector.Probability

noncomputable section
namespace OTSelector.Reconstruction

/-- Global coordinate clamping into the actual closed unit cube. -/
def originalUnitCubeNormalization {q : ℕ} (v : Fin q → ℝ) : DyadicUnitCube q :=
  fun i ↦ ⟨max 0 (min 1 (v i)), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

/-- The global normalization is measurable, including inputs outside the cube. -/
theorem measurable_originalUnitCubeNormalization {q : ℕ} :
    Measurable (originalUnitCubeNormalization (q := q)) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.max (measurable_const.min (measurable_pi_apply i))).subtype_mk

/-- Closed-cube coordinates are preserved literally by normalization. -/
theorem dyadicCubePoint_originalUnitCubeNormalization_of_closed {q : ℕ}
    (v : Fin q → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    dyadicCubePoint (originalUnitCubeNormalization v) = v := by
  funext i
  simp only [dyadicCubePoint, originalUnitCubeNormalization,
    min_eq_right (hv i).2, max_eq_right (hv i).1]

/-- Every original open unit-cube observation is unchanged. -/
theorem dyadicCubePoint_originalUnitCubeNormalization_of_mem_unitCube {q : ℕ}
    (v : Fin q → ℝ) (hv : v ∈ unitCube q) :
    dyadicCubePoint (originalUnitCubeNormalization v) = v :=
  dyadicCubePoint_originalUnitCubeNormalization_of_closed v fun i ↦
    ⟨(mem_pi.mp hv i (mem_univ i)).1.le, (mem_pi.mp hv i (mem_univ i)).2.le⟩

/-- The true cube sampler, represented in the closed cube by the global map. -/
def originalNormalizedCubeLaw (q : ℕ) : Measure (DyadicUnitCube q) :=
  (cubeMeasure (Fin q) 1).map originalUnitCubeNormalization

instance originalNormalizedCubeLaw_isProbabilityMeasure (q : ℕ) :
    IsProbabilityMeasure (originalNormalizedCubeLaw q) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  exact Measure.isProbabilityMeasure_map measurable_originalUnitCubeNormalization.aemeasurable

/-- Reading coordinates recovers exactly the actual original unit-cube law;
its full-measure support is proved from the original sampler internally. -/
theorem map_dyadicCubePoint_originalNormalizedCubeLaw (q : ℕ) :
    (originalNormalizedCubeLaw q).map dyadicCubePoint = cubeMeasure (Fin q) 1 := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have hm : Measurable (dyadicCubePoint (q := q)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  have hmem : unitCube q ∈ ae (cubeMeasure (Fin q) 1) :=
    (mem_ae_iff_prob_eq_one (measurableSet_unitCube q)).2 (cubeMeasure_unitCube q)
  rw [originalNormalizedCubeLaw, Measure.map_map hm measurable_originalUnitCubeNormalization]
  calc
    _ = (cubeMeasure (Fin q) 1).map id := Measure.map_congr (by
      filter_upwards [hmem] with v hv
      exact dyadicCubePoint_originalUnitCubeNormalization_of_mem_unitCube v hv)
    _ = _ := Measure.map_id

/-- Normalizing every original iid position produces the exact closed-cube iid law. -/
theorem map_originalUnitCubeNormalization_infinitePi (q : ℕ) :
    (Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1)).map
      (fun word i ↦ originalUnitCubeNormalization (word i)) =
        Measure.infinitePi (fun _ : ℕ ↦ originalNormalizedCubeLaw q) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  exact Measure.infinitePi_map_pi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1)
    (fun _ ↦ measurable_originalUnitCubeNormalization)

/-- Coordinate readout also recovers the full original infinite sampler law. -/
theorem map_dyadicCubePoint_originalNormalizedCubeLaw_infinitePi (q : ℕ) :
    (Measure.infinitePi (fun _ : ℕ ↦ originalNormalizedCubeLaw q)).map
      (fun word i ↦ dyadicCubePoint (word i)) =
        Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1) := by
  have hm : Measurable (dyadicCubePoint (q := q)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  rw [Measure.infinitePi_map_pi (fun _ : ℕ ↦ originalNormalizedCubeLaw q) (fun _ ↦ hm)]
  simp_rw [map_dyadicCubePoint_originalNormalizedCubeLaw]

/-- The literal centered physical affine cube agrees with the original
unit-cube coordinate formula, at every original closed-cube observation. -/
theorem originalIIDCubePhysicalMap_normalization_affine {q : ℕ}
    (R : ℝ) (v : Fin q → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    originalIIDCubePhysicalMap
      ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2 * R)
      (originalUnitCubeNormalization v) =
        (EuclideanSpace.equiv (Fin q) ℝ).symm (fun i ↦ 2 * R * v i - R) := by
  have hpoint := dyadicCubePoint_originalUnitCubeNormalization_of_closed v hv
  ext i
  change -R + (2 * R) * dyadicCubePoint (originalUnitCubeNormalization v) i =
    2 * R * v i - R
  rw [hpoint]
  ring

end OTSelector.Reconstruction
