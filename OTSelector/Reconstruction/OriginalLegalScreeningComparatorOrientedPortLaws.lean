import OTSelector.Reconstruction.OriginalStagePhysicalPortProbability
import OTSelector.Reconstruction.OriginalStagePortAtomLaws

/-! The actual original finite port arrays yield physical probability families
with true unit Euclidean error and exact class measure readouts. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The literal canonical reflected law attached to the same original port,
read in its actual Euclidean physical coordinates. -/
def originalPhysicalOrientedPortLaw {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (x : Fin q → ℝ) :=
  (originalPhysicalPortProbabilityMeasure b R x).map (EuclideanSpace.equiv (Fin q) ℝ).symm

/-- The actual port law is a probability and pays at most one unit of genuine
Euclidean square deviation, without a coordinate dimension factor. -/
theorem originalPhysicalOrientedPortLaw_spec {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    {x : Fin q → ℝ} (hx : x ∈ originalCenteredPhysicalCubeRegion b (2*R)) :
    IsProbabilityMeasure (originalPhysicalOrientedPortLaw b R x) ∧
    Integrable (fun v ↦ dist ((EuclideanSpace.equiv (Fin q) ℝ).symm x) v^2)
      (originalPhysicalOrientedPortLaw b R x) ∧
    (∫ v, dist ((EuclideanSpace.equiv (Fin q) ℝ).symm x) v^2
      ∂originalPhysicalOrientedPortLaw b R x) ≤ 1 := by
  have : IsProbabilityMeasure (originalPhysicalPortProbabilityMeasure b R x) :=
    originalPhysicalPortProbabilityMeasure_isProbability b hR hx
  let e := (EuclideanSpace.equiv (Fin q) ℝ).symm
  have he : Measurable e := e.continuous.measurable
  have hprob : IsProbabilityMeasure (originalPhysicalOrientedPortLaw b R x) :=
    Measure.isProbabilityMeasure_map he.aemeasurable
  have hd : ∀ᵐ v ∂originalPhysicalOrientedPortLaw b R x, dist (e x) v ≤ 1 := by
    apply (ae_map_iff he.aemeasurable (measurableSet_le
      (measurable_const.dist measurable_id) measurable_const)).2
    filter_upwards [originalPhysicalPortProbabilityMeasure_ae_euclidean_deviation_le_one b hx] with v hv
    change dist (e x) (e v) ≤ 1
    rw [dist_comm, dist_eq_norm, ← map_sub]
    exact hv
  have hb : ∀ᵐ v ∂originalPhysicalOrientedPortLaw b R x, dist (e x) v^2 ≤ (1 : ℝ) :=
    hd.mono (fun v hv ↦ by nlinarith [dist_nonneg (x := e x) (y := v)])
  have hI : Integrable (fun v ↦ dist (e x) v^2) (originalPhysicalOrientedPortLaw b R x) :=
    Integrable.of_bound ((measurable_const.dist measurable_id).pow_const 2).aestronglyMeasurable 1
      (hb.mono (fun v hv ↦ by
        change |dist (e x) v^2| ≤ 1
        rwa [abs_of_nonneg (sq_nonneg (dist (e x) v))]))
  refine ⟨hprob, hI, ?_⟩
  have h := integral_mono_ae hI (integrable_const (1 : ℝ)) hb
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using h

/-- The physical class sum uses the identical original endpoint labels. -/
theorem originalFiniteEndpointAtoms_physicalOrientedPortClassMeasure {q n : ℕ}
    (points : Fin n → LegalMarkedPhysicalPoint q) (C : Set ℝ) (hC : MeasurableSet C)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    (((volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))).withDensity
      (fun z ↦ ENNReal.ofReal (originalOrientedStageReflectedClassDensity b R C
        (∑ i, Measure.dirac (points i)) z))).map (EuclideanSpace.equiv (Fin q) ℝ).symm) =
      ∑ i, if (points i).2 ∈ C then originalPhysicalOrientedPortLaw b R (points i).1 else 0 := by
  unfold originalOrientedStageReflectedClassDensity
  rw [originalFiniteEndpointAtoms_classMeasure points C hC
    (originalCanonicalOrientedReflectedKernel b R)
    (measurable_originalCanonicalOrientedReflectedKernel b R)
    (originalCanonicalOrientedReflectedKernel_nonneg b R),
    Measure.map_finset_sum' (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rfl
  · exact Measure.map_zero _


end OTSelector.Reconstruction
