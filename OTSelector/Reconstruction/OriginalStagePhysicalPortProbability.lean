import OTSelector.Reconstruction.OriginalStagePhysicalPortKernelSupport
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedReflectedMass
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Each unchanged original port endpoint yields a true physical reflected probability law. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual physical reflected law of one unchanged original port endpoint. -/
def originalPhysicalPortProbabilityMeasure {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (x : Fin q → ℝ) :
    Measure (Fin q → ℝ) :=
  (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))).withDensity
    (fun z ↦ ENNReal.ofReal (originalCanonicalOrientedReflectedKernel b R z x))

/-- The same actual endpoint inside the physical cube has a genuinely normalized port
law. Unit mass comes from reflection and the canonical mollifier, rather than a premise. -/
theorem originalPhysicalPortProbabilityMeasure_isProbability {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    {x : Fin q → ℝ} (hx : x ∈ originalCenteredPhysicalCubeRegion b (2 * R)) :
    IsProbabilityMeasure (originalPhysicalPortProbabilityMeasure b R x) := by
  have hsupp : ∀ᵐ p ∂(Measure.dirac (x, (0 : ℝ))),
      p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R) := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hx
  have hm := originalOrientedStageReflectedClassDensity_integrable_mass b hR
    (Measure.dirac (x, (0 : ℝ))) hsupp univ
  have hdensity : originalOrientedStageReflectedClassDensity b R univ (Measure.dirac (x, (0 : ℝ))) =
      fun z ↦ originalCanonicalOrientedReflectedKernel b R z x := by
    funext z
    unfold originalOrientedStageReflectedClassDensity
    have he : {p : LegalMarkedPhysicalPoint q | p.2 ∈ (univ : Set ℝ)} = univ := by simp
    rw [he, Measure.restrict_univ, integral_dirac]
  have hi : Integrable (fun z ↦ originalCanonicalOrientedReflectedKernel b R z x)
      (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) := by
    rw [hdensity] at hm
    exact hm.1
  constructor
  rw [originalPhysicalPortProbabilityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun z ↦ originalCanonicalOrientedReflectedKernel_nonneg b R z x)),
    integral_originalCanonicalOrientedReflectedKernel_eq_one b hR hx]
  simp

/-- Original physical port smoothing moves the same endpoint by at most one in the genuine
Euclidean metric. No factor depending on dimension is inserted. -/
theorem originalPhysicalPortProbabilityMeasure_ae_euclidean_deviation_le_one {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ}
    {x : Fin q → ℝ} (hx : x ∈ originalCenteredPhysicalCubeRegion b (2 * R)) :
    ∀ᵐ z ∂originalPhysicalPortProbabilityMeasure b R x,
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (z - x)‖ ≤ 1 := by
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  have hK : MeasurableSet K := (isCompact_originalStagePhysicalCube b (2 * R)).measurableSet
  have hbad : MeasurableSet {z : Fin q → ℝ |
      ¬ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (z - x)‖ ≤ 1} := by
    exact (measurableSet_le (((EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable).comp
      (measurable_id.sub_const x)).norm measurable_const).compl
  apply ae_iff.mpr
  rw [originalPhysicalPortProbabilityMeasure, withDensity_apply _ hbad]
  have hzero : (fun z ↦ ENNReal.ofReal (originalCanonicalOrientedReflectedKernel b R z x)) =ᵐ[
      (volume.restrict K).restrict {z | ¬ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (z - x)‖ ≤ 1}] 0 := by
    filter_upwards [ae_restrict_of_ae (ae_restrict_mem hK), ae_restrict_mem hbad] with z hz hd
    rw [originalCanonicalOrientedReflectedKernel_eq_zero_of_one_le_euclidean b hz hx (le_of_lt (lt_of_not_ge hd))]
    simp only [ENNReal.ofReal_zero, Pi.zero_apply]
  exact (lintegral_congr_ae hzero).trans (lintegral_zero)

end OTSelector.Reconstruction
