import OTSelector.Reconstruction.FinslerOriginalCubeSingletonNullity
import OTSelector.Reconstruction.OriginalReserveMappedWindowSampler
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolume

/-! Actual original Poisson array labels are distinct after the same physical cube map. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The genuine oriented physical placement is injective for every nonzero cube radius. -/
theorem originalOrientedRawCubePhysicalMap_injective {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : R ≠ 0) : Injective (originalOrientedRawCubePhysicalMap b R) := by
  intro v z hvz
  have h := (orthonormalPhysicalCubeMap b).injective hvz
  ext i
  have hi := congrFun h i
  change 2*R*v i-R = 2*R*z i-R at hi
  have hR2 : 2*R ≠ 0 := mul_ne_zero (by norm_num) hR
  exact (mul_left_cancel₀ hR2) (by linarith only [hi])

/-- Both literal original finite marked arrays are injective almost surely.
This follows from the actual raw Poisson law and positive-dimensional spatial
atomlessness, with no condition on clock atoms or sample counts. -/
theorem ae_injective_originalMappedReserveCloudArrays {q : ℕ} (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : R ≠ 0) :
    ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate,
      Injective (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R)
        cloud).1.2 ∧
      Injective (originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R)
        cloud).2.2 := by
  have hs : ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate, Injective cloud.1.2 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact ae_of_all _ (fun _ _ ↦ hij)
    · filter_upwards [twoMarkedCloudLaw_ae_source_marks_ne hq α β rate hij] with cloud hc
      exact fun he ↦ False.elim (hc he)
  have ht : ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate, Injective cloud.2.2 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact ae_of_all _ (fun _ _ ↦ hij)
    · filter_upwards [twoMarkedCloudLaw_ae_target_marks_ne hq α β rate hij] with cloud hc
      exact fun he ↦ False.elim (hc he)
  have hmap : Injective (Prod.map (originalOrientedRawCubePhysicalMap b R) (id : ℝ → ℝ)) :=
    (originalOrientedRawCubePhysicalMap_injective b hR).prodMap injective_id
  filter_upwards [hs, ht] with cloud hsource htarget
  constructor
  · intro i j hij
    apply Fin.ext
    exact hsource (hmap hij)
  · intro i j hij
    apply Fin.ext
    exact htarget (hmap hij)

end OTSelector.Reconstruction
