import OTSelector.Reconstruction.OriginalCurrentAllFacesTraceBound
import OTSelector.Analysis.Calculus.OrthonormalCubeEnergy
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessAffineScale

/-! True physical centered-cube boundary traces of the original stationary scene. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual physical centered cube of side R in the same selected frame. -/
def originalCenteredPhysicalCubeRegion {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) : Set (Fin q → ℝ) :=
  orthonormalPhysicalCubeRegion b (fun _ ↦ -R / 2) (fun _ ↦ R / 2)

/-- The normalized ordered face point is exactly the actual centered physical face point. -/
theorem orthonormalPhysicalCubeMap_centered_face_point {r : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
    (j : Fin (r + 1) × Fin 2) (R : ℝ) (y : Fin r → ℝ) :
    orthonormalPhysicalCubeMap b
      (j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) ((fun _ ↦ -R / 2) + R • y)) =
      EuclideanSpace.equiv (Fin (r + 1)) ℝ
        (originalCenteredCubeFaceOffset b j (R / 2) + orderedOrthonormalFaceMap b j.1 (R • y)) := by
  let C := (orthonormalCubeCoordinates b).symm
  have hc : C (fun _ : Fin (r + 1) ↦ -R / 2) = (-R / 2) • ∑ k, b k := by
    rw [orthonormalCubeCoordinates_symm_eq_sum]
    exact Finset.smul_sum.symm
  have hf (c : ℝ) : C (j.1.insertNth c y) = c • b j.1 + orderedOrthonormalFaceMap b j.1 y := by
    rw [orthonormalCubeCoordinates_symm_eq_sum, Fin.sum_univ_succAbove _ j.1]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rfl
  have hhalf : -R / 2 + R = R / 2 := by ring
  have hp : (fun _ : Fin (r + 1) ↦ -R / 2) +
      R • j.1.insertNth (if j.2 = 0 then 0 else 1) y =
      j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) ((fun _ ↦ -R / 2) + R • y) := by
    rw [affine_cube_face_insertNth]
    by_cases hs : j.2 = 0 <;> simp [hs, hhalf, Function.comp_def]
  rw [← hp]
  change EuclideanSpace.equiv (Fin (r + 1)) ℝ
    (C ((fun _ ↦ -R / 2) + R • j.1.insertNth (if j.2 = 0 then 0 else 1) y)) = _
  apply congrArg (EuclideanSpace.equiv (Fin (r + 1)) ℝ)
  rw [map_add, map_smul, hc, hf]
  by_cases hs : j.2 = 0
  · simp [originalCenteredCubeFaceOffset, hs, neg_div, map_smul]
  · simp [originalCenteredCubeFaceOffset, hs, neg_div, map_smul, smul_add]
    module

local instance originalPhysicalCubeColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {r : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin (r + 1) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching (r + 1) α β kin g)
  (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
  (x : Fin (r + 1) → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene (r + 1))))

/-- Each actual normal observable is sampled at the literal original rerooted physical face. -/
def LegalWeightedStationaryPoissonMatching.scenePhysicalCubeFaceReadout
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1))
    (j : Fin (r + 1) × Fin 2) (z : Fin r → ℝ) : ℝ :=
  x j.1 (legalMarkedInputSceneReroot (r + 1)
    (orthonormalPhysicalCubeMap b (j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) z)) s)

/-- The actual affine-normalized physical face samples equal the original all-face readouts. -/
theorem LegalWeightedStationaryPoissonMatching.scenePhysicalCubeFaceReadout_affine
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1))
    (j : Fin (r + 1) × Fin 2) (y : Fin r → ℝ) :
    Q.scenePhysicalCubeFaceReadout b x R s j ((fun _ ↦ -R / 2) + R • y) =
      Q.sceneAllFacesReadout b x R s j y := by
  unfold LegalWeightedStationaryPoissonMatching.scenePhysicalCubeFaceReadout
  rw [orthonormalPhysicalCubeMap_centered_face_point]
  change x j.1 (legalMarkedInputSceneReroot (r + 1) _ s) =
    x j.1 (legalMarkedInputSceneReroot (r + 1)
      (EuclideanSpace.equiv (Fin (r + 1)) ℝ (originalCenteredCubeFaceOffset b j (R / 2)) +
        EuclideanSpace.equiv (Fin (r + 1)) ℝ (orderedOrthonormalFaceMap b j.1 (R • y))) s)
  rw [map_add]

/-- The true signed coordinate-area pairing on the physical centered cube of side R. -/
def LegalWeightedStationaryPoissonMatching.scenePhysicalCubeBoundaryPairing
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1))
    (φ : (Fin (r + 1) → ℝ) → ℝ) : ℝ :=
  ∑ j : Fin (r + 1) × Fin 2, (if j.2 = 0 then (-1 : ℝ) else 1) *
    ∫ z in Icc (fun _ : Fin r ↦ -R / 2) (fun _ ↦ R / 2),
      Q.scenePhysicalCubeFaceReadout b x R s j z *
        φ (orthonormalPhysicalCubeMap b (j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) z))

private theorem scenePhysicalCubeBoundaryPairing_eq_affine
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1)) (φ : (Fin (r + 1) → ℝ) → ℝ) :
    Q.scenePhysicalCubeBoundaryPairing b x R s φ =
      originalAffineCubeBoundaryPairing (fun _ ↦ -R / 2) R
        (Q.scenePhysicalCubeFaceReadout b x R s) (φ ∘ orthonormalPhysicalCubeMap b) := by
  have hhalf : -R / 2 + R = R / 2 := by ring
  have ht : ((fun _ : Fin r ↦ -R / 2) + R • (1 : Fin r → ℝ)) = (fun _ ↦ R / 2) := by
    ext k
    simpa using hhalf
  simp only [LegalWeightedStationaryPoissonMatching.scenePhysicalCubeBoundaryPairing,
    originalAffineCubeBoundaryPairing, Function.comp_def, ht, hhalf]

private theorem ae_memLp_sceneAllFacesReadout (R : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ j : Fin (r + 1) × Fin 2,
      MemLp (Q.sceneAllFacesReadout b x R s j) 2
        (volume.restrict (Icc (0 : Fin r → ℝ) 1)) := by
  apply ae_all_iff.mpr
  intro j
  let L := orderedOrthonormalFaceMap b j.1
  let offset := fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)
  have hm : Measurable (fun p : LegalMarkedOptimalInputScene (r + 1) × (Fin r → ℝ) ↦
      Q.sceneScalarFaceReadout L offset (x j.1) R p.2 p.1) := by
    change Measurable ((Function.uncurry (Q.sceneScalarFaceReadout L offset (x j.1) R)) ∘
      (Prod.swap : LegalMarkedOptimalInputScene (r + 1) × (Fin r → ℝ) →
        (Fin r → ℝ) × LegalMarkedOptimalInputScene (r + 1)))
    exact (Q.measurable_sceneScalarFaceReadout L offset (x j.1) R).comp measurable_swap
  have hp := (Q.integrable_sq_sceneScalarFaceReadout_prod L offset (x j.1) R
    (A := Icc (0 : Fin r → ℝ) 1) isCompact_Icc.measure_lt_top.ne).swap
  filter_upwards [hp.prod_right_ae] with s hs
  exact (memLp_two_iff_integrable_sq
    (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hs

/-- One actual full-measure scene set controls every C1 physical zero-mean cube test,
with the genuine side-R volume power and the original full physical gradient energy. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_smooth_physicalCube_pairing_sq_le
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ (φ : (Fin (r + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ →
      (∫ z in originalCenteredPhysicalCubeRegion b R, φ z) = 0 →
      (Q.scenePhysicalCubeBoundaryPairing b x R s φ)^2 ≤
        R^(r + 1) * Q.sceneAllFacesTraceDualBound b x R s *
          ∑ k : Fin (r + 1), ∫ z in originalCenteredPhysicalCubeRegion b R,
            (fderiv ℝ φ z (Pi.single k 1))^2 := by
  filter_upwards [ae_memLp_sceneAllFacesReadout Q b x R] with s hs
  intro φ hφ hmean
  let a : Fin (r + 1) → ℝ := fun _ ↦ -R / 2
  have hu : a + R • 1 = (fun _ ↦ R / 2) := by
    ext k
    dsimp [a]
    ring
  have hg : ∀ j : Fin (r + 1) × Fin 2,
      MemLp (fun y ↦ Q.scenePhysicalCubeFaceReadout b x R s j (a ∘ j.1.succAbove + R • y)) 2
        (volume.restrict (Icc (0 : Fin r → ℝ) 1)) := by
    intro j
    simpa only [a, Function.comp_def, Q.scenePhysicalCubeFaceReadout_affine] using hs j
  have hm : (∫ y in Icc a (a + R • 1), (φ ∘ orthonormalPhysicalCubeMap b) y) = 0 := by
    simp only [Function.comp_apply]
    rw [hu, ← integral_orthonormalPhysicalCubeRegion b a (fun _ ↦ R / 2) φ]
    exact hmean
  have hE : originalRawBoxGradientEnergy a (a + R • 1) (φ ∘ orthonormalPhysicalCubeMap b) =
      ∑ k : Fin (r + 1), ∫ z in originalCenteredPhysicalCubeRegion b R,
        (fderiv ℝ φ z (Pi.single k 1))^2 := by
    unfold originalRawBoxGradientEnergy
    rw [sum_integral_sq_fderiv_comp_orthonormalPhysicalCubeMap b a (a + R • 1) hφ, hu]
    rfl
  have hh := smooth_affineCube_all_faces_pairing_sq_le a hR hg
    (hφ.comp (orthonormalPhysicalCubeMap b).contDiff) hm
  rw [hE] at hh
  rw [scenePhysicalCubeBoundaryPairing_eq_affine]
  simpa only [a, Function.comp_def, Q.scenePhysicalCubeFaceReadout_affine,
    LegalWeightedStationaryPoissonMatching.sceneAllFacesTraceDualBound] using hh

/-- The actual coefficient multiplying the full physical gradient energy. -/
def LegalWeightedStationaryPoissonMatching.scenePhysicalCubeTraceDualBound
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1)) : ℝ :=
  R^(r + 1) * Q.sceneAllFacesTraceDualBound b x R s

/-- The physical coefficient is nonnegative at every nonnegative side length. -/
theorem LegalWeightedStationaryPoissonMatching.scenePhysicalCubeTraceDualBound_nonneg
    {R : ℝ} (hR : 0 ≤ R) (s : LegalMarkedOptimalInputScene (r + 1)) :
    0 ≤ Q.scenePhysicalCubeTraceDualBound b x R s :=
  mul_nonneg (pow_nonneg hR _) (Q.sceneAllFacesTraceDualBound_nonneg b x R s)

/-- The actual coefficient is measurable for every side length. -/
theorem LegalWeightedStationaryPoissonMatching.measurable_scenePhysicalCubeTraceDualBound
    (R : ℝ) : Measurable (Q.scenePhysicalCubeTraceDualBound b x R) :=
  (Q.measurable_sceneAllFacesTraceDualBound b x R).const_mul _

/-- The actual coefficient is integrable under the same original scene law. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_scenePhysicalCubeTraceDualBound
    (R : ℝ) : Integrable (Q.scenePhysicalCubeTraceDualBound b x R) (Q.law : Measure _) :=
  (Q.integrable_sceneAllFacesTraceDualBound b x R).const_mul _

/-- Its genuinely normalized expectation vanishes from the actual normal projection inputs. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_integral_scenePhysicalCubeTraceDualBound_div_volume_zero
    (hproj : ∀ i : Fin (r + 1),
      (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection (x i) = 0) :
    Tendsto (fun R : ℝ ↦ (∫ s, Q.scenePhysicalCubeTraceDualBound b x R s ∂(Q.law : Measure _)) /
      R^(r + 1)) atTop (𝓝 0) := by
  have he : (fun R : ℝ ↦ (∫ s, Q.scenePhysicalCubeTraceDualBound b x R s ∂(Q.law : Measure _)) /
        R^(r + 1)) =ᶠ[atTop]
      (fun R : ℝ ↦ ∫ s, Q.sceneAllFacesTraceDualBound b x R s ∂(Q.law : Measure _)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    unfold LegalWeightedStationaryPoissonMatching.scenePhysicalCubeTraceDualBound
    rw [integral_const_mul]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hR.ne')
  exact (Q.tendsto_integral_sceneAllFacesTraceDualBound_zero b x hproj).congr' he.symm

end OTSelector.Reconstruction
