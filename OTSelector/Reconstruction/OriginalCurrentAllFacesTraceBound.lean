import OTSelector.Reconstruction.OriginalCurrentCubeTraceDualBound
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessAllFaces
import OTSelector.Analysis.Sobolev.CubeTraceFaceGeometry

/-! A single vanishing actual random bound for all faces of the same selected cube. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Ordered tangent coordinates omit the normal coordinate and retain its actual basis order. -/
def orderedOrthonormalFaceMap {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (i : Fin (r + 1)) :
    (Fin r → ℝ) →ₗ[ℝ] E where
  toFun y := ∑ k, y k • b (i.succAbove k)
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp [mul_smul, Finset.smul_sum]

/-- The ordered tangent map covers exactly the true normal's orthogonal hyperplane. -/
theorem range_orderedOrthonormalFaceMap {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (i : Fin (r + 1)) :
    (orderedOrthonormalFaceMap b i).range = (ℝ ∙ b i)ᗮ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.2
    change ⟪b i, ∑ k : Fin r, y k • b (i.succAbove k)⟫_ℝ = 0
    simp only [inner_sum, inner_smul_right]
    apply Finset.sum_eq_zero
    intro k _
    rw [b.inner_eq_zero (Fin.ne_succAbove i k), mul_zero]
  · intro hx
    have hz : ⟪b i, x⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 hx
    refine ⟨fun k ↦ ⟪b (i.succAbove k), x⟫_ℝ, ?_⟩
    change (∑ k : Fin r, ⟪b (i.succAbove k), x⟫_ℝ • b (i.succAbove k)) = x
    have hs := Fin.sum_univ_succAbove (fun k ↦ ⟪b k, x⟫_ℝ • b k) i
    rw [hz, zero_smul, zero_add] at hs
    exact hs.symm.trans (b.sum_repr' x)

local instance originalAllFacesColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {r : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin (r + 1) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching (r + 1) α β kin g)
  (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
  (x : Fin (r + 1) → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene (r + 1))))

/-- Literal original-scene normal readouts on all centered physical faces of side length R. -/
def LegalWeightedStationaryPoissonMatching.sceneAllFacesReadout
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1))
    (j : Fin (r + 1) × Fin 2) (y : Fin r → ℝ) : ℝ :=
  Q.sceneScalarFaceReadout (orderedOrthonormalFaceMap b j.1)
    (fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)) (x j.1) R y s

/-- The deterministic all-face bound applied to the actual family of original face readouts. -/
def LegalWeightedStationaryPoissonMatching.sceneAllFacesTraceDualBound
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1)) : ℝ :=
  originalRawUnitCubeBoundaryTraceDualBound (Q.sceneAllFacesReadout b x R s)

/-- The actual common all-face bound is pointwise nonnegative. -/
theorem LegalWeightedStationaryPoissonMatching.sceneAllFacesTraceDualBound_nonneg
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1)) :
    0 ≤ Q.sceneAllFacesTraceDualBound b x R s :=
  originalRawUnitCubeBoundaryTraceDualBound_nonneg _

private theorem sceneAllFacesTraceDualBound_eq_sum (R : ℝ) :
    Q.sceneAllFacesTraceDualBound b x R = fun s ↦
      (Fintype.card (Fin (r + 1) × Fin 2) : ℝ) * ∑ j : Fin (r + 1) × Fin 2,
        Q.sceneCubeTraceDualBound (orderedOrthonormalFaceMap b j.1)
          (fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)) (x j.1) R s := rfl

/-- The bound built from the literal original scene is measurable. -/
theorem LegalWeightedStationaryPoissonMatching.measurable_sceneAllFacesTraceDualBound
    (R : ℝ) : Measurable (Q.sceneAllFacesTraceDualBound b x R) := by
  rw [sceneAllFacesTraceDualBound_eq_sum]
  exact (Finset.measurable_sum Finset.univ (fun j _ ↦
    Q.measurable_sceneCubeTraceDualBound (orderedOrthonormalFaceMap b j.1)
      (fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)) (x j.1) R)).const_mul _

/-- Actual stationarity gives an integrable bound without a boundary-rate premise. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sceneAllFacesTraceDualBound
    (R : ℝ) : Integrable (Q.sceneAllFacesTraceDualBound b x R) (Q.law : Measure _) := by
  rw [sceneAllFacesTraceDualBound_eq_sum]
  exact (integrable_finsetSum Finset.univ (fun j _ ↦
    Q.integrable_sceneCubeTraceDualBound (orderedOrthonormalFaceMap b j.1)
      (fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)) (x j.1) R)).const_mul _

/-- On one full-measure set, the same actual quantity controls every C1 zero-mean raw test. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_smooth_all_faces_pairing_sq_le_sceneAllFacesTraceDualBound
    (R : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ (φ : (Fin (r + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ →
      (∫ z in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1), φ z) = 0 →
      (originalRawUnitCubeBoundaryPairing (Q.sceneAllFacesReadout b x R s) φ)^2 ≤
        Q.sceneAllFacesTraceDualBound b x R s * originalRawUnitCubeGradientEnergy φ := by
  have hfaces : ∀ j : Fin (r + 1) × Fin 2,
      ∀ᵐ s ∂(Q.law : Measure _), MemLp (Q.sceneAllFacesReadout b x R s j) 2
        (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))) := by
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
      (A := Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1)) isCompact_Icc.measure_lt_top.ne).swap
    filter_upwards [hp.prod_right_ae] with s hs
    exact (memLp_two_iff_integrable_sq
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hs
  filter_upwards [ae_all_iff.mpr hfaces] with s hs
  intro φ hφ hmean
  exact smooth_rawUnitCube_all_faces_pairing_sq_le hs hφ hmean

/-- The chosen normal projection condition produces a vanishing expected all-face bound. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_integral_sceneAllFacesTraceDualBound_zero
    (hproj : ∀ i : Fin (r + 1),
      (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection (x i) = 0) :
    Tendsto (fun R : ℝ ↦ ∫ s, Q.sceneAllFacesTraceDualBound b x R s ∂(Q.law : Measure _))
      atTop (𝓝 0) := by
  have hlim : ∀ j : Fin (r + 1) × Fin 2,
      Tendsto (fun R : ℝ ↦ ∫ s, Q.sceneCubeTraceDualBound (orderedOrthonormalFaceMap b j.1)
        (fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)) (x j.1) R s ∂(Q.law : Measure _))
        atTop (𝓝 0) := by
    intro j
    apply Q.tendsto_integral_sceneCubeTraceDualBound_zero
    simpa only [range_orderedOrthonormalFaceMap] using hproj j.1
  have hsum := (tendsto_finsetSum Finset.univ (fun j _ ↦ hlim j)).const_mul
    (Fintype.card (Fin (r + 1) × Fin 2) : ℝ)
  simp only [Finset.sum_const_zero, mul_zero] at hsum
  convert hsum using 1
  funext R
  rw [sceneAllFacesTraceDualBound_eq_sum, integral_const_mul]
  congr 1
  exact integral_finsetSum Finset.univ (fun j _ ↦
    Q.integrable_sceneCubeTraceDualBound (orderedOrthonormalFaceMap b j.1)
      (fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)) (x j.1) R)

end OTSelector.Reconstruction
