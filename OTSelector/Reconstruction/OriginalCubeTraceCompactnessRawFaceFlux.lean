import OTSelector.Analysis.Sobolev.CubeTraceFaceGeometry
import OTSelector.Reconstruction.OriginalCurrentNormalizedFaceFluxVariance
import OTSelector.MeasureTheory.Integral.AffineCube

/-! Literal centered physical face fluxes and their true surface-order normalization. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q α β kin g)

/-- The literal scalar field is evaluated at precisely the specified original
physical translation under the same original law. -/
theorem LegalWeightedStationaryPoissonMatching.sceneScalarFaceReadout_apply
    {ι : Type*} [Fintype ι] (L : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (R : ℝ) (y : ι → ℝ) (s : LegalMarkedOptimalInputScene q) :
    Q.sceneScalarFaceReadout L offset x R y s =
      x (legalMarkedInputSceneReroot q
        (EuclideanSpace.equiv (Fin q) ℝ (offset R + L (R • y))) s) := by
  change x (legalMarkedInputSceneReroot q
    (EuclideanSpace.equiv (Fin q) ℝ (offset R) +
      EuclideanSpace.equiv (Fin q) ℝ (L (R • y))) s) = _
  rw [map_add]

/-- The normalized face convention is the exact lower corner of the
physical centered cube when its scale is the physical side length. -/
def originalCenteredCubeFluxOffsets {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : Fin q × Fin 2) (t : ℝ) : EuclideanSpace ℝ (Fin q) :=
  originalCenteredCubeFaceOffset b j (t/2)

/-- A raw physical face integral uses the actual tangent coordinates in
[-R,R] and the actual normal coordinate ±R, under the unchanged scene law. -/
def LegalWeightedStationaryPoissonMatching.sceneRawCenteredFaceIntegral
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (R : ℝ) (j : Fin q × Fin 2) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∫ z in Icc (fun _ : {k : Fin q // k ≠ j.1} ↦ -R) (fun _ ↦ R),
    Q.sceneScalarFaceReadout (orthonormalFaceMap b j.1)
      (fun _ ↦ (if j.2 = 0 then -R else R) • b j.1) (x j.1) 1 z s

/-- The raw full physical flux is the actual signed sum of all 2q raw faces. -/
def LegalWeightedStationaryPoissonMatching.sceneRawCenteredCubeFlux
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (R : ℝ) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∑ j : Fin q × Fin 2, (if j.2 = 0 then (-1 : ℝ) else 1) *
    Q.sceneRawCenteredFaceIntegral b x R j s

/-- Actual affine face change of variables produces the genuine area
factor (2R)^(q-1) and the exact same original normalized face integral. -/
theorem LegalWeightedStationaryPoissonMatching.sceneRawCenteredFaceIntegral_eq
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    {R : ℝ} (hR : 0 < R) (j : Fin q × Fin 2) (s : LegalMarkedOptimalInputScene q) :
    Q.sceneRawCenteredFaceIntegral b x R j s =
      (2*R)^(q-1) * Q.sceneOrientedFaceIntegral b (originalCenteredCubeFluxOffsets b) x (2*R) j s := by
  have ha := integral_centered_cube_eq_two_mul_radius_pow_smul
    (fun z : {k : Fin q // k ≠ j.1} → ℝ ↦ Q.sceneScalarFaceReadout (orthonormalFaceMap b j.1)
      (fun _ ↦ (if j.2 = 0 then -R else R) • b j.1) (x j.1) 1 z s) hR
  simp only [smul_eq_mul, card_originalCubeFaceCoordinates] at ha
  unfold LegalWeightedStationaryPoissonMatching.sceneRawCenteredFaceIntegral
  rw [ha]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _
  dsimp only
  rw [Q.sceneScalarFaceReadout_apply, Q.sceneScalarFaceReadout_apply]
  simp only [one_smul, originalCenteredCubeFluxOffsets]
  have he : (2*R : ℝ)/2 = R := by ring
  rw [he]
  have hp := originalCenteredCubeFacePoint_eq_normal_add_centered_tangent b j R y
  change (originalCenteredCubeFaceOffset b j R + orthonormalFaceMap b j.1 ((2*R) • y)) = _ at hp
  rw [← hp]

/-- The actual full raw physical flux carries the same genuine face area
factor; there is no extra spatial normalization hidden in a definition. -/
theorem LegalWeightedStationaryPoissonMatching.sceneRawCenteredCubeFlux_eq
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    {R : ℝ} (hR : 0 < R) (s : LegalMarkedOptimalInputScene q) :
    Q.sceneRawCenteredCubeFlux b x R s =
      (2*R)^(q-1) * Q.sceneNormalizedFaceFlux b (originalCenteredCubeFluxOffsets b) x (2*R) s := by
  unfold LegalWeightedStationaryPoissonMatching.sceneRawCenteredCubeFlux
    LegalWeightedStationaryPoissonMatching.sceneNormalizedFaceFlux
  simp_rw [Q.sceneRawCenteredFaceIntegral_eq b x hR]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Surface-order normalization by R^(q-1) leaves only its genuine fixed
factor 2^(q-1) and the actual normalized full face flux at side scale 2R. -/
theorem LegalWeightedStationaryPoissonMatching.inv_radius_pow_mul_sceneRawCenteredCubeFlux
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    {R : ℝ} (hR : 0 < R) (s : LegalMarkedOptimalInputScene q) :
    (R^(q-1))⁻¹ * Q.sceneRawCenteredCubeFlux b x R s =
      (2 : ℝ)^(q-1) * Q.sceneNormalizedFaceFlux b (originalCenteredCubeFluxOffsets b) x (2*R) s := by
  rw [Q.sceneRawCenteredCubeFlux_eq b x hR, mul_pow]
  field_simp [pow_ne_zero _ hR.ne']

/-- Every positive-radius raw centered-cube flux is measurable under
its unchanged original scene law. -/
theorem LegalWeightedStationaryPoissonMatching.measurable_sceneRawCenteredCubeFlux
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    {R : ℝ} (hR : 0 < R) : Measurable (Q.sceneRawCenteredCubeFlux b x R) := by
  have he : Q.sceneRawCenteredCubeFlux b x R = fun s ↦ (2*R)^(q-1) *
      Q.sceneNormalizedFaceFlux b (originalCenteredCubeFluxOffsets b) x (2*R) s := by
    funext s
    exact Q.sceneRawCenteredCubeFlux_eq b x hR s
  rw [he]
  exact (Q.measurable_sceneNormalizedFaceFlux b (originalCenteredCubeFluxOffsets b) x (2*R)).const_mul _

/-- Actual raw physical flux has a finite original second moment at each
positive radius, with the genuine face-area scaling. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sq_sceneRawCenteredCubeFlux
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    {R : ℝ} (hR : 0 < R) :
    Integrable (fun s ↦ (Q.sceneRawCenteredCubeFlux b x R s)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  simp_rw [Q.sceneRawCenteredCubeFlux_eq b x hR, mul_pow]
  exact (Q.integrable_sq_sceneNormalizedFaceFlux b (originalCenteredCubeFluxOffsets b) x (2*R)).const_mul _

/-- The genuine raw physical full-flux second moment is little-o of
R^(2(q-1)), from the actual same-frame normal invariant projections.
The area change of variables and side-scale change R to 2R are proved. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_integral_sq_normalized_sceneRawCenteredCubeFlux_zero
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (hx : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection (x i) = 0) :
    Tendsto (fun R : ℝ ↦ ∫ s, ((R^(q-1))⁻¹ * Q.sceneRawCenteredCubeFlux b x R s)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) atTop (𝓝 0) := by
  have hl := Q.tendsto_integral_sq_sceneNormalizedFaceFlux_zero b
    (originalCenteredCubeFluxOffsets b) x hx
  have hscale : Tendsto (fun R : ℝ ↦ 2*R) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have hlim := (hl.comp hscale).const_mul (((2 : ℝ)^(q-1))^2)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp_rw [Q.inv_radius_pow_mul_sceneRawCenteredCubeFlux b x hR, mul_pow]
  exact (integral_const_mul _ _).symm

end OTSelector.Reconstruction
