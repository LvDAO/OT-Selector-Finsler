import OTSelector.Reconstruction.OriginalOrientedCubeReflectedKernel

/-! Same-input-measure physical oriented reflected fields and genuine local-window Fubini. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ}

private def orientedReflectedMarkedCoordinates
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    ((Fin q → ℝ) × ℝ) ≃ᵐ ((Fin q → ℝ) × ℝ) :=
  (orthonormalPhysicalCubeMap b).toHomeomorph.toMeasurableEquiv.symm.prodCongr (MeasurableEquiv.refl ℝ)

/-- The literal oriented class discrepancy integrates the original physical reflected
response against the unchanged full original physical input measure and clock marks. -/
def originalOrientedClassReflectedInputScalarField
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (η : (Fin q → ℝ) → ℝ) (L : ℝ) (C : Set ℝ)
    (σ : Measure ((Fin q → ℝ) × ℝ)) (z : Fin q → ℝ) : ℝ :=
  ∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
    originalOrientedCubeReflectedInputResponse b η L z p.1 ∂σ

/-- Actual measurable-equivalence integration identifies the literal physical field with
the raw pulled-kernel field; neither a new scene nor a rotated matching law is introduced. -/
theorem originalOrientedClassReflectedInputScalarField_eq_raw_map
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (η : (Fin q → ℝ) → ℝ) (L : ℝ) (C : Set ℝ)
    (σ : Measure ((Fin q → ℝ) × ℝ)) (z : Fin q → ℝ) :
    originalOrientedClassReflectedInputScalarField b η L C σ z =
      originalClassReflectedInputScalarField (η ∘ orthonormalPhysicalCubeMap b) (L / 2) C
        (σ.map (fun p ↦ ((orthonormalPhysicalCubeMap b).symm p.1, p.2)))
        ((orthonormalPhysicalCubeMap b).symm z) := by
  exact (integral_map_equiv (orientedReflectedMarkedCoordinates b)
    (fun p ↦ C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
      originalCubeReflectedInputResponse (η ∘ orthonormalPhysicalCubeMap b) (L / 2)
        ((orthonormalPhysicalCubeMap b).symm z) p.1)).symm

/-- For an actual Euclidean radial kernel the raw mapped field retains the same eta. -/
theorem originalOrientedClassReflectedInputScalarField_eq_raw_map_of_radial
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} (hηradial : IsOriginalEuclideanRadial η)
    (L : ℝ) (C : Set ℝ) (σ : Measure ((Fin q → ℝ) × ℝ)) (z : Fin q → ℝ) :
    originalOrientedClassReflectedInputScalarField b η L C σ z =
      originalClassReflectedInputScalarField η (L / 2) C
        (σ.map (fun p ↦ ((orthonormalPhysicalCubeMap b).symm p.1, p.2)))
        ((orthonormalPhysicalCubeMap b).symm z) := by
  rw [originalOrientedClassReflectedInputScalarField_eq_raw_map,
    euclideanRadial_comp_orthonormalPhysicalCubeMap b hηradial]

/-- The raw expanded input window is exactly the original physical expanded side-L+2
cube, retaining all original marks and allowing an infinite full input measure. -/
theorem map_oriented_input_outerWindow
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (L : ℝ) (σ : Measure ((Fin q → ℝ) × ℝ)) :
    (σ.map (fun p ↦ ((orthonormalPhysicalCubeMap b).symm p.1, p.2)))
        (haarRootCube (Fin q) (L / 2 + 1) ×ˢ (Set.univ : Set ℝ)) =
      σ (originalCenteredPhysicalCubeRegion b (L + 2) ×ˢ (Set.univ : Set ℝ)) := by
  change (σ.map (orientedReflectedMarkedCoordinates b)) _ = _
  have hA : MeasurableSet (haarRootCube (Fin q) (L / 2 + 1) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  rw [Measure.map_apply (orientedReflectedMarkedCoordinates b).measurable hA]
  congr 1
  ext p
  simp only [mem_preimage, mem_prod, mem_univ, and_true]
  change (orthonormalPhysicalCubeMap b).symm p.1 ∈ haarRootCube (Fin q) (L / 2 + 1) ↔
    p.1 ∈ originalCenteredPhysicalCubeRegion b (L + 2)
  rw [mem_originalCenteredPhysicalCubeRegion_iff]
  have he : (L + 2) / 2 = L / 2 + 1 := by ring
  rw [he]

/-- Observation-volume transport gives the exact same-input physical-field test pairing
as the original raw-frame field pairing, with literal Haar change of variables. -/
theorem integral_orientedClassReflectedInputScalarField_mul_eq_raw
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} (hηradial : IsOriginalEuclideanRadial η)
    (L : ℝ) (C : Set ℝ) (σ : Measure ((Fin q → ℝ) × ℝ)) (u : (Fin q → ℝ) → ℝ) :
    (∫ z in originalCenteredPhysicalCubeRegion b L,
      originalOrientedClassReflectedInputScalarField b η L C σ z * u z) =
      ∫ y in haarRootCube (Fin q) (L / 2),
        originalClassReflectedInputScalarField η (L / 2) C
          (σ.map (fun p ↦ ((orthonormalPhysicalCubeMap b).symm p.1, p.2))) y *
            u (orthonormalPhysicalCubeMap b y) := by
  rw [originalCenteredPhysicalCubeRegion,
    integral_orthonormalPhysicalCubeRegion b (fun _ ↦ -L / 2) (fun _ ↦ L / 2)]
  simp only [originalOrientedClassReflectedInputScalarField_eq_raw_map_of_radial b hηradial,
    ContinuousLinearEquiv.symm_apply_apply, haarRootCube, neg_div]

/-- Actual finite mass in the original physical expanded cube suffices for literal
oriented-field test integrability, without globally finite original input mass. -/
theorem integrable_originalOrientedClassReflectedInputScalarField_mul
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    (hηradial : IsOriginalEuclideanRadial η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0)
    {L : ℝ} (hL : 2 ≤ L) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ))
    (hσ : σ (originalCenteredPhysicalCubeRegion b (L + 2) ×ˢ (Set.univ : Set ℝ)) < ∞)
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    Integrable (fun z ↦ originalOrientedClassReflectedInputScalarField b η L C σ z * u z)
      (volume.restrict (originalCenteredPhysicalCubeRegion b L)) := by
  let σraw := σ.map (fun p ↦ ((orthonormalPhysicalCubeMap b).symm p.1, p.2))
  have hraw : σraw (haarRootCube (Fin q) (L / 2 + 1) ×ˢ (Set.univ : Set ℝ)) < ∞ := by
    rw [map_oriented_input_outerWindow]
    exact hσ
  have hi := integrable_originalClassReflectedInputScalarField_mul_of_finite_outer hη hM hηM
    (raw_unit_range_of_euclidean_unit_range hηsupport) (by linarith : 1 ≤ L / 2) hC σraw hraw
    (hu.comp (orthonormalPhysicalCubeMap b).continuous)
  have hcomp : IntegrableOn
      ((fun z ↦ originalOrientedClassReflectedInputScalarField b η L C σ z * u z) ∘ orthonormalPhysicalCubeMap b)
      (haarRootCube (Fin q) (L / 2)) := by
    apply hi.congr
    exact ae_of_all _ (fun y ↦ by
      change originalClassReflectedInputScalarField η (L / 2) C σraw y * u (orthonormalPhysicalCubeMap b y) =
        originalOrientedClassReflectedInputScalarField b η L C σ (orthonormalPhysicalCubeMap b y) * u (orthonormalPhysicalCubeMap b y)
      rw [originalOrientedClassReflectedInputScalarField_eq_raw_map_of_radial b hηradial,
        ContinuousLinearEquiv.symm_apply_apply])
  have h := ((measurePreserving_orthonormalPhysicalCubeMap b).integrableOn_image
    (orthonormalPhysicalCubeMap b).toHomeomorph.measurableEmbedding).mpr hcomp
  simpa only [IntegrableOn, originalCenteredPhysicalCubeRegion, orthonormalPhysicalCubeRegion, haarRootCube, neg_div] using h

/-- Genuine same-input physical Fubini is transported from the proved raw local-window
theorem, keeping the original physical eta and full physical input measure on both sides. -/
theorem integral_originalOrientedClassReflectedInputScalarField_mul_eq
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    (hηradial : IsOriginalEuclideanRadial η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0)
    {L : ℝ} (hL : 2 ≤ L) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ))
    (hσ : σ (originalCenteredPhysicalCubeRegion b (L + 2) ×ˢ (Set.univ : Set ℝ)) < ∞)
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    (∫ z in originalCenteredPhysicalCubeRegion b L,
      originalOrientedClassReflectedInputScalarField b η L C σ z * u z) =
      ∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
        (∫ z in originalCenteredPhysicalCubeRegion b L,
          originalOrientedCubeReflectedInputResponse b η L z p.1 * u z) ∂σ := by
  let σraw := σ.map (fun p ↦ ((orthonormalPhysicalCubeMap b).symm p.1, p.2))
  have hraw : σraw (haarRootCube (Fin q) (L / 2 + 1) ×ˢ (Set.univ : Set ℝ)) < ∞ := by
    rw [map_oriented_input_outerWindow]
    exact hσ
  calc
    _ = ∫ y in haarRootCube (Fin q) (L / 2),
        originalClassReflectedInputScalarField η (L / 2) C σraw y * u (orthonormalPhysicalCubeMap b y) :=
      integral_orientedClassReflectedInputScalarField_mul_eq_raw b hηradial L C σ u
    _ = ∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
        (∫ y in haarRootCube (Fin q) (L / 2), originalCubeReflectedInputResponse η (L / 2) y p.1 * u (orthonormalPhysicalCubeMap b y)) ∂σraw :=
      integral_originalClassReflectedInputScalarField_mul_eq_of_finite_outer hη hM hηM
        (raw_unit_range_of_euclidean_unit_range hηsupport) (by linarith : 1 ≤ L / 2) hC σraw hraw
        (hu.comp (orthonormalPhysicalCubeMap b).continuous)
    _ = _ := by
      change (∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
        (∫ y in haarRootCube (Fin q) (L / 2), originalCubeReflectedInputResponse η (L / 2) y p.1 *
          u (orthonormalPhysicalCubeMap b y)) ∂σ.map (orientedReflectedMarkedCoordinates b)) = _
      rw [integral_map_equiv (orientedReflectedMarkedCoordinates b)]
      apply integral_congr_ae
      apply ae_of_all
      intro p
      change C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
        (∫ y in haarRootCube (Fin q) (L / 2), originalCubeReflectedInputResponse η (L / 2) y
          ((orthonormalPhysicalCubeMap b).symm p.1) * u (orthonormalPhysicalCubeMap b y)) = _
      rw [← integral_orientedCube_reflected_response_mul b hηradial L p.1 u]

end OTSelector.Reconstruction
