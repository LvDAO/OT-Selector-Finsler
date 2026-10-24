import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetPhysicalFaces
import Mathlib.MeasureTheory.Constructions.Pi

/-! The two genuine face-coordinate conventions give exactly the same physical cube flux. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Inserting a normal coordinate gives its actual selected-frame normal plus tangent vector. -/
theorem originalScreeningPhysicalCubeMap_insertNth {r : ℕ}
    (b : OrthonormalBasis (Fin (r+1)) ℝ (EuclideanSpace ℝ (Fin (r+1))))
    (i : Fin (r+1)) (c : ℝ) (y : Fin r → ℝ) :
    orthonormalPhysicalCubeMap b (i.insertNth c y) =
      EuclideanSpace.equiv (Fin (r+1)) ℝ (c • b i + orderedOrthonormalFaceMap b i y) := by
  apply congrArg (EuclideanSpace.equiv (Fin (r+1)) ℝ)
  change (orthonormalCubeCoordinates b).symm (i.insertNth c y) = _
  rw [orthonormalCubeCoordinates_symm_eq_sum, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

/-- Haar coordinate reindexing from ordered tangent coordinates to the actual omitted-index
face coordinates preserves every literal centered face integral, including its true area. -/
theorem originalScreening_integral_omittedFaceCoordinates_eq_ordered {r : ℕ}
    (i : Fin (r+1)) (R : ℝ) (f : ({k : Fin (r+1) // k ≠ i} → ℝ) → ℝ) :
    (∫ z in Icc (fun _ : {k : Fin (r+1) // k ≠ i} ↦ -R) (fun _ ↦ R), f z) =
      ∫ y in Icc (fun _ : Fin r ↦ -R) (fun _ ↦ R),
        f (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin (r+1) // k ≠ i} ↦ ℝ)
          (finSuccAboveEquiv i) y) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : {k : Fin (r+1) // k ≠ i} ↦ ℝ) (finSuccAboveEquiv i)
  have he (y : Fin r → ℝ) (k : Fin r) : e y ((finSuccAboveEquiv i) k) = y k :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) (finSuccAboveEquiv i) y k
  have himage : e '' Icc (fun _ : Fin r ↦ -R) (fun _ ↦ R) =
      Icc (fun _ : {k : Fin (r+1) // k ≠ i} ↦ -R) (fun _ ↦ R) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      constructor <;> intro k <;> obtain ⟨j, rfl⟩ := (finSuccAboveEquiv i).surjective k
      · simpa only [he] using hy.1 j
      · simpa only [he] using hy.2 j
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      constructor <;> intro k
      · have h := he (e.symm z) k
        rw [e.apply_symm_apply] at h
        rw [← h]
        exact hz.1 _
      · have h := he (e.symm z) k
        rw [e.apply_symm_apply] at h
        rw [← h]
        exact hz.2 _
  rw [← himage]
  exact (volume_measurePreserving_piCongrLeft (fun _ : {k : Fin (r+1) // k ≠ i} ↦ ℝ)
    (finSuccAboveEquiv i)).setIntegral_image_emb e.measurableEmbedding f _

/-- The coordinate permutation preserves the actual selected-frame tangent vector. -/
theorem originalScreening_orthonormalFaceMap_reindex {r : ℕ}
    (b : OrthonormalBasis (Fin (r+1)) ℝ (EuclideanSpace ℝ (Fin (r+1))))
    (i : Fin (r+1)) (y : Fin r → ℝ) :
    orthonormalFaceMap b i
      (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin (r+1) // k ≠ i} ↦ ℝ)
        (finSuccAboveEquiv i) y) = orderedOrthonormalFaceMap b i y := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : {k : Fin (r+1) // k ≠ i} ↦ ℝ) (finSuccAboveEquiv i)
  have hs := (finSuccAboveEquiv i).sum_comp (fun k ↦ e y k • b k.1)
  change (∑ k, e y k • b k.1) = ∑ k, y k • b (i.succAbove k)
  rw [← hs]
  apply Finset.sum_congr rfl
  intro k _
  change e y ((finSuccAboveEquiv i) k) • b (i.succAbove k) = _
  rw [show e y ((finSuccAboveEquiv i) k) = y k from
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) (finSuccAboveEquiv i) y k]

/-- The original raw radius-R full flux is exactly the signed coordinate-area pairing on
the very same physical side-2R cube, tested against the literal constant one. -/
theorem LegalWeightedStationaryPoissonMatching.sceneRawCenteredCubeFlux_eq_physicalConstantPairing
    {r : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (r+1) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (r+1) μ ν kin g)
    (b : OrthonormalBasis (Fin (r+1)) ℝ (EuclideanSpace ℝ (Fin (r+1))))
    (x : Fin (r+1) → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene (r+1))))
    (R : ℝ) (scene : LegalMarkedOptimalInputScene (r+1)) :
    Q.sceneRawCenteredCubeFlux b x R scene =
      Q.scenePhysicalCubeBoundaryPairing b x (2*R) scene (fun _ ↦ 1) := by
  unfold LegalWeightedStationaryPoissonMatching.sceneRawCenteredCubeFlux
    LegalWeightedStationaryPoissonMatching.scenePhysicalCubeBoundaryPairing
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold LegalWeightedStationaryPoissonMatching.sceneRawCenteredFaceIntegral
  rw [originalScreening_integral_omittedFaceCoordinates_eq_ordered]
  have hhalf : (2*R)/2 = R := by ring
  have hneg : -(2*R)/2 = -R := by ring
  simp only [hhalf, hneg, mul_one]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _
  dsimp only
  rw [Q.sceneScalarFaceReadout_apply]
  simp only [one_smul, originalScreening_orthonormalFaceMap_reindex,
    LegalWeightedStationaryPoissonMatching.scenePhysicalCubeFaceReadout, hhalf, hneg]
  rw [originalScreeningPhysicalCubeMap_insertNth]

end OTSelector.Reconstruction
