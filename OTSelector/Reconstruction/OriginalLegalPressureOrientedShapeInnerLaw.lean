import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeNearCubeGeometry
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolume
import OTSelector.Probability.PoissonRestriction

/-! Exact original conditional sampling law for the actual inner orthogonal cube. -/
open Set Function MeasureTheory Filter
open OTSelector.Probability
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q : ℕ}

/-- The actual inner cube expressed in the original unit sampler coordinates. -/
def originalOrientedShapeUnitInner
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (s : ℝ) : Set (Fin q → ℝ) :=
  (fun v : Fin q → ℝ ↦ fun i ↦ v i-(1/2:ℝ)) ⁻¹' originalCenteredPhysicalCubeRegion b s

/-- The original unit-word map into the same inner cube, with the unit center restored. -/
def originalOrientedShapeUnitInnerMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (s : ℝ)
    (v : Fin q → ℝ) : Fin q → ℝ :=
  fun i ↦ originalOrientedRawCubePhysicalMap b (s/2) v i+(1/2:ℝ)

/-- Centering the genuine original unit sampler gives literal unit-volume Haar law. -/
theorem map_originalOrientedShape_centered_unit (q : ℕ) :
    (cubeMeasure (Fin q) 1).map (fun v i ↦ v i-(1/2:ℝ)) =
      volume.restrict (haarRootCube (Fin q) (1/2)) := by
  have h := map_originalUnitCube_centered_eq_normalized_volume q (R := (1/2:ℝ)) (by norm_num)
  have hA : (fun v : Fin q → ℝ ↦ fun i ↦ 2*(1/2:ℝ)*v i-(1/2:ℝ)) =
      (fun v : Fin q → ℝ ↦ fun i ↦ v i-(1/2:ℝ)) := by funext v i; ring
  have hV : volume (haarRootCube (Fin q) (1/2)) = 1 := by
    rw [volume_haarRootCube (Fin q) (by norm_num)]
    norm_num
  simpa only [hA,hV,inv_one,one_smul] using h

theorem measurableSet_originalOrientedShapeUnitInner
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (s : ℝ) :
    MeasurableSet (originalOrientedShapeUnitInner b s) := by
  have hside : 2*(s/2)=s := by ring
  have hK : MeasurableSet (originalCenteredPhysicalCubeRegion b s) := by
    simpa only [hside] using measurableSet_originalOrientedTraffic_cube b (s/2)
  exact hK.preimage (by fun_prop)

/-- The actual inner event has exactly its physical volume under the original sampler. -/
theorem originalOrientedShapeUnitInner_mass
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {s : ℝ} (hs : 0 ≤ s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1/2)) :
    (cubeMeasure (Fin q) 1) (originalOrientedShapeUnitInner b s) = ENNReal.ofReal (s^q) := by
  have hside : 2*(s/2)=s := by ring
  have hK : MeasurableSet (originalCenteredPhysicalCubeRegion b s) := by
    simpa only [hside] using measurableSet_originalOrientedTraffic_cube b (s/2)
  have hA : Measurable (fun v : Fin q → ℝ ↦ fun i ↦ v i-(1/2:ℝ)) := by fun_prop
  unfold originalOrientedShapeUnitInner
  rw [← Measure.map_apply hA hK,map_originalOrientedShape_centered_unit,
    Measure.restrict_apply hK,inter_eq_left.mpr hsub]
  exact originalOrientedShape_cube_volume b hs

/-- The original unit word maps exactly to the original conditional inner law.
The boundary null-set argument is inherited from the true affine Haar map. -/
theorem map_originalOrientedShapeUnitInnerMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {s : ℝ} (hs : 0 < s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1/2)) :
    (cubeMeasure (Fin q) 1).map (originalOrientedShapeUnitInnerMap b s) =
      restrictedPointLaw (cubeMeasure (Fin q) 1) (originalOrientedShapeUnitInner b s) := by
  let μ := cubeMeasure (Fin q) 1
  let : IsProbabilityMeasure μ := isProbabilityMeasure_cubeMeasure (by norm_num)
  let e : (Fin q → ℝ) ≃ᵐ (Fin q → ℝ) :=
    MeasurableEquiv.addRight (fun _ ↦ -(1/2:ℝ))
  let K := originalCenteredPhysicalCubeRegion b s
  let Q0 := haarRootCube (Fin q) (1/2)
  let F := originalOrientedRawCubePhysicalMap b (s/2)
  have hside : 2*(s/2)=s := by ring
  have hK : MeasurableSet K := by
    simpa only [K,hside] using measurableSet_originalOrientedTraffic_cube b (s/2)
  have he : (e : (Fin q → ℝ) → Fin q → ℝ) =
      (fun v i ↦ v i-(1/2:ℝ)) := by funext v i; simp [e,sub_eq_add_neg]
  have hcenter : μ.map e = volume.restrict Q0 := by
    simpa only [μ,Q0,he] using map_originalOrientedShape_centered_unit q
  have hmass : (volume.restrict Q0) K = volume K := by
    rw [Measure.restrict_apply hK,inter_eq_left.mpr hsub]
  have hpositive : (volume.restrict Q0) K ≠ 0 := by
    rw [hmass,originalOrientedShape_cube_volume b hs.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hs q))
  have hcond : restrictedPointLaw (volume.restrict Q0) K =
      (volume K)⁻¹ • volume.restrict K := by
    rw [restrictedPointLaw,ite_eq_right hpositive,ProbabilityTheory.cond,hmass,
      Measure.restrict_restrict hK,inter_eq_left.mpr hsub]
  have hphysical : μ.map F = restrictedPointLaw (μ.map e) K := by
    rw [hcenter,hcond]
    simpa only [μ,F,K,hside] using
      map_originalUnitCube_oriented_eq_normalized_volume b (R := s/2) (by positivity)
  have hresult : μ.map ((e.symm : (Fin q → ℝ) → Fin q → ℝ) ∘ F) =
      restrictedPointLaw μ (e ⁻¹' K) := by
    rw [← Measure.map_map e.symm.measurable
      (measurable_originalOrientedRawCubePhysicalMap b (s/2)),hphysical,
      restrictedPointLaw_map μ e.measurable hK]
    exact e.map_symm_map
  convert hresult using 1
  · congr 1
    funext v i
    simp [originalOrientedShapeUnitInnerMap,e,F]
  · rw [he]
    rfl

end OTSelector.Reconstruction
