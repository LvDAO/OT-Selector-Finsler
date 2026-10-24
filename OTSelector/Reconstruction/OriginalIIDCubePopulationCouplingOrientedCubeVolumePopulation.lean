import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolume
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingRawCube

/-! Same-frame raw original-atom population plans with exactly preserved Euclidean energy. -/

open Set Function MeasureTheory
open OTSelector.Probability
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q n : ℕ}

/-- Read the standard Euclidean optimizer coordinates in the actual physical frame. -/
def originalOrientedCubeEuclideanReadout
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    EuclideanSpace ℝ (Fin q) ≃L[ℝ] (Fin q → ℝ) :=
  b.repr.symm.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin q) ℝ)

/-- The raw coordinate norm need not be Euclidean; the true physical Euclidean
distance of the rotated readouts is exactly the original optimizer distance. -/
theorem originalOrientedCubeEuclideanReadout_norm_sub
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (u v : EuclideanSpace ℝ (Fin q)) :
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (originalOrientedCubeEuclideanReadout b u) -
      (EuclideanSpace.equiv (Fin q) ℝ).symm (originalOrientedCubeEuclideanReadout b v)‖ = ‖u-v‖ := by
  change ‖b.repr.symm u - b.repr.symm v‖ = ‖u-v‖
  rw [← map_sub, b.repr.symm.norm_map]

private theorem oriented_readout_rawPoint
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (v : Fin q → ℝ) :
    originalOrientedCubeEuclideanReadout b (originalRawCubePhysicalMap
      ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) v) =
        originalOrientedRawCubePhysicalMap b R v := by
  have haxis : originalRawCubePhysicalMap
      ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) v =
      (EuclideanSpace.equiv (Fin q) ℝ).symm (fun i ↦ 2*R*v i-R) := by
    ext i
    change -R + (2*R)*v i = 2*R*v i-R
    ring
  rw [haxis]
  rfl

/-- The actual axis plan is mapped once into the same raw physical cube frame. -/
def originalOrientedRawCubePopulationCoupling
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (x : Fin n → (Fin q → ℝ)) : Measure ((Fin q → ℝ) × (Fin q → ℝ)) :=
  (originalRawCubePopulationCoupling ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) x).map
    (Prod.map (originalOrientedCubeEuclideanReadout b) (originalOrientedCubeEuclideanReadout b))

theorem measurable_originalOrientedRawCubePopulationCoupling
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    Measurable (originalOrientedRawCubePopulationCoupling (n := n) b R) :=
  (Measure.measurable_map _ ((originalOrientedCubeEuclideanReadout b).continuous.measurable.prodMap
    (originalOrientedCubeEuclideanReadout b).continuous.measurable)).comp
      (originalRawCubePopulationCoupling_spec (n := n) _ (2*R)).1

/-- The same original raw observations and the literal same-frame normalized
cube population are the two exact marginals, including repeated and absent atoms. -/
theorem originalOrientedRawCubePopulationCoupling_spec
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R)
    (x : Fin n → (Fin q → ℝ)) (hx : ∀ i, x i ∈ unitCube q) :
    let Γ := originalOrientedRawCubePopulationCoupling b R x
    IsFiniteMeasure Γ ∧
      Γ.map Prod.fst = ∑ i, Measure.dirac (originalOrientedRawCubePhysicalMap b R (x i)) ∧
      Γ.map Prod.snd = (n : ℝ≥0∞) •
        normalizedFiniteLaw (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) := by
  let F := originalOrientedCubeEuclideanReadout b
  let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
  have hF := F.continuous.measurable
  have hbase := (originalRawCubePopulationCoupling_spec z (2*R)).2 x hx
  have : IsFiniteMeasure (originalRawCubePopulationCoupling z (2*R) x) := hbase.1
  have hA : Measurable (originalRawCubePhysicalMap z (2*R)) :=
    measurable_const.add ((EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.const_smul (2*R))
  have hread : F ∘ originalRawCubePhysicalMap z (2*R) = originalOrientedRawCubePhysicalMap b R :=
    funext (oriented_readout_rawPoint b R)
  refine ⟨by unfold originalOrientedRawCubePopulationCoupling; infer_instance, ?_, ?_⟩
  · change ((originalRawCubePopulationCoupling z (2*R) x).map (Prod.map F F)).map Prod.fst = _
    rw [Measure.map_map measurable_fst (hF.prodMap hF)]
    change (originalRawCubePopulationCoupling z (2*R) x).map (F ∘ Prod.fst) = _
    rw [← Measure.map_map hF measurable_fst, hbase.2.1, Measure.map_finset_sum' hF.aemeasurable]
    simp only [Measure.map_dirac' hF]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg Measure.dirac (oriented_readout_rawPoint b R (x i))
  · change ((originalRawCubePopulationCoupling z (2*R) x).map (Prod.map F F)).map Prod.snd = _
    rw [Measure.map_map measurable_snd (hF.prodMap hF)]
    change (originalRawCubePopulationCoupling z (2*R) x).map (F ∘ Prod.snd) = _
    rw [← Measure.map_map hF measurable_snd, hbase.2.2, Measure.map_smul,
      Measure.map_map hF hA, hread, map_originalUnitCube_oriented_eq_normalizedFiniteLaw b hR]

/-- Exact original Euclidean square energy is preserved under the actual raw
physical frame readout; no additional dimension factor enters the transport cost. -/
theorem originalOrientedRawCubePopulationCoupling_squareCost_eq
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (x : Fin n → (Fin q → ℝ)) :
    let c := fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm p.1-(EuclideanSpace.equiv (Fin q) ℝ).symm p.2‖^2
    Integrable c (originalOrientedRawCubePopulationCoupling b R x) ∧
      (∫ p, c p ∂originalOrientedRawCubePopulationCoupling b R x) =
        ∫ p, ‖p.1-p.2‖^2 ∂originalRawCubePopulationCoupling
          ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) x := by
  let F := originalOrientedCubeEuclideanReadout b
  have heF : MeasurableEmbedding (F : EuclideanSpace ℝ (Fin q) → (Fin q → ℝ)) :=
    F.toHomeomorph.measurableEmbedding
  have he := heF.prodMap heF
  have hc (p : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)) :
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (F p.1)-
        (EuclideanSpace.equiv (Fin q) ℝ).symm (F p.2)‖^2 = ‖p.1-p.2‖^2 := by
    rw [originalOrientedCubeEuclideanReadout_norm_sub]
  constructor
  · apply he.integrable_map_iff.mpr
    have hbaseI : Integrable (fun p ↦ ‖p.1-p.2‖^2) (originalRawCubePopulationCoupling
        ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) x) :=
      (originalIIDPhysicalCubePopulationCoupling_squareCost_le (originalNormalizedCubeLaw q)
        ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R)
        (fun i ↦ originalUnitCubeNormalization (x i))).1
    exact hbaseI.congr (Filter.Eventually.of_forall fun p ↦ (hc p).symm)
  · change (∫ p, ‖(EuclideanSpace.equiv (Fin q) ℝ).symm p.1-
        (EuclideanSpace.equiv (Fin q) ℝ).symm p.2‖^2 ∂(originalRawCubePopulationCoupling
          ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) x).map (Prod.map F F)) = _
    rw [he.integral_map]
    exact integral_congr_ae (Filter.Eventually.of_forall hc)

/-- The true same-frame raw population plan keeps the established Euclidean
expected matching rate exactly, with no extra q factor from changing frame. -/
theorem expected_originalOrientedRawCubePopulationCoupling_squareCost_rate
    (hq : 4 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    let energy := fun x : Fin n → (Fin q → ℝ) ↦ ∫ p,
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm p.1-(EuclideanSpace.equiv (Fin q) ℝ).symm p.2‖^2
        ∂originalOrientedRawCubePopulationCoupling b R x
    Integrable energy (Measure.pi (fun _ : Fin n ↦ cubeMeasure (Fin q) 1)) ∧
      (∫ x, energy x ∂Measure.pi (fun _ : Fin n ↦ cubeMeasure (Fin q) 1)) ≤
        ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(n : ℝ)^(1-2/(q : ℝ)) := by
  have h := expected_originalRawCubePopulationCoupling_squareCost_rate (n := n) hq
    ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R)
  have heq : (fun x : Fin n → (Fin q → ℝ) ↦ ∫ p,
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm p.1-(EuclideanSpace.equiv (Fin q) ℝ).symm p.2‖^2
        ∂originalOrientedRawCubePopulationCoupling b R x) =
      (fun x ↦ ∫ p, ‖p.1-p.2‖^2 ∂originalRawCubePopulationCoupling
        ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) x) :=
    funext fun x ↦ (originalOrientedRawCubePopulationCoupling_squareCost_eq b R x).2
  simpa only [heq] using h

end OTSelector.Reconstruction
