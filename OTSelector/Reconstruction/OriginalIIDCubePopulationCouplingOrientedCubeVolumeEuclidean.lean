import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolumePopulation

/-! Read the very same oriented raw cube law and plan in true Euclidean space. -/

open Set Function MeasureTheory
open OTSelector.Probability
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
variable {q n : ℕ}

/-- The actual same-frame physical cube law, expressed in Euclidean coordinates. -/
theorem map_originalUnitCube_oriented_Euclidean_eq_normalizedFiniteLaw
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R) :
    (cubeMeasure (Fin q) 1).map
      ((EuclideanSpace.equiv (Fin q) ℝ).symm ∘ originalOrientedRawCubePhysicalMap b R) =
      (normalizedFiniteLaw (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R)))).map
        (EuclideanSpace.equiv (Fin q) ℝ).symm := by
  rw [← Measure.map_map (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable
    (measurable_originalOrientedRawCubePhysicalMap b R), map_originalUnitCube_oriented_eq_normalizedFiniteLaw b hR]

/-- The original oriented raw plan is read back without changing its physical points. -/
def originalOrientedEuclideanCubePopulationCoupling
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (x : Fin n → (Fin q → ℝ)) :
    Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)) :=
  (originalOrientedRawCubePopulationCoupling b R x).map
    (Prod.map (EuclideanSpace.equiv (Fin q) ℝ).symm (EuclideanSpace.equiv (Fin q) ℝ).symm)

theorem measurable_originalOrientedEuclideanCubePopulationCoupling
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    Measurable (originalOrientedEuclideanCubePopulationCoupling (n := n) b R) :=
  (Measure.measurable_map _ ((EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.prodMap
    (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable)).comp
      (measurable_originalOrientedRawCubePopulationCoupling b R)

/-- Exact original-atom and literal physical-cube marginals in the Euclidean
space used by the original-atom RN disintegration. -/
theorem originalOrientedEuclideanCubePopulationCoupling_spec
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R)
    (x : Fin n → (Fin q → ℝ)) (hx : ∀ i, x i ∈ unitCube q) :
    let Γ := originalOrientedEuclideanCubePopulationCoupling b R x
    IsFiniteMeasure Γ ∧
      Γ.map Prod.fst = ∑ i, Measure.dirac
        ((EuclideanSpace.equiv (Fin q) ℝ).symm (originalOrientedRawCubePhysicalMap b R (x i))) ∧
      Γ.map Prod.snd = (n : ℝ≥0∞) •
        (normalizedFiniteLaw (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R)))).map
          (EuclideanSpace.equiv (Fin q) ℝ).symm := by
  let F := (EuclideanSpace.equiv (Fin q) ℝ).symm
  have hF := F.continuous.measurable
  have hraw := originalOrientedRawCubePopulationCoupling_spec b hR x hx
  have : IsFiniteMeasure (originalOrientedRawCubePopulationCoupling b R x) := hraw.1
  refine ⟨by unfold originalOrientedEuclideanCubePopulationCoupling; infer_instance, ?_, ?_⟩
  · change ((originalOrientedRawCubePopulationCoupling b R x).map (Prod.map F F)).map Prod.fst = _
    rw [Measure.map_map measurable_fst (hF.prodMap hF)]
    change (originalOrientedRawCubePopulationCoupling b R x).map (F ∘ Prod.fst) = _
    rw [← Measure.map_map hF measurable_fst, hraw.2.1, Measure.map_finset_sum' hF.aemeasurable]
    simp only [Measure.map_dirac' hF]
    rfl
  · change ((originalOrientedRawCubePopulationCoupling b R x).map (Prod.map F F)).map Prod.snd = _
    rw [Measure.map_map measurable_snd (hF.prodMap hF)]
    change (originalOrientedRawCubePopulationCoupling b R x).map (F ∘ Prod.snd) = _
    rw [← Measure.map_map hF measurable_snd, hraw.2.2, Measure.map_smul]

/-- The Euclidean plan's cost is precisely the raw plan's actual Euclidean
physical cost, including an empty original array. -/
theorem originalOrientedEuclideanCubePopulationCoupling_squareCost_eq
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (x : Fin n → (Fin q → ℝ)) :
    Integrable (fun p ↦ ‖p.1-p.2‖^2) (originalOrientedEuclideanCubePopulationCoupling b R x) ∧
      (∫ p, ‖p.1-p.2‖^2 ∂originalOrientedEuclideanCubePopulationCoupling b R x) =
        ∫ p, ‖(EuclideanSpace.equiv (Fin q) ℝ).symm p.1-
          (EuclideanSpace.equiv (Fin q) ℝ).symm p.2‖^2 ∂originalOrientedRawCubePopulationCoupling b R x := by
  have heF : MeasurableEmbedding ((EuclideanSpace.equiv (Fin q) ℝ).symm :
      (Fin q → ℝ) → EuclideanSpace ℝ (Fin q)) :=
    (EuclideanSpace.equiv (Fin q) ℝ).symm.toHomeomorph.measurableEmbedding
  have he := heF.prodMap heF
  exact ⟨he.integrable_map_iff.mpr (originalOrientedRawCubePopulationCoupling_squareCost_eq b R x).1,
    he.integral_map _⟩

/-- The unchanged true Euclidean plan inherits the same expected assignment
rate, with no additional cost constant from either coordinate readout. -/
theorem expected_originalOrientedEuclideanCubePopulationCoupling_squareCost_rate
    (hq : 4 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    Integrable (fun x : Fin n → (Fin q → ℝ) ↦ ∫ p, ‖p.1-p.2‖^2
      ∂originalOrientedEuclideanCubePopulationCoupling b R x)
        (Measure.pi (fun _ : Fin n ↦ cubeMeasure (Fin q) 1)) ∧
      (∫ x, ∫ p, ‖p.1-p.2‖^2 ∂originalOrientedEuclideanCubePopulationCoupling b R x
        ∂Measure.pi (fun _ : Fin n ↦ cubeMeasure (Fin q) 1)) ≤
          ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(n : ℝ)^(1-2/(q : ℝ)) := by
  have h := expected_originalOrientedRawCubePopulationCoupling_squareCost_rate (n := n) hq b R
  have heq : (fun x : Fin n → (Fin q → ℝ) ↦ ∫ p, ‖p.1-p.2‖^2
      ∂originalOrientedEuclideanCubePopulationCoupling b R x) =
      (fun x ↦ ∫ p, ‖(EuclideanSpace.equiv (Fin q) ℝ).symm p.1-
        (EuclideanSpace.equiv (Fin q) ℝ).symm p.2‖^2 ∂originalOrientedRawCubePopulationCoupling b R x) :=
    funext fun x ↦ (originalOrientedEuclideanCubePopulationCoupling_squareCost_eq b R x).2
  simpa only [heq] using h

end OTSelector.Reconstruction
