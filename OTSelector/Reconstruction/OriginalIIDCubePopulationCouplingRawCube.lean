import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingCubeNormalization
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingPhysical

/-! The actual open-cube sampler produces a genuine empirical-to-population
coupling at its unchanged raw observations, with the sharp physical cube rate. -/
open Set Function MeasureTheory
open OTSelector.Probability
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q n : ℕ}

/-- Literal physical positions of the original raw unit-cube observations. -/
def originalRawCubePhysicalMap (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (v : Fin q → ℝ) : EuclideanSpace ℝ (Fin q) :=
  z + L • (EuclideanSpace.equiv (Fin q) ℝ).symm v

/-- The actual raw-coordinate population transport, normalized only for its finite
optimizer construction. Original observations are recovered on their true support. -/
def originalRawCubePopulationCoupling (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (x : Fin n → (Fin q → ℝ)) :=
  originalIIDPhysicalCubePopulationCoupling (originalNormalizedCubeLaw q) z L
    (fun i ↦ originalUnitCubeNormalization (x i))

private theorem measurable_rawCubePhysicalMap (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (originalRawCubePhysicalMap z L) :=
  measurable_const.add ((EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.const_smul L)

/-- Reading the full normalized population gives precisely the original physical population. -/
theorem map_physical_originalNormalizedCubeLaw (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    (originalNormalizedCubeLaw q).map (originalIIDCubePhysicalMap z L) =
      (cubeMeasure (Fin q) 1).map (originalRawCubePhysicalMap z L) := by
  have hp : Measurable (dyadicCubePoint (q := q)) := measurable_pi_lambda _
    (fun i ↦ measurable_subtype_coe.comp (measurable_pi_apply i))
  rw [← map_dyadicCubePoint_originalNormalizedCubeLaw q,
    Measure.map_map (measurable_rawCubePhysicalMap z L) hp]
  rfl

/-- The same raw original sample yields a measurable finite plan; on its actual
unit-cube support the counted source and full physical population target are exact. -/
theorem originalRawCubePopulationCoupling_spec
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (originalRawCubePopulationCoupling (n := n) z L) ∧
    ∀ x : Fin n → (Fin q → ℝ), (∀ i, x i ∈ unitCube q) →
      let Γ := originalRawCubePopulationCoupling z L x
      IsFiniteMeasure Γ ∧
        Γ.map Prod.fst = ∑ i, Measure.dirac (originalRawCubePhysicalMap z L (x i)) ∧
        Γ.map Prod.snd = (n : ℝ≥0∞) •
          (cubeMeasure (Fin q) 1).map (originalRawCubePhysicalMap z L) := by
  have hn : Measurable (fun x : Fin n → (Fin q → ℝ) ↦
      fun i ↦ originalUnitCubeNormalization (x i)) :=
    measurable_pi_lambda _ (fun i ↦ measurable_originalUnitCubeNormalization.comp
      (measurable_pi_apply i))
  refine ⟨(measurable_originalIIDPhysicalCubePopulationCoupling _ z L).comp hn, ?_⟩
  intro x hx
  have h := originalIIDPhysicalCubePopulationCoupling_marginals
    (originalNormalizedCubeLaw q) z L (fun i ↦ originalUnitCubeNormalization (x i))
  have hread (i : Fin n) : originalIIDCubePhysicalMap z L
      (originalUnitCubeNormalization (x i)) = originalRawCubePhysicalMap z L (x i) := by
    unfold originalIIDCubePhysicalMap originalRawCubePhysicalMap
    rw [dyadicCubePoint_originalUnitCubeNormalization_of_mem_unitCube _ (hx i)]
  simpa only [hread, map_physical_originalNormalizedCubeLaw,
    originalRawCubePopulationCoupling] using h

/-- The original open-cube population plan has the actual expected Euclidean
square-cost rate, including an empty cloud, with no selected-population law input. -/
theorem expected_originalRawCubePopulationCoupling_squareCost_rate (hq : 4 < q)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Integrable (fun x : Fin n → (Fin q → ℝ) ↦
      ∫ p, ‖p.1 - p.2‖ ^ 2 ∂originalRawCubePopulationCoupling z L x)
      (Measure.pi (fun _ : Fin n ↦ cubeMeasure (Fin q) 1)) ∧
    (∫ x, ∫ p, ‖p.1 - p.2‖ ^ 2 ∂originalRawCubePopulationCoupling z L x
      ∂Measure.pi (fun _ : Fin n ↦ cubeMeasure (Fin q) 1)) ≤
        ((q : ℝ) * L ^ 2) * dyadicMatchingConstant q *
          (n : ℝ) ^ (1 - 2 / (q : ℝ)) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  let T : (Fin n → (Fin q → ℝ)) → (Fin n → DyadicUnitCube q) :=
    fun x i ↦ originalUnitCubeNormalization (x i)
  have hm : Measurable T := measurable_pi_lambda _
    (fun i ↦ measurable_originalUnitCubeNormalization.comp (measurable_pi_apply i))
  have hlaw : (Measure.pi (fun _ : Fin n ↦ cubeMeasure (Fin q) 1)).map T =
      Measure.pi (fun _ : Fin n ↦ originalNormalizedCubeLaw q) :=
    Measure.pi_map_pi (fun _ ↦ measurable_originalUnitCubeNormalization.aemeasurable)
  have h := expected_originalIIDPhysicalCubePopulationCoupling_squareCost_rate
    (n := n) hq (originalNormalizedCubeLaw q) z L
  have hmapI := h.1
  rw [← hlaw] at hmapI
  have heq := integral_map hm.aemeasurable hmapI.aestronglyMeasurable
  rw [hlaw] at heq
  exact ⟨hmapI.comp_aemeasurable hm.aemeasurable, heq.symm.trans_le h.2⟩

end OTSelector.Reconstruction
