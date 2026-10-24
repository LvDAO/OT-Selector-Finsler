import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellIntensity
import OTSelector.Probability.BinomialShapeLaw

/-! Exact original Haar/class binomial prefixes in the literal microscopic shape. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral
open scoped Topology ENNReal NNReal BigOperators unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- One actual Haar Jacobian fixes every full-box probability before the
retained class mass and measurable cell are chosen. For positive original
subcells, normalizing all used coordinates gives the literal binomial shape
law at that full-box probability, with the original retained count unchanged. -/
theorem exists_original_microcell_binomial_prefix_laws
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (classMass : ℝ≥0) (s : Set E) (hs : MeasurableSet s),
      ∀ (n : ℕ) [NeZero n] (ν : Fin q → ℤ) (N : ℕ)
        (hmass : μ (s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) ≠ 0)
        (hbox : (c * classMass) * ((n : ℝ≥0)⁻¹) ^ q ≤ 1)
        (A : Type*) [MeasurableSpace A] (α : Measure A) [IsProbabilityMeasure α],
      let K := s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))
      let _inst := normalized_original_unitPartitionCell_probability μ e n ν
        (hs.inter ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable))
        inter_subset_right hmass
      let p : unitInterval := ⟨((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0),
        (show (0 : ℝ) ≤ ((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) from NNReal.coe_nonneg _),
        (show (((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ) ≤ 1 from by exact_mod_cast hbox)⟩
      (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α)
        (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal)).map
          (mapBlockData (Prod.map
            (affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹) id)) =
        binomialShapeBlockLaw q α N p (originalMicrocellShape e n ν s) := by
  obtain ⟨c, hc, hlaws⟩ := exists_original_microcell_intensity_laws μ e
  refine ⟨c, hc, ?_⟩
  intro classMass s hs n _ ν N hmass hbox A _ α _
  let K := s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))
  have hK : MeasurableSet K := hs.inter
    ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable)
  letI := normalized_original_unitPartitionCell_probability μ e n ν hK inter_subset_right hmass
  have hp : (μ K * (classMass : ℝ≥0∞)).toNNReal =
      ((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q) *
        restrictionWeight (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s) := by
    rw [(hlaws n ν).2 classMass s hs, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
    rfl
  dsimp only
  rw [hp]
  have h := original_microcell_blockDataLaw_map μ e n ν hs hmass α
    (binomWeight N (((c * classMass) * ((n : ℝ≥0)⁻¹) ^ q) *
      restrictionWeight (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s)))
  simpa only [binomialShapeBlockLaw, Real.toNNReal_coe] using h

end OTSelector.Reconstruction
