import OTSelector.Reconstruction.FinslerRelativeLawOriginalGridBoxProbability
import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellIntensity

/-! Literal original Haar/class box masses match the homogeneous microscopic grid. -/
open MeasureTheory Filter BoxIntegral
open MeasureTheory.Measure
open scoped Topology ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- One original Haar Jacobian works for every class mass and grid scale.
Every literal box eventually has a genuine probability, uniformly over all
integer box indices, equal to the homogeneous binomial grid probability. -/
theorem exists_original_haar_grid_box_probabilities
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) (hq : 0 < q) :
    ∃ c : ℝ≥0, 0 < c ∧
      μ.map e = (c : ℝ≥0∞) • (volume : Measure (Fin q → ℝ)) ∧ ∀ (classMass : ℝ≥0∞) (L : ℝ), 0 < L →
      ∀ᶠ N : ℕ in atTop, ∀ ν : Fin q → ℤ,
      let n := positiveMicroscopicGridOrder q L N
      let mass := (μ (e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) * classMass).toNNReal
      mass ≤ 1 ∧ (mass : ℝ) = (positiveMicroscopicCubeProbability q (c * classMass.toNNReal) L N : ℝ) := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c := addHaarScalarFactor (μ.map e) (volume : Measure (Fin q → ℝ))
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : μ.map e = c • (volume : Measure (Fin q → ℝ)) :=
    isAddLeftInvariant_eq_smul _ _
  have hmass (n : ℕ) [NeZero n] (ν : Fin q → ℤ) :
      μ (e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) =
        ((c * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ≥0∞) := by
    rw [unitPartitionBox_haar_mass_eq μ e n ν]
    have hscaled := map_affineHaarCubeCoord μ e hmap (fun l ↦ (ν l : ℝ) / n)
      (inv_pos.mpr (by exact_mod_cast n.pos_of_neZero) : 0 < (n : ℝ≥0)⁻¹)
    have hm := congrArg (fun ρ : Measure (Fin q → ℝ) ↦ ρ (seedUnitCube q)) hscaled
    rw [Measure.map_apply (measurable_affineHaarCubeCoord e _ _) (measurableSet_seedUnitCube q),
      Measure.smul_apply, volume_seedUnitCube] at hm
    simpa only [affineHaarCube, ENNReal.smul_one] using hm
  refine ⟨c, hc, by simpa only [Measure.coe_nnreal_smul] using hmap, ?_⟩
  intro classMass L hL
  filter_upwards [eventually_positiveMicroscopicCubeProbability_eq_original_box hq
    (c * classMass.toNNReal) hL] with N hN
  intro ν
  have hbox := hmass (positiveMicroscopicGridOrder q L N) ν
  have hreal : (μ (e ⁻¹' (unitPartition.box (positiveMicroscopicGridOrder q L N) ν :
      Set (Fin q → ℝ))) * classMass).toNNReal =
      (c * classMass.toNNReal) * ((positiveMicroscopicGridOrder q L N : ℝ≥0)⁻¹) ^ q := by
    rw [hbox, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
    ring
  dsimp only
  rw [hreal]
  exact ⟨hN.1, hN.2.symm⟩

end OTSelector.Reconstruction
