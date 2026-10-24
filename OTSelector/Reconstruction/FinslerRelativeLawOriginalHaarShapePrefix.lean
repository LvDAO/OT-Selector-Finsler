import OTSelector.Reconstruction.FinslerRelativeLawOriginalPrefixModelLaw
import OTSelector.Reconstruction.FinslerRelativeLawOriginalNullShapeMean
import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellIntensity

/-! Exact original iid retained prefixes in Haar microcells, including null cells. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral
open scoped Topology ENNReal NNReal BigOperators unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- A literal original Haar/class restriction determines the full finite iid
shape law, without a positive-subcell premise. Null cells produce the exact
empty law; all other cells retain their original binomial count. -/
theorem finiteOriginalRestrictedData_haar_shape_law
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ)
    {event : Set X} (hevent : MeasurableSet event)
    (read : X → E × A) (hread : Measurable read)
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (index : Fin q → ℤ) (s : Set E) (hs : MeasurableSet s)
    (τ : Measure A) [IsFiniteMeasure τ] (hτ : 0 < τ.real univ)
    (hsource : (ν.restrict event).map read =
      (μ.restrict (s ∩ e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ)))).prod τ)
    (hbox : (μ (e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ))) * τ univ).toNNReal ≤ 1) :
    let _inst := normalizedFiniteLaw_probability τ hτ
    let p : unitInterval := ⟨(μ (e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ))) * τ univ).toNNReal,
      NNReal.coe_nonneg _, (by exact_mod_cast hbox)⟩
    (Measure.pi (fun _ : Fin N ↦ ν)).map
      (fun x ↦ mapBlockData (Prod.map
        (affineHaarCubeCoord e (fun l ↦ (index l : ℝ) / n) (n : ℝ≥0)⁻¹) id ∘ read)
        (finiteOriginalRestrictedData event x)) =
      binomialShapeBlockLaw q (normalizedFiniteLaw τ) N p (originalMicrocellShape e n index s) := by
  letI := normalizedFiniteLaw_probability τ hτ
  let B := e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ))
  let K := s ∩ B
  let m := μ.restrict K
  let shape := originalMicrocellShape e n index s
  let f := Prod.map (affineHaarCubeCoord e (fun l ↦ (index l : ℝ) / n) (n : ℝ≥0)⁻¹)
    (id : A → A)
  have hf : Measurable f := (measurable_affineHaarCubeCoord e _ _).prodMap measurable_id
  have hK : MeasurableSet K := hs.inter
    ((unitPartition.box n index).measurableSet_coe.preimage e.continuous.measurable)
  obtain ⟨c, hc, hlaws⟩ := exists_original_unitPartition_box_laws μ e n
  have hBmass : μ B = ((c * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ≥0∞) := (hlaws index).1
  have hBfin : μ B ≠ ∞ := by rw [hBmass]; exact ENNReal.coe_ne_top
  have hBnonzero : μ B ≠ 0 := by
    rw [hBmass]
    exact_mod_cast mul_ne_zero hc.ne' (pow_ne_zero _ (inv_ne_zero
      (by exact_mod_cast (NeZero.ne n) : (n : ℝ≥0) ≠ 0)))
  haveI : IsFiniteMeasure m := ⟨by
    rw [show m univ = μ K from Measure.restrict_apply_univ K]
    exact lt_of_le_of_lt (measure_mono inter_subset_right) hBfin.lt_top⟩
  have hmass : μ K = μ B * (cubeMeasure (Fin q) 1) shape := by
    have h := original_microcell_mass_eq μ e n index hs
    rw [← unitPartitionBox_haar_mass_eq μ e n index] at h
    exact h
  let p : unitInterval := ⟨(μ B * τ univ).toNNReal, NNReal.coe_nonneg _,
    (by exact_mod_cast hbox)⟩
  by_cases hzero : μ K = 0
  · have hνzero : ν event = 0 := by
      have h := congrArg (fun ρ : Measure (E × A) ↦ ρ univ) hsource
      have hmzero : m = 0 := Measure.restrict_eq_zero.mpr hzero
      change ((ν.restrict event).map read) univ = (m.prod τ) univ at h
      simpa only [Measure.map_apply hread MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply_univ, hmzero, Measure.zero_prod, Measure.coe_zero, Pi.zero_apply] using h
    have hshapezero : (cubeMeasure (Fin q) 1) shape = 0 := by
      rw [hzero] at hmass
      exact (mul_eq_zero.mp hmass.symm).resolve_left hBnonzero
    have h := finiteOriginalRestrictedData_null_law ν N hevent hνzero (f ∘ read) (hf.comp hread)
    dsimp only at h ⊢
    rw [binomialShapeBlockLaw_eq_empty_of_null q (normalizedFiniteLaw τ) N p hshapezero]
    exact h
  · have hmpos : 0 < m.real univ := by
      rw [measureReal_def, Measure.restrict_apply_univ]
      exact ENNReal.toReal_pos hzero (ne_top_of_le_ne_top hBfin (measure_mono inter_subset_right))
    letI := normalizedFiniteLaw_probability m hmpos
    have hprodpos : 0 < (m.prod τ).real univ := by
      rw [measureReal_def, ← univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
      exact mul_pos hmpos hτ
    have hpoint : normalizedFiniteLaw (m.prod τ) =
        (normalizedFiniteLaw m).prod (normalizedFiniteLaw τ) := normalizedFiniteLaw_prod_eq m τ
    have hcount : ((m.prod τ) univ).toNNReal =
        (μ B * τ univ).toNNReal * restrictionWeight (cubeMeasure (Fin q) 1) shape := by
      rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, hmass]
      simp only [ENNReal.toNNReal_mul, restrictionWeight]
      ring
    have hbase := finiteOriginalRestrictedData_normalized_model_law ν N hevent read hread
      (m.prod τ) hprodpos hsource
    dsimp only at hbase
    simp only [hpoint] at hbase
    have hobs : Measurable (fun x : Fin N → X ↦ mapBlockData read
        (finiteOriginalRestrictedData event x)) :=
      (measurable_mapBlockData hread).comp (measurable_finiteOriginalRestrictedData hevent)
    have h := congrArg (fun ρ ↦ ρ.map (mapBlockData f)) hbase
    rw [Measure.map_map (measurable_mapBlockData hf) hobs] at h
    have hcloud := original_microcell_blockDataLaw_map μ e n index hs hzero
      (normalizedFiniteLaw τ) (binomWeight N ((m.prod τ) univ).toNNReal)
    rw [hcloud, hcount] at h
    dsimp only at h ⊢
    simpa only [Function.comp_def, mapBlockData, binomialShapeBlockLaw, Real.toNNReal_coe] using h

end OTSelector.Reconstruction
