import OTSelector.Reconstruction.FinslerOriginalScalarRangeClockModel
import OTSelector.Probability.FiniteCellClassFlow
import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure
import OTSelector.Transport.Coupling.WindowPairFlow
import OTSelector.Reconstruction.FinslerPhysicalSceneCoordinates
import OTSelector.Reconstruction.FinslerOriginalClassRetentionPressure

/-! The continuous original clock law retained by the literal finite mask has
exactly the original normalized pair-class observation. Lost mass stays in its
original physical intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Classifying a point in its original scalar range has exactly its original
bin membership, including empty classes and all bin boundaries. -/
theorem FiniteScalarBins.rangeClassify_eq_iff {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (x : range) (j : Fin Q.count) :
    Q.rangeClassify x = j ↔ x.val ∈ Q.cell j := by
  constructor
  · intro h
    simpa only [h] using Q.rangeClassify_mem x
  · exact Q.rangeClassify_eq_of_mem j

/-- Original clock rectangles are the exact atoms of the unchanged continuous
law's finite observation. No independent class sample is substituted. -/
theorem FiniteScalarBins.clockClassPairMeasure_eq_original_observation
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (range × range)) [IsFiniteMeasure π] :
    clockClassPairMeasure
        (actualClockClassFlow (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell) =
      π.map (Prod.map Q.rangeClassify Q.rangeClassify) := by
  apply Measure.ext_of_singleton
  rintro ⟨i,j⟩
  have hpre : (Prod.map Q.rangeClassify Q.rangeClassify) ⁻¹' {(i,j)} =
      (Prod.map Subtype.val Subtype.val) ⁻¹' (Q.cell i ×ˢ Q.cell j) := by
    ext ⟨x,y⟩
    change (Q.rangeClassify x,Q.rangeClassify y) = (i,j) ↔
      x.val ∈ Q.cell i ∧ y.val ∈ Q.cell j
    rw [Prod.mk.injEq,Q.rangeClassify_eq_iff,Q.rangeClassify_eq_iff]
  have hraw : clockClassPairMeasure
      (actualClockClassFlow (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell) {(i,j)} =
      ENNReal.ofReal (actualClockClassFlow
        (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell i j) := by
    simp [clockClassPairMeasure,finiteClassPopulationCoupling,Measure.finsetSum_apply,
      Measure.smul_apply,Measure.dirac_prod_dirac,Pi.single_apply,Prod.mk.injEq,ite_and]
  rw [hraw,actualClockClassFlow,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [Measure.map_apply (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify)
    (measurableSet_singleton (i,j)), hpre]
  exact Measure.map_apply (measurable_subtype_coe.prodMap measurable_subtype_coe)
    ((Q.measurable_cell i).prod (Q.measurable_cell j))


/-- Restricting the actual finite pair measure to its original legal mask is
exactly masking its raw weights, with no change to their mass. -/
theorem clockClassPairMeasure_masked_eq_restrict
    {I J : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSpace J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (P₀ : I → J → ℝ) (allowed : I → J → Prop) :
    clockClassPairMeasure (maskedClockFlow allowed P₀) =
      (clockClassPairMeasure P₀).restrict {p | allowed p.1 p.2} := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨i,j⟩
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  by_cases hij : allowed i j
  · have hset : {(i,j)} ∩ {p | allowed p.1 p.2} = {(i,j)} := by
      ext p
      simp only [mem_inter_iff,mem_singleton_iff,mem_ofPred_eq]
      aesop
    rw [hset]
    simp [clockClassPairMeasure,finiteClassPopulationCoupling,Measure.finsetSum_apply,
      Measure.smul_apply,Measure.dirac_prod_dirac,Pi.single_apply,Prod.mk.injEq,ite_and,
      maskedClockFlow,hij]
  · have hset : {(i,j)} ∩ {p | allowed p.1 p.2} = ∅ := by
      ext p
      simp only [mem_inter_iff,mem_singleton_iff,mem_ofPred_eq,mem_empty_iff_false]
      aesop
    rw [hset,measure_empty]
    simp [clockClassPairMeasure,finiteClassPopulationCoupling,Measure.finsetSum_apply,
      Measure.smul_apply,Measure.dirac_prod_dirac,Pi.single_apply,Prod.mk.injEq,ite_and,
      maskedClockFlow,hij]

/-- Observing the actual continuous law after legal retention gives precisely
its original masked pair weights. This is a deterministic equality of laws. -/
theorem FiniteScalarBins.maskedClockClassPairMeasure_eq_original_observation
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (range × range)) [IsFiniteMeasure π]
    (allowed : Fin Q.count → Fin Q.count → Prop) :
    clockClassPairMeasure (maskedClockFlow allowed
        (actualClockClassFlow (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell)) =
      (π.restrict {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)}).map
        (Prod.map Q.rangeClassify Q.rangeClassify) := by
  rw [clockClassPairMeasure_masked_eq_restrict,
    Q.clockClassPairMeasure_eq_original_observation π]
  exact Measure.restrict_map (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify)
    (Set.to_countable {p : Fin Q.count × Fin Q.count | allowed p.1 p.2}).measurableSet

/-- Normalization by the actual retained mass commutes with observing the
unchanged continuous law. No lost original mass is absorbed into probability. -/
theorem FiniteScalarBins.normalized_maskedClockClassPairMeasure_eq_original_observation
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (range × range)) [IsFiniteMeasure π]
    (allowed : Fin Q.count → Fin Q.count → Prop) :
    normalizedClockClassPairMeasure (maskedClockFlow allowed
        (actualClockClassFlow (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell)) =
      (normalizedFiniteLaw
        (π.restrict {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)})).map
          (Prod.map Q.rangeClassify Q.rangeClassify) := by
  rw [normalizedClockClassPairMeasure,
    Q.maskedClockClassPairMeasure_eq_original_observation π allowed,
    normalizedFiniteLaw_map _ _ (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify)]


/-- The total original masked class weight is precisely the mass of the
continuous original retained law, before probability normalization. -/
theorem FiniteScalarBins.masked_clock_mass_eq_original_retained_mass
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (range × range)) [IsFiniteMeasure π]
    (allowed : Fin Q.count → Fin Q.count → Prop) :
    (∑ i, ∑ j, maskedClockFlow allowed
        (actualClockClassFlow (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell) i j) =
      (π.restrict {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)}).real univ := by
  have hnonneg i j : 0 ≤ maskedClockFlow allowed
      (actualClockClassFlow (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell) i j := by
    dsimp only [maskedClockFlow]
    split_ifs
    · exact actualClockClassFlow_nonneg _ _ _ _ _
    · exact le_refl _
  rw [← clockClassPairMeasure_real_univ _ hnonneg,
    Q.maskedClockClassPairMeasure_eq_original_observation π allowed]
  exact map_measureReal_apply
    (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify) MeasurableSet.univ

/-- Positive scalar physical intensity changes the retained mass, while the
normalized original continuous-law observation remains exactly the same. -/
theorem FiniteScalarBins.normalized_scaled_masked_weights_eq_original_observation
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (range × range)) [IsFiniteMeasure π]
    (allowed : Fin Q.count → Fin Q.count → Prop)
    (hmass : 0 < (π.restrict
      {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)}).real univ)
    {c : ℝ} (hc : 0 < c) :
    normalizedClockClassPairMeasure (fun i j ↦ c * maskedClockFlow allowed
        (actualClockClassFlow (π.map (Prod.map Subtype.val Subtype.val)) Q.cell Q.cell) i j) =
      (normalizedFiniteLaw
        (π.restrict {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)})).map
          (Prod.map Q.rangeClassify Q.rangeClassify) := by
  rw [normalizedClockClassPairMeasure_const_mul]
  · exact Q.normalized_maskedClockClassPairMeasure_eq_original_observation π allowed
  · intro i j
    dsimp only [maskedClockFlow]
    split_ifs
    · exact actualClockClassFlow_nonneg _ _ _ _ _
    · exact le_refl _
  · rwa [Q.masked_clock_mass_eq_original_retained_mass π allowed]
  · exact hc

end OTSelector.Reconstruction
