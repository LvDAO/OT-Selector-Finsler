import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudget
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsCounts

/-! True null law blocks have no observed original reserve atoms at any Poisson rate. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The actual thinned Poisson pair has law dirac (0,0) on two null clock classes,
including its genuine random observed prefix length. -/
theorem ae_originalRawReserve_null_class_counts (rate : ℝ≥0)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hμ : μ S = 0) (hν : ν T = 0) :
    ∀ᵐ z ∂twoMarkedCloudLaw q ℝ ℝ μ ν rate,
      originalReserveBlockCount z.1.1 (fun i ↦ (z.1.2 i).2) S = 0 ∧
      originalReserveBlockCount z.2.1 (fun i ↦ (z.2.2 i).2) T = 0 := by
  have hlaw := hasLaw_originalReserveObservedBlockCount_pair (q := q) μ ν rate hS hT
  simp only [hμ,hν,ENNReal.toNNReal_zero,mul_zero,poissonMeasure_zero,Measure.dirac_prod,Measure.map_dirac] at hlaw
  filter_upwards [hlaw.ae_eq_of_dirac] with z hz
  have hs := congrArg Prod.fst hz
  have ht := congrArg Prod.snd hz
  change originalReserveObservedBlockCount S z.1 = 0 at hs
  change originalReserveObservedBlockCount T z.2 = 0 at ht
  rw [originalReserveObservedBlockCount_eq_natCount] at hs ht
  exact ⟨hs,ht⟩

/-- One raw-reserve event excludes every actual zero-law block from both observed arrays. -/
theorem ae_all_originalRawReserve_zeroClockBlock_counts (rate : ℝ≥0) (G : OriginalStageClockGrid) :
    ∀ᵐ z ∂twoMarkedCloudLaw q ℝ ℝ μ ν rate,
      ∀ block : G.ClockSlabBlock μ ν, block ∉ G.positiveSlabBlocks μ ν →
        originalReserveBlockCount z.1.1 (fun i ↦ (z.1.2 i).2) (G.sourceBlockCell μ ν block) = 0 ∧
        originalReserveBlockCount z.2.1 (fun i ↦ (z.2.2 i).2) (G.targetBlockCell μ ν block) = 0 := by
  apply ae_all_iff.mpr
  intro block
  by_cases hb : block ∈ G.positiveSlabBlocks μ ν
  · exact ae_of_all _ (fun _ hn ↦ (hn hb).elim)
  have hz := G.zeroSlabBlock_restrict block hb
  filter_upwards [ae_originalRawReserve_null_class_counts rate
    (G.blockCells_measurable block).1 (G.blockCells_measurable block).2
    (Measure.restrict_eq_zero.mp hz.1) (Measure.restrict_eq_zero.mp hz.2)] with z hz
  exact fun _ ↦ hz

/-- A finite original counting law reads exactly its original mark-filter cardinality. -/
theorem originalFiniteCloud_clock_class_mass {m : ℕ}
    (x : Fin m → LegalMarkedPhysicalPoint q) (U : Finset (Fin m))
    {C : Set ℝ} :
    (∑ i ∈ U, Measure.dirac (x i)) {p | p.2 ∈ C} =
      ((U.filter (fun i ↦ (x i).2 ∈ C)).card : ℝ≥0∞) := by
  classical
  simp [Measure.finsetSum_apply,Set.indicator_apply,Finset.sum_boole]

/-- Every subset of the unchanged observed original indices remains null after
arbitrary position changes preserving its actual marks. No spatial iid callback is needed. -/
theorem originalFiniteReserve_clock_class_zero_of_raw_zero
    (raw : MarkedCloudSpace q ℝ) (v : Fin raw.1 → LegalMarkedPhysicalPoint q)
    (hmark : ∀ i, (v i).2 = (raw.2 i).2) (kept : Finset (Fin raw.1))
    {C : Set ℝ}
    (hraw : originalReserveBlockCount raw.1 (fun i ↦ (raw.2 i).2) C = 0) :
    (∑ i ∈ kept, Measure.dirac (v i)) {p | p.2 ∈ C} = 0 := by
  classical
  rw [originalReserveBlockCount_eq_remaining_univ] at hraw
  have hempty : (Finset.univ.filter (fun i : Fin raw.1 ↦ (raw.2 i).2 ∈ C)) = ∅ :=
    Finset.card_eq_zero.mp hraw
  have hnot (i : Fin raw.1) : (v i).2 ∉ C := by
    rw [hmark]
    intro hi
    have hm : i ∈ Finset.univ.filter (fun j : Fin raw.1 ↦ (raw.2 j).2 ∈ C) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
    rw [hempty] at hm
    exact Finset.notMem_empty i hm
  rw [originalFiniteCloud_clock_class_mass v kept]
  have he : kept.filter (fun i ↦ (v i).2 ∈ C) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    exact fun i _ ↦ hnot i
  simp only [he,Finset.card_empty,Nat.cast_zero]

/-- A real unused-original counting law has no labels in a class whose actual
port mass and actual kept reserve mass both vanish. -/
theorem originalUnused_filter_empty_of_clock_class_zero {m : ℕ}
    (x : Fin m → LegalMarkedPhysicalPoint q) (U : Finset (Fin m))
    (port reserve : Measure (LegalMarkedPhysicalPoint q))
    (hlaw : (∑ i ∈ U, Measure.dirac (x i)) = port+reserve)
    {C : Set ℝ}
    (hport : port {p | p.2 ∈ C} = 0) (hreserve : reserve {p | p.2 ∈ C} = 0) :
    U.filter (fun i ↦ (x i).2 ∈ C) = ∅ := by
  have hh := congrArg (fun ρ : Measure (LegalMarkedPhysicalPoint q) ↦ ρ {p | p.2 ∈ C}) hlaw
  rw [Measure.add_apply,hport,hreserve,zero_add,originalFiniteCloud_clock_class_mass x U] at hh
  exact Finset.card_eq_zero.mp (by exact_mod_cast hh)

end OTSelector.Reconstruction
