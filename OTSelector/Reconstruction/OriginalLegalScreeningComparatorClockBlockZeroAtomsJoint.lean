import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockZeroAtomsPorts
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockZeroAtomsRaw

/-! Null actual block atoms vanish on the unchanged original main-plus-raw-reserve law. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- A single event on the true original Q times raw reserve law simultaneously gives
zero actual port masses and zero original observed reserve counts in every zero block. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_originalReserve_zeroClockBlocks
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) (rate : ℝ≥0) (G : OriginalStageClockGrid) :
    ∀ᵐ p ∂originalMainReserveExperimentLaw Q rate,
      ∀ block : G.ClockSlabBlock μ ν, block ∉ G.positiveSlabBlocks μ ν →
      ∀ A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)), ∀ K : Set (Fin q → ℝ),
        (originalStageWindowSourcePortPlan A K p.1 : Measure (LegalMarkedPhysicalEdge q)).fst
          {x | x.2 ∈ G.sourceBlockCell μ ν block} = 0 ∧
        (originalStageWindowTargetPortPlan A K p.1 : Measure (LegalMarkedPhysicalEdge q)).snd
          {x | x.2 ∈ G.targetBlockCell μ ν block} = 0 ∧
        originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2) (G.sourceBlockCell μ ν block) = 0 ∧
        originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2) (G.targetBlockCell μ ν block) = 0 := by
  have hm := ae_fst_of_ae (ν := twoMarkedCloudLaw q ℝ ℝ μ ν rate)
    (Q.ae_all_zeroClockBlocks_port_class_zero G)
  have hr := ae_snd_of_ae (μ := (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (ae_all_originalRawReserve_zeroClockBlock_counts (q := q) (μ := μ) (ν := ν) rate G)
  filter_upwards [hm,hr] with p hm hr
  intro block hb A K
  exact ⟨(hm block hb A K).1,(hm block hb A K).2,(hr block hb).1,(hr block hb).2⟩

/-- On that same event any actual unused-original counting laws have empty
zero-block filters, for every mark-preserving physical realization of the raw arrays. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_originalUnused_zeroClockBlock_filters
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) (rate : ℝ≥0) (G : OriginalStageClockGrid) :
    ∀ᵐ p ∂originalMainReserveExperimentLaw Q rate,
      ∀ (m n : ℕ) (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
        (U : Finset (Fin m)) (V : Finset (Fin n))
        (vs : Fin p.2.1.1 → LegalMarkedPhysicalPoint q) (vt : Fin p.2.2.1 → LegalMarkedPhysicalPoint q),
      (∀ i, (vs i).2 = (p.2.1.2 i).2) → (∀ j, (vt j).2 = (p.2.2.2 j).2) →
      ∀ (sourceKept : Finset (Fin p.2.1.1)) (targetKept : Finset (Fin p.2.2.1))
        (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (K : Set (Fin q → ℝ)),
      (∑ i ∈ U, Measure.dirac (x i)) =
        (originalStageWindowSourcePortPlan A K p.1 : Measure (LegalMarkedPhysicalEdge q)).fst +
          ∑ j ∈ sourceKept, Measure.dirac (vs j) →
      (∑ i ∈ V, Measure.dirac (y i)) =
        (originalStageWindowTargetPortPlan A K p.1 : Measure (LegalMarkedPhysicalEdge q)).snd +
          ∑ j ∈ targetKept, Measure.dirac (vt j) →
      ∀ block : G.ClockSlabBlock μ ν, block ∉ G.positiveSlabBlocks μ ν →
        U.filter (fun i ↦ (x i).2 ∈ G.sourceBlockCell μ ν block) = ∅ ∧
        V.filter (fun j ↦ (y j).2 ∈ G.targetBlockCell μ ν block) = ∅ := by
  filter_upwards [Q.ae_all_originalReserve_zeroClockBlocks rate G] with p hp
  intro m n x y U V vs vt hvs hvt sourceKept targetKept A K hs ht block hb
  have hz := hp block hb A K
  have hsource := originalFiniteReserve_clock_class_zero_of_raw_zero p.2.1 vs hvs sourceKept hz.2.2.1
  have htarget := originalFiniteReserve_clock_class_zero_of_raw_zero p.2.2 vt hvt targetKept hz.2.2.2
  exact ⟨originalUnused_filter_empty_of_clock_class_zero x U _ _ hs hz.1 hsource,
    originalUnused_filter_empty_of_clock_class_zero y V _ _ ht hz.2.1 htarget⟩

end OTSelector.Reconstruction
