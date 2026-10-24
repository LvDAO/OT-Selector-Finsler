import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation
import OTSelector.Reconstruction.MarkedStationaryValueLegalScalarRepair

/-!
# Legal block recovery on the original conditional clock populations

The already constructed original calibration and compact disjoint carriers
produce a uniform absolute clock-support gap. One finite bin partition of the
global compact clock range then controls legal block recovery on almost every
original conditional population, with one class constant independent of the
root and the finite observations. No neighborhood-rank or sample-balance
assumption is introduced.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z] [MeasurableEq Z]

/-- A common finite scalar partition and the absolute conditional support gap
are produced once from the original compact disjoint calibrated carriers. -/
theorem exists_population_conditional_scalar_bins
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → Z} (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {u : M → ℝ} (hu : Continuous u) {A B N : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hN : MeasurableSet N)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∃ gap : ℝ, 0 < gap ∧ ∃ _bins : FiniteScalarBins (u '' A ∪ u '' B) gap,
      ∀ᵐ z ∂μ.map a,
        (condDistrib u a μ z).support ⊆ u '' A ∪ u '' B ∧
        ∀ s ∈ (condDistrib u a μ z).support, ∀ t ∈ (condDistrib u a ν z).support,
          gap ≤ |t - s| := by
  obtain ⟨gap, hgap, hsep⟩ := exists_population_conditional_separation μ ν ha hbalance hu
    hA hB hAB hN hμA hνB hμN hνN horder
  obtain ⟨bins⟩ := exists_finiteScalarBins ((hA.image hu).union (hB.image hu)) hgap
  have hsourceImage := ae_support_map_condDistrib_subset_compact_image μ ha hA hμA hu
  have hclock := ae_condDistrib_clock_eq_map_id μ a hu.measurable
  refine ⟨gap, hgap, bins, ?_⟩
  filter_upwards [hsep, hsourceImage, hclock] with z hz hzi hzc
  constructor
  · intro s hs
    apply Or.inl
    apply hzi
    rw [← hzc]
    exact hs
  · intro s hs t ht
    simpa only [Real.dist_eq, abs_sub_comm] using hz.separated s hs t ht

/-- Original calibrated conditional supports supply all finite-class data
needed for the actual legal block pressure comparison. -/
theorem exists_population_conditional_legal_block_recovery
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → Z} (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {u : M → ℝ} (hu : Continuous u) {A B N : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hN : MeasurableSet N)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∃ gap : ℝ, 0 < gap ∧ ∃ bins : FiniteScalarBins (u '' A ∪ u '' B) gap,
      ∀ᵐ z ∂μ.map a, ∀ (m n : ℕ) (source : Fin m → ℝ) (target : Fin n → ℝ),
        (∀ i, source i ∈ (condDistrib u a μ z).support) →
        (∀ j, target j ∈ (condDistrib u a ν z).support) →
        ∀ (K : ℕ) (block : Fin K → Finset (Fin m × Fin n)),
          (∀ b, block b ⊆ scalarClockLegalGraph source target) →
          Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.fst)
            ((block b').image Prod.fst)) →
          Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.snd)
            ((block b').image Prod.snd)) →
          ∀ (c : Fin m → Fin n → ℝ) (C : ℝ), 0 ≤ C → (∀ i j, |c i j| ≤ C) →
            PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c ≤
              (∑ b, PartialMatching.legalMaximumValue (block b) c) +
                ((PartialMatching.legalMaximumCard (scalarClockLegalGraph source target) -
                  ∑ b, PartialMatching.legalMaximumCard (block b) : ℕ) : ℝ) *
                    ((2 * (bins.count : ℝ) - 1) * C) := by
  obtain ⟨gap, hgap, bins, hbins⟩ := exists_population_conditional_scalar_bins μ ν ha hbalance hu
    hA hB hAB hN hμA hνB hμN hνN horder
  refine ⟨gap, hgap, bins, ?_⟩
  filter_upwards [hbins] with z hz
  intro m n source target hs ht K block hsub hrows hcols c C hC0 hC
  exact bins.legalMaximumValue_le_sum_blocks_add_deficit hgap source target
    (fun i ↦ hz.1 (hs i)) (fun i j ↦ hz.2 _ (hs i) _ (ht j))
    block hsub hrows hcols c hC0 hC

end OTSelector.Reconstruction
