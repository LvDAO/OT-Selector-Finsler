import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching
import OTSelector.Finite.LegalMatchingValue

/-!
# Integer restrictions are actual matchings of the original finite arrays

A restricted integer edge plan whose endpoint measures are dominated by the
original finite input arrays has an exact partial-matching representation in
those original row and column indices. Every edge measure and every real cost
are retained exactly. This is the finite comparator extraction needed for
stationary-window recovery, rather than a replacement candidate space.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MetricSpace Y] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- Exact integer-plan extraction on the same original finite source and
target indices, with no endpoint-balance or extension-capacity premise. -/
theorem exists_originalIndex_partialMatching_of_integer_plan
    {m n : ℕ} (base : X × Y) (μ : LocalFiniteMeasure (X × Y))
    (hc : IsLegalCountingMeasure base μ)
    (source : Fin m → X) (target : Fin n → Y) (hs : Injective source) (ht : Injective target)
    (hsource : (μ : Measure (X × Y)).fst ≤ ∑ i, Measure.dirac (source i))
    (htarget : (μ : Measure (X × Y)).snd ≤ ∑ j, Measure.dirac (target j)) :
    ∃ σ : OTSelector.PartialMatching m n,
      (μ : Measure (X × Y)) = ∑ e ∈ σ.edges, Measure.dirac (source e.1, target e.2) := by
  have hsunit := ((isLegalSimpleCountingMeasure_iff base.1 _).mp
    (isLegalSimpleCountingMeasure_of_injective_tuple base.1 source hs)).2
  have htunit := ((isLegalSimpleCountingMeasure_iff base.2 _).mp
    (isLegalSimpleCountingMeasure_of_injective_tuple base.2 target ht)).2
  have hr (x : X) : (μ : Measure (X × Y)).map Prod.fst {x} ≤ 1 :=
    (hsource {x}).trans (hsunit x)
  have hcol (y : Y) : (μ : Measure (X × Y)).map Prod.snd {y} ≤ 1 :=
    (htarget {y}).trans (htunit y)
  have hrowinj := injOn_support_of_legalCounting_of_map_singleton_le_one base μ hc Prod.fst measurable_fst hr
  have hcolinj := injOn_support_of_legalCounting_of_map_singleton_le_one base μ hc Prod.snd measurable_snd hcol
  let F : Fin m × Fin n → X × Y := fun e ↦ (source e.1, target e.2)
  have hF : Injective F := by
    intro e f heq
    exact Prod.ext (hs (congrArg Prod.fst heq)) (ht (congrArg Prod.snd heq))
  let σ : OTSelector.PartialMatching m n :=
    { edges := Finset.univ.filter (fun e ↦ F e ∈ (μ : Measure (X × Y)).support)
      row_inj := by
        intro e he f hf heq
        have hpoint := hrowinj (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
          (congrArg source heq)
        exact hF hpoint
      col_inj := by
        intro e he f hf heq
        have hpoint := hcolinj (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2
          (congrArg target heq)
        exact hF hpoint }
  have hsourceNull : (∑ i, Measure.dirac (source i)) (range source)ᶜ = 0 := by
    rw [Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Measure.dirac_apply' _ (finite_range source).measurableSet.compl]
    exact indicator_of_notMem (by simp) _
  have htargetNull : (∑ j, Measure.dirac (target j)) (range target)ᶜ = 0 := by
    rw [Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Measure.dirac_apply' _ (finite_range target).measurableSet.compl]
    exact indicator_of_notMem (by simp) _
  have hsAE : ∀ᵐ e ∂(μ : Measure (X × Y)), e.1 ∈ range source := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    exact ae_iff.mpr (le_antisymm ((hsource _).trans_eq hsourceNull) bot_le)
  have htAE : ∀ᵐ e ∂(μ : Measure (X × Y)), e.2 ∈ range target := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    exact ae_iff.mpr (le_antisymm ((htarget _).trans_eq htargetNull) bot_le)
  let E := σ.edges.image F
  have hE : ∀ᵐ e ∂(μ : Measure (X × Y)), e ∈ E := by
    filter_upwards [hsAE, htAE, Measure.support_mem_ae (μ := (μ : Measure (X × Y)))] with e heS heT heSupp
    obtain ⟨i, hi⟩ := heS
    obtain ⟨j, hj⟩ := heT
    have heq : F (i, j) = e := Prod.ext hi hj
    refine Finset.mem_image.mpr ⟨(i, j), ?_, heq⟩
    change (i, j) ∈ Finset.univ.filter (fun e ↦ F e ∈ (μ : Measure (X × Y)).support)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, heq]
    exact heSupp
  have hmass (e : X × Y) (he : e ∈ E) : (μ : Measure (X × Y)) {e} = 1 := by
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp he
    have hsup : F ij ∈ (μ : Measure (X × Y)).support := (Finset.mem_filter.mp hij).2
    have hlo := one_le_singleton_of_mem_support_of_legalCounting base μ hc hsup
    apply le_antisymm ?_ hlo
    apply le_trans ?_ (hr (F ij).1)
    rw [Measure.map_apply measurable_fst (measurableSet_singleton (F ij).1)]
    exact measure_mono (singleton_subset_iff.mpr rfl)
  refine ⟨σ, ?_⟩
  calc
    (μ : Measure (X × Y)) = ∑ e ∈ E, (μ : Measure (X × Y)) {e} • Measure.dirac e :=
      Measure.ae_mem_finset_iff.mp hE
    _ = ∑ e ∈ E, Measure.dirac e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hmass e he, one_smul]
    _ = ∑ e ∈ σ.edges, Measure.dirac (source e.1, target e.2) := by
      exact Finset.sum_image (fun e _ f _ hef ↦ hF hef)

/-- The extracted original indices retain the actual legal relation whenever
the restricted integer plan uses that relation almost everywhere. -/
theorem originalIndex_partialMatching_isLegal_of_ae
    {m n : ℕ} (μ : LocalFiniteMeasure (X × Y))
    (source : Fin m → X) (target : Fin n → Y) (σ : OTSelector.PartialMatching m n)
    (hμ : (μ : Measure (X × Y)) = ∑ e ∈ σ.edges, Measure.dirac (source e.1, target e.2))
    (allowed : X → Y → Prop) (ha : ∀ᵐ e ∂(μ : Measure (X × Y)), allowed e.1 e.2) :
    PartialMatching.IsLegal (Finset.univ.filter (fun e ↦ allowed (source e.1) (target e.2))) σ := by
  intro e he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hbad
  have hz : (μ : Measure (X × Y)) {(source e.1, target e.2)} = 0 :=
    measure_mono_null (singleton_subset_iff.mpr hbad) (ae_iff.mp ha)
  have hdir : Measure.dirac (source e.1, target e.2) ≤ (μ : Measure (X × Y)) := by
    rw [hμ]
    exact Finset.single_le_sum
      (f := fun ij : Fin m × Fin n ↦ Measure.dirac (source ij.1, target ij.2))
      (fun _ _ ↦ Measure.zero_le _) he
  have h := hdir {(source e.1, target e.2)}
  rw [hz] at h
  simp at h

/-- The exact integer matching mass is the actual retained edge count. -/
theorem measure_univ_eq_originalIndex_partialMatching_card
    {m n : ℕ} (μ : LocalFiniteMeasure (X × Y))
    (source : Fin m → X) (target : Fin n → Y) (σ : OTSelector.PartialMatching m n)
    (hμ : (μ : Measure (X × Y)) = ∑ e ∈ σ.edges, Measure.dirac (source e.1, target e.2)) :
    (μ : Measure (X × Y)) univ = (σ.card : ℝ≥0∞) := by
  rw [hμ]
  simp [Measure.finsetSum_apply, OTSelector.PartialMatching.card]

/-- Every real original edge cost is integrable on the extracted finite core
and is exactly the cost of its actual original-index partial matching. -/
theorem integral_eq_originalIndex_partialMatching_cost
    {m n : ℕ} (μ : LocalFiniteMeasure (X × Y))
    (source : Fin m → X) (target : Fin n → Y) (σ : OTSelector.PartialMatching m n)
    (hμ : (μ : Measure (X × Y)) = ∑ e ∈ σ.edges, Measure.dirac (source e.1, target e.2))
    (cost : X × Y → ℝ) :
    Integrable cost (μ : Measure (X × Y)) ∧
      (∫ e, cost e ∂(μ : Measure (X × Y))) = σ.cost (fun i j ↦ cost (source i, target j)) := by
  rw [hμ]
  constructor
  · exact integrable_finsetSum_measure.mpr (fun e he ↦ integrable_dirac (by simp))
  · rw [integral_finsetSum_measure (fun e he ↦ integrable_dirac (by simp))]
    simp only [integral_dirac, OTSelector.PartialMatching.cost]

/-- A genuine integer window restriction produces a legal partial matching
on the original finite arrays, with exact cardinality and original signed
cost. No unrelated candidate space or iid law for unmatched points is used. -/
theorem exists_originalIndex_legal_partialMatching_cost_of_integer_plan
    {m n : ℕ} (base : X × Y) (μ : LocalFiniteMeasure (X × Y))
    (hc : IsLegalCountingMeasure base μ)
    (source : Fin m → X) (target : Fin n → Y) (hs : Injective source) (ht : Injective target)
    (hsource : (μ : Measure (X × Y)).fst ≤ ∑ i, Measure.dirac (source i))
    (htarget : (μ : Measure (X × Y)).snd ≤ ∑ j, Measure.dirac (target j))
    (allowed : X → Y → Prop) (ha : ∀ᵐ e ∂(μ : Measure (X × Y)), allowed e.1 e.2)
    (cost : X × Y → ℝ) :
    ∃ σ : OTSelector.PartialMatching m n,
      PartialMatching.IsLegal (Finset.univ.filter (fun e ↦ allowed (source e.1) (target e.2))) σ ∧
      (μ : Measure (X × Y)) = ∑ e ∈ σ.edges, Measure.dirac (source e.1, target e.2) ∧
      (μ : Measure (X × Y)) univ = (σ.card : ℝ≥0∞) ∧
      Integrable cost (μ : Measure (X × Y)) ∧
      (∫ e, cost e ∂(μ : Measure (X × Y))) = σ.cost (fun i j ↦ cost (source i, target j)) := by
  obtain ⟨σ, hσ⟩ := exists_originalIndex_partialMatching_of_integer_plan base μ hc source target hs ht hsource htarget
  exact ⟨σ, originalIndex_partialMatching_isLegal_of_ae μ source target σ hσ allowed ha, hσ,
    measure_univ_eq_originalIndex_partialMatching_card μ source target σ hσ,
    integral_eq_originalIndex_partialMatching_cost μ source target σ hσ cost⟩

end OTSelector.Reconstruction
