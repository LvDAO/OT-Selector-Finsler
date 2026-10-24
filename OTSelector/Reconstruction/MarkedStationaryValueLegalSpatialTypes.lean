import OTSelector.Reconstruction.MarkedStationaryValueLegalPoisson
import OTSelector.Reconstruction.MarkedStationaryValueLegalNestedBlocks

/-!
# Original Poisson joint spatial and population type counts

The type of one actual point may depend on both its original spatial position
and its original mark. Common point type laws then give the unchanged original
Poisson histogram estimate, including nonuniform spatial partitions.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {q : ℕ} {A B T : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace T]

/-- The actual count and the types of original full points. -/
def pointTypeCloud (tag : ((Fin q → ℝ) × A) → T) (z : MarkedCloudSpace q A) :
    ℕ × (ℕ → T) := (z.1, fun i ↦ tag (z.2 i))

theorem measurable_pointTypeCloud {tag : ((Fin q → ℝ) × A) → T} (ht : Measurable tag) :
    Measurable (pointTypeCloud tag) := by
  unfold pointTypeCloud
  fun_prop

theorem map_markedPoissonLaw_pointTypes (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    {tag : ((Fin q → ℝ) × A) → T} (ht : Measurable tag) (r : ℝ≥0) :
    (markedPoissonLaw q A α r).map (pointTypeCloud tag) =
      (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦
        ((cubeMeasure (Fin q) 1).prod α).map tag)) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  unfold markedPoissonLaw pointTypeCloud markedSeqLaw
  change ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦
      (cubeMeasure (Fin q) 1).prod α))).map
      (Prod.map id (fun x : ℕ → (Fin q → ℝ) × A ↦ fun i ↦ tag (x i))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    Measure.infinitePi_map_pi (μ := fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α)
      (f := fun _ : ℕ ↦ tag) (fun _ ↦ ht)]

/-- Common original full-point type laws produce the exact independent type
Poisson law on both original colors. -/
theorem map_twoMarkedCloudLaw_pointTypes (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {tagA : ((Fin q → ℝ) × A) → T} {tagB : ((Fin q → ℝ) × B) → T}
    (hA : Measurable tagA) (hB : Measurable tagB) (L : Measure T) [IsProbabilityMeasure L]
    (hLA : ((cubeMeasure (Fin q) 1).prod α).map tagA = L)
    (hLB : ((cubeMeasure (Fin q) 1).prod β).map tagB = L) (r : ℝ≥0) :
    (twoMarkedCloudLaw q A B α β r).map (Prod.map (pointTypeCloud tagA) (pointTypeCloud tagB)) =
      (poissonTypeLaw T L r).prod (poissonTypeLaw T L r) := by
  unfold twoMarkedCloudLaw
  rw [← Measure.map_prod_map _ _ (measurable_pointTypeCloud hA) (measurable_pointTypeCloud hB),
    map_markedPoissonLaw_pointTypes q α hA, map_markedPoissonLaw_pointTypes q β hB, hLA, hLB]
  rfl

/-- The original joint point-type histogram discrepancy. -/
def pointTypeDiscrepancy {K : ℕ} (tagA : ((Fin q → ℝ) × A) → Fin K)
    (tagB : ((Fin q → ℝ) × B) → Fin K) (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  ∑ b : Fin K, |(poissonTypeCount (pointTypeCloud tagA ω.1) b : ℝ) -
    (poissonTypeCount (pointTypeCloud tagB ω.2) b : ℝ)|

/-- Nonuniform spatial partitions are covered by the same original Poisson
histogram bound as finite population types. -/
theorem pointType_discrepancy_integrable_bound (q : ℕ) {K : ℕ} [NeZero K]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {tagA : ((Fin q → ℝ) × A) → Fin K} {tagB : ((Fin q → ℝ) × B) → Fin K}
    (hA : Measurable tagA) (hB : Measurable tagB)
    (L : Measure (Fin K)) [IsProbabilityMeasure L]
    (hLA : ((cubeMeasure (Fin q) 1).prod α).map tagA = L)
    (hLB : ((cubeMeasure (Fin q) 1).prod β).map tagB = L) (r : ℝ≥0) :
    Integrable (pointTypeDiscrepancy (q := q) tagA tagB) (twoMarkedCloudLaw q A B α β r) ∧
      (∫ ω, pointTypeDiscrepancy (q := q) tagA tagB ω ∂twoMarkedCloudLaw q A B α β r) ≤
        Real.sqrt (2 * (r : ℝ) * K) := by
  let P := poissonTypeLaw (Fin K) L r
  let f := fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
    ∑ b : Fin K, |(poissonTypeCount z.1 b : ℝ) - (poissonTypeCount z.2 b : ℝ)|
  let project := Prod.map (pointTypeCloud (q := q) tagA) (pointTypeCloud (q := q) tagB)
  have hp : MeasurePreserving project (twoMarkedCloudLaw q A B α β r) (P.prod P) :=
    ⟨(measurable_pointTypeCloud hA).prodMap (measurable_pointTypeCloud hB),
      map_twoMarkedCloudLaw_pointTypes q α β hA hB L hLA hLB r⟩
  have hbase := poissonType_discrepancy_integrable_bound L r
  have hcount : Measurable (poissonTypeCount (T := Fin K)) := measurable_poissonTypeCount
  have hfm : Measurable f := by
    apply Finset.measurable_sum
    intro b _
    have hfst : Measurable (fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
        (poissonTypeCount z.1 b : ℝ)) :=
      measurable_from_nat.comp (((measurable_pi_apply b).comp hcount).comp measurable_fst)
    have hsnd : Measurable (fun z : (ℕ × (ℕ → Fin K)) × (ℕ × (ℕ → Fin K)) ↦
        (poissonTypeCount z.2 b : ℝ)) :=
      measurable_from_nat.comp (((measurable_pi_apply b).comp hcount).comp measurable_snd)
    exact (hfst.sub hsnd).abs
  have hid : (∫ ω, pointTypeDiscrepancy (q := q) tagA tagB ω
      ∂twoMarkedCloudLaw q A B α β r) = ∫ z, f z ∂P.prod P := by
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hfm.aestronglyMeasurable).symm
  exact ⟨hp.integrable_comp_of_integrable hbase.1, hid.trans_le hbase.2⟩

/-- A cell and a population tag have their literal product law on the
independent original spatial-mark point. -/
theorem map_point_jointSpatialType (q : ℕ) {β : Type*} [MeasurableSpace β]
    (α : Measure A) [IsProbabilityMeasure α] {cell : (Fin q → ℝ) → β}
    {tag : A → T} (hc : Measurable cell) (ht : Measurable tag) :
    ((cubeMeasure (Fin q) 1).prod α).map (fun p ↦ (cell p.1, tag p.2)) =
      ((cubeMeasure (Fin q) 1).map cell).prod (α.map tag) := by
  exact (Measure.map_prod_map _ _ hc ht).symm

/-- Finite graph fibers are measurable when every actual edge event is. -/
theorem measurableSet_graph_eq_of_mem {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    (G : Ω → Finset E) (hG : ∀ e, MeasurableSet {ω | e ∈ G ω}) (edges : Finset E) :
    MeasurableSet {ω | G ω = edges} := by
  have hrepr : {ω | G ω = edges} = ⋂ e, {ω | e ∈ G ω ↔ e ∈ edges} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, Finset.ext_iff]
  rw [hrepr]
  apply MeasurableSet.iInter
  intro e
  by_cases he : e ∈ edges
  · simpa only [he, iff_true] using hG e
  · have hnot : MeasurableSet {ω | ¬e ∈ G ω} := (hG e).compl
    simpa only [he, iff_false] using hnot

/-- The actual original-index legal child graph for an arbitrary spatial label. -/
def spatialLegalMarkedGraph (q m n : ℕ) {β : Type*} [Fintype β] [DecidableEq β]
    (cell : (Fin q → ℝ) → β) (source : A → ℝ) (target : B → ℝ)
    (b : β) (ω : TwoMarkedCloudSpace q A B) : Finset (Fin m × Fin n) :=
  PartialMatching.spatialLegalBlock (legalMarkedGraph q m n source target ω)
    (fun i ↦ cell (mSourcePoint ω i)) (fun j ↦ cell (mTargetPoint ω j)) b

theorem measurableSet_spatialLegalMarkedGraph_eq (q m n : ℕ)
    {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {cell : (Fin q → ℝ) → β} {source : A → ℝ} {target : B → ℝ}
    (hc : Measurable cell) (hs : Measurable source) (ht : Measurable target)
    (b : β) (edges : Finset (Fin m × Fin n)) :
    MeasurableSet {ω : TwoMarkedCloudSpace q A B |
      spatialLegalMarkedGraph q m n cell source target b ω = edges} := by
  apply measurableSet_graph_eq_of_mem
  intro e
  have hclock := measurableSet_lt (hs.comp (measurable_mSourceMark q e.1))
    (ht.comp (measurable_mTargetMark q e.2))
  have hsource : MeasurableSet {ω : TwoMarkedCloudSpace q A B |
      cell (mSourcePoint ω e.1) = b} :=
    measurableSet_eq_fun (hc.comp (measurable_mSourcePoint q e.1)) measurable_const
  have htarget : MeasurableSet {ω : TwoMarkedCloudSpace q A B |
      cell (mTargetPoint ω e.2) = b} :=
    measurableSet_eq_fun (hc.comp (measurable_mTargetPoint q e.2)) measurable_const
  simpa only [spatialLegalMarkedGraph, PartialMatching.spatialLegalBlock, legalMarkedGraph,
    Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_def, Set.ofPred_and] using
    hclock.inter (hsource.inter htarget)

/-- Count selection of the actual legal spatial graph preserves measurability. -/
theorem measurable_spatialLegalMarkedCard_cast (q : ℕ)
    {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {cell : (Fin q → ℝ) → β} {source : A → ℝ} {target : B → ℝ}
    (hc : Measurable cell) (hs : Measurable source) (ht : Measurable target) (b : β) :
    Measurable (fun ω : TwoMarkedCloudSpace q A B ↦
      (PartialMatching.legalMaximumCard (spatialLegalMarkedGraph q (mSourceCount ω)
        (mTargetCount ω) cell source target b ω) : ℝ)) := by
  have hfixed (mn : ℕ × ℕ) : Measurable (fun ω : TwoMarkedCloudSpace q A B ↦
      (PartialMatching.legalMaximumCard
        (spatialLegalMarkedGraph q mn.1 mn.2 cell source target b ω) : ℝ)) :=
    measurable_legalMaximumCard_cast _
      (measurableSet_spatialLegalMarkedGraph_eq q mn.1 mn.2 hc hs ht b)
  have hprod : Measurable (fun p : (ℕ × ℕ) × TwoMarkedCloudSpace q A B ↦
      (PartialMatching.legalMaximumCard
        (spatialLegalMarkedGraph q p.1.1 p.1.2 cell source target b p.2) : ℝ)) :=
    measurable_from_prod_countable_right hfixed
  have h := hprod.comp (((measurable_mSourceCount q).prodMk
    (measurable_mTargetCount q)).prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using h

/-- The sum of actual child legal source deficiencies on the original cloud. -/
def spatialLegalMarkedSourceDefectSum (q : ℕ) {β : Type*} [Fintype β] [DecidableEq β]
    (cell : (Fin q → ℝ) → β) (source : A → ℝ) (target : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  (mSourceCount ω : ℝ) - ∑ b : β, (PartialMatching.legalMaximumCard
    (spatialLegalMarkedGraph q (mSourceCount ω) (mTargetCount ω) cell source target b ω) : ℝ)

theorem measurable_spatialLegalMarkedSourceDefectSum (q : ℕ)
    {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {cell : (Fin q → ℝ) → β} {source : A → ℝ} {target : B → ℝ}
    (hc : Measurable cell) (hs : Measurable source) (ht : Measurable target) :
    Measurable (spatialLegalMarkedSourceDefectSum (A := A) (B := B) q cell source target) :=
  (measurable_from_nat.comp (measurable_mSourceCount q)).sub
    (Finset.measurable_sum _ (fun b _ ↦ measurable_spatialLegalMarkedCard_cast q hc hs ht b))

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The pressure-hierarchy natural deficiencies have this exact real sum. -/
theorem spatialLegalMarkedSourceDefectSum_eq_nat (q : ℕ)
    {β : Type*} [Fintype β] [DecidableEq β]
    (cell : (Fin q → ℝ) → β) (source : A → ℝ) (target : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    spatialLegalMarkedSourceDefectSum q cell source target ω =
      ∑ b : β, (((OTSelector.blockFinset
        (fun i : Fin (mSourceCount ω) ↦ cell (mSourcePoint ω i)) b).card -
        PartialMatching.legalMaximumCard (spatialLegalMarkedGraph q (mSourceCount ω)
          (mTargetCount ω) cell source target b ω) : ℕ) : ℝ) := by
  symm
  calc
    _ = ∑ b : β, (((OTSelector.blockFinset
        (fun i : Fin (mSourceCount ω) ↦ cell (mSourcePoint ω i)) b).card : ℝ) -
        (PartialMatching.legalMaximumCard (spatialLegalMarkedGraph q (mSourceCount ω)
          (mTargetCount ω) cell source target b ω) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Nat.cast_sub (PartialMatching.spatialLegalBlock_source_card_le _ _ _ b)
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Nat.cast_sum, OTSelector.sum_card_blockFinset]
      rfl

/-- The total original child deficiency is integrable for every finite
measurable spatial partition, with no equal-volume or balance input. -/
theorem integrable_spatialLegalMarkedSourceDefectSum (q : ℕ)
    {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {cell : (Fin q → ℝ) → β} {source : A → ℝ} {target : B → ℝ}
    (hc : Measurable cell) (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (βlaw : Measure B) [IsProbabilityMeasure βlaw]
    (r : ℝ≥0) :
    Integrable (spatialLegalMarkedSourceDefectSum q cell source target)
      (twoMarkedCloudLaw q A B α βlaw r) := by
  have hmeas := measurable_spatialLegalMarkedSourceDefectSum (A := A) (B := B) q hc hs ht
  refine (integrable_mSourceCount q α βlaw r).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  have hnonneg : 0 ≤ spatialLegalMarkedSourceDefectSum q cell source target ω := by
    rw [spatialLegalMarkedSourceDefectSum_eq_nat]
    exact Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, spatialLegalMarkedSourceDefectSum]
  exact sub_le_self _ (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))

end OTSelector.Reconstruction
