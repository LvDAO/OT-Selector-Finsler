import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCounting

/-!
# Measurable simple integer carriers for the original legal scene

The same integer input measure is simple precisely when every singleton has
mass at most one. Shell multisets make this predicate Borel. This permits the
exact original finite Poisson window law to transfer simplicity to the same
joint weak scene, without adding a new configuration or sampling law.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

local instance markedStationaryValueLegalInputSimpleCarrierConfigurationTopology (base : X) :
    TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance markedStationaryValueLegalInputSimpleCarrierConfigurationBorel (base : X) :
    BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace

/-- The actual measure is an integer configuration with unit occupied atoms. -/
def IsLegalSimpleCountingMeasure (base : X) (μ : LocalFiniteMeasure X) : Prop :=
  ∃ c : LocalConfiguration base, LocalConfiguration.toLocalFiniteMeasure c = μ ∧
    ∀ x, LocalConfiguration.multiplicity c x ≤ 1

/-- Integer counting and unit atom bounds characterize the simple carrier. -/
theorem isLegalSimpleCountingMeasure_iff (base : X) (μ : LocalFiniteMeasure X) :
    IsLegalSimpleCountingMeasure base μ ↔
      IsLegalCountingMeasure base μ ∧ ∀ x, (μ : Measure X) {x} ≤ 1 := by
  constructor
  · rintro ⟨c, rfl, hc⟩
    refine ⟨⟨c, rfl⟩, fun x ↦ ?_⟩
    change LocalConfiguration.countingMeasure c {x} ≤ 1
    rw [LocalConfiguration.countingMeasure_singleton]
    exact_mod_cast hc x
  · rintro ⟨⟨c, rfl⟩, hc⟩
    refine ⟨c, rfl, fun x ↦ ?_⟩
    have hx := hc x
    change LocalConfiguration.countingMeasure c {x} ≤ 1 at hx
    rw [LocalConfiguration.countingMeasure_singleton] at hx
    exact_mod_cast hx

private theorem measurableSet_legalMultiset_nodup {Y : Type*}
    [MeasurableSpace Y] [StandardBorelSpace Y] :
    MeasurableSet {m : Multiset Y | m.Nodup} := by
  have he (m : Multiset Y) : m.Nodup ↔ ∀ i j : ℕ, i < j → j < m.card →
      (MultisetEncoding.paddedCode m).2 i ≠ (MultisetEncoding.paddedCode m).2 j := by
    rw [← Multiset.sort_eq m (MultisetEncoding.codingLE Y), Multiset.coe_nodup,
      List.nodup_iff_getElem?_ne_getElem?]
    simp only [MultisetEncoding.paddedCode, Multiset.length_sort, Multiset.sort_eq]
  simp_rw [he]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (measurableSet_lt measurable_const MultisetEncoding.measurable_card).imp
    (measurableSet_eq_fun
      ((measurable_pi_apply i).comp MultisetEncoding.measurable_paddedCode.snd)
      ((measurable_pi_apply j).comp MultisetEncoding.measurable_paddedCode.snd)).compl

/-- Simplicity of the original integer measure is a Borel event, including on
infinite configurations. The finite shell code supplies its measurability. -/
theorem measurableSet_isLegalSimpleCountingMeasure [StandardBorelSpace X] (base : X) :
    MeasurableSet {μ : LocalFiniteMeasure X | IsLegalSimpleCountingMeasure base μ} := by
  have he (c : LocalConfiguration base) :
      (∀ x, LocalConfiguration.multiplicity c x ≤ 1) ↔ ∀ n, (c n).Nodup := by
    classical
    constructor
    · intro h n
      apply Multiset.nodup_iff_count_le_one.mpr
      intro x
      simpa only [LocalConfiguration.multiplicity_shell] using h x.val
    · intro h x
      exact Multiset.nodup_iff_count_le_one.mp
        (h (LocalConfiguration.shellIndex base x)) ⟨x, rfl⟩
  have hE : MeasurableSet {c : LocalConfiguration base | ∀ x, LocalConfiguration.multiplicity c x ≤ 1} := by
    simp_rw [he]
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n ↦
      (LocalConfiguration.measurable_shell n) measurableSet_legalMultiset_nodup
  have hem : MeasurableEmbedding (LocalConfiguration.toLocalFiniteMeasure (base := base)) :=
    LocalConfiguration.isClosedEmbedding_toLocalFiniteMeasure.measurableEmbedding
  have himage := hem.measurableSet_image.mpr hE
  convert himage using 1
  ext μ
  simp only [IsLegalSimpleCountingMeasure, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨c, hc, hs⟩
    exact ⟨c, hs, hc⟩
  · rintro ⟨c, hs, hc⟩
    exact ⟨c, hc, hs⟩

/-- An injective finite original point enumeration has exactly unit atoms. -/
theorem isLegalSimpleCountingMeasure_of_injective_tuple {n : ℕ}
    (base : X) (f : Fin n → X) (hf : Injective f) :
    IsLegalSimpleCountingMeasure base
      ⟨∑ i, Measure.dirac (f i), inferInstance⟩ := by
  classical
  let c := LocalConfiguration.ofTuple base f
  have heq : LocalConfiguration.toLocalFiniteMeasure c =
      (⟨∑ i, Measure.dirac (f i), inferInstance⟩ : LocalFiniteMeasure X) := by
    apply Subtype.ext
    exact LocalConfiguration.countingMeasure_ofTuple f
  apply (isLegalSimpleCountingMeasure_iff base _).mpr
  refine ⟨⟨c, heq⟩, fun x ↦ ?_⟩
  by_cases hx : ∃ i, f i = x
  · obtain ⟨i, rfl⟩ := hx
    simp [Measure.finsetSum_apply, Measure.dirac_apply', Pi.single_apply, hf.eq_iff]
  · have hx' : ∀ i, f i ≠ x := by simpa using hx
    simp [Measure.finsetSum_apply, Measure.dirac_apply', hx']

private theorem legal_filter_sum_dirac_restrict {Y : Type*} (m : Multiset Y)
    (f : Y → X) (U : Set X) :
    (((m.filter (fun y ↦ f y ∈ U)).map (fun y ↦ Measure.dirac (f y))).sum) =
      ((m.map (fun y ↦ Measure.dirac (f y))).sum).restrict U := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons y m ih =>
      by_cases hy : f y ∈ U
      · simp [hy, Measure.restrict_add, restrict_dirac, ih]
      · simp [hy, Measure.restrict_add, restrict_dirac, ih]

/-- Restriction retains precisely the original occupied atoms and their
integer multiplicities, including for an arbitrary measurable window. -/
theorem isLegalCountingMeasure_restrict (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (U : Set X) :
    IsLegalCountingMeasure base ⟨(μ : Measure X).restrict U, inferInstance⟩ := by
  classical
  obtain ⟨c, rfl⟩ := hμ
  let d : LocalConfiguration base := fun n ↦ (c n).filter (fun x ↦ x.val ∈ U)
  refine ⟨d, ?_⟩
  apply Subtype.ext
  change LocalConfiguration.countingMeasure d = (LocalConfiguration.countingMeasure c).restrict U
  simp only [LocalConfiguration.countingMeasure]
  rw [Measure.restrict_sum_of_countable]
  congr 1
  funext n
  exact legal_filter_sum_dirac_restrict (c n) Subtype.val U

/-- No restriction duplicates an original unit atom. -/
theorem isLegalSimpleCountingMeasure_restrict (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalSimpleCountingMeasure base μ) (U : Set X) :
    IsLegalSimpleCountingMeasure base ⟨(μ : Measure X).restrict U, inferInstance⟩ := by
  obtain ⟨hc, hs⟩ := (isLegalSimpleCountingMeasure_iff base μ).mp hμ
  apply (isLegalSimpleCountingMeasure_iff base _).mpr
  refine ⟨isLegalCountingMeasure_restrict base μ hc U, fun x ↦ ?_⟩
  exact (Measure.restrict_le_self (μ := (μ : Measure X)) (s := U) {x}).trans (hs x)

end OTSelector.Reconstruction
