import OTSelector.Reconstruction.FinslerRelativeLawOriginalAssignmentExpectation
import OTSelector.Finite.MeasurableLegalOptimizer

/-! Actual retained-cell legal optimizers on the unchanged original indices.
Filtering by the literal retained flags and original physical cells supplies
both insertion support and measurable edge events automatically. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The actual original-index legal graph in one retained cell. The extra graph
is the prescribed frozen class legality, read from those same observations. -/
def originalRetainedCellGraph {X Z C T : Type*} {n : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n)) (c : C)
    (sample : (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) :
    Finset (Fin n × Fin n) := by
  classical
  exact (extra c sample).filter (fun e ↦
    subplanRetentionFlag (sample.1 e.1).2 = false ∧
    subplanRetentionFlag (sample.2 e.2).2 = false ∧
    a (sample.1 e.1).1 ∈ cell c ∧ a (sample.2 e.2).1 ∈ cell c)

/-- The first exact legal optimum uses the unchanged original sample indices. -/
def originalRetainedCellOptimizer {X Z C T : Type*} {n : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (model : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ) (c : C)
    (sample : (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) :
    OTSelector.PartialMatching n n :=
  PartialMatching.firstLegalOptimalMatching (originalRetainedCellGraph a cell extra c sample)
    (model c sample)

/-- The canonical original-index cell optimizer has the actual legal maximum
cardinality and the literal frozen model value, including isolated vertices. -/
theorem originalRetainedCellOptimizer_isLegalOptimal {X Z C T : Type*} {n : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (model : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ) (c : C)
    (sample : (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) :
    PartialMatching.IsLegalOptimal (originalRetainedCellGraph a cell extra c sample)
      (model c sample) (originalRetainedCellOptimizer a cell extra model c sample) :=
  PartialMatching.firstLegalOptimalMatching_isLegalOptimal _ _

/-- Every actual optimizer edge has its original false flags and physical-cell
membership. It can therefore be inserted in the same residual experiment. -/
theorem originalRetainedCellOptimizer_support {X Z C T : Type*} {n : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (model : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ) (c : C)
    (sample : (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)))
    (e : Fin n × Fin n) (he : e ∈ (originalRetainedCellOptimizer a cell extra model c sample).edges) :
    e ∈ extra c sample ∧ subplanRetentionFlag (sample.1 e.1).2 = false ∧
      subplanRetentionFlag (sample.2 e.2).2 = false ∧
      a (sample.1 e.1).1 ∈ cell c ∧ a (sample.2 e.2).1 ∈ cell c := by
  have h := (PartialMatching.firstLegalOptimalMatching_isLegalOptimal
    (originalRetainedCellGraph a cell extra c sample) (model c sample)).1 he
  exact Finset.mem_filter.mp h

/-- The actual cell graph is measurable directly from original observations
and the supplied finite class graph events. -/
theorem measurableSet_originalRetainedCellGraph_eq
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))] {n : ℕ}
    (a : X → Z) (ha : Measurable a) (cell : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c))
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (hextra : ∀ c S, MeasurableSet {sample | extra c sample = S})
    (c : C) (S : Finset (Fin n × Fin n)) :
    MeasurableSet {sample | originalRetainedCellGraph a cell extra c sample = S} := by
  classical
  have hex (e : Fin n × Fin n) : MeasurableSet {sample | e ∈ extra c sample} := by
    have hm : Measurable (extra c) := by
      apply measurable_to_countable'
      intro S
      exact hextra c S
    exact (measurableSet_mem_finset e).preimage hm
  have hflags (e : Fin n × Fin n) : MeasurableSet {sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) |
      subplanRetentionFlag (sample.1 e.1).2 = false ∧
        subplanRetentionFlag (sample.2 e.2).2 = false} := by
    have hs : Measurable (fun sample :
        (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
        (sample.1 e.1).2) := by fun_prop
    have ht : Measurable (fun sample :
        (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
        (sample.2 e.2).2) := by fun_prop
    exact (measurableSet_eq_fun ((measurable_of_countable subplanRetentionFlag).comp hs)
      measurable_const).inter
      (measurableSet_eq_fun ((measurable_of_countable subplanRetentionFlag).comp ht) measurable_const)
  have hroots (e : Fin n × Fin n) : MeasurableSet {sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) |
      a (sample.1 e.1).1 ∈ cell c ∧ a (sample.2 e.2).1 ∈ cell c} := by
    exact ((ha (hcell c)).preimage (show Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
        (sample.1 e.1).1) from by fun_prop)).inter
      ((ha (hcell c)).preimage (show Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
        (sample.2 e.2).1) from by fun_prop))
  have hmem (e : Fin n × Fin n) :
      MeasurableSet {sample | e ∈ originalRetainedCellGraph a cell extra c sample} := by
    have heq : {sample | e ∈ originalRetainedCellGraph a cell extra c sample} =
        {sample | e ∈ extra c sample} ∩ ({sample |
          subplanRetentionFlag (sample.1 e.1).2 = false ∧
          subplanRetentionFlag (sample.2 e.2).2 = false} ∩ {sample |
            a (sample.1 e.1).1 ∈ cell c ∧ a (sample.2 e.2).1 ∈ cell c}) := by
      ext sample
      simp only [originalRetainedCellGraph, Finset.mem_filter, Set.mem_inter_iff,
        Set.mem_ofPred_eq, and_assoc]
    rw [heq]
    exact (hex e).inter ((hflags e).inter (hroots e))
  have hm : Measurable (originalRetainedCellGraph a cell extra c) := by
    apply measurable_finset_iff.mpr
    intro e
    exact measurableSet_setOfPred.mp (hmem e)
  exact (measurableSet_singleton S).preimage hm

/-- Every original retained optimizer edge event is measurable. This removes
the measurable selected-matching premise of the global expectation theorem. -/
theorem measurableSet_mem_originalRetainedCellOptimizer
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))] {n : ℕ}
    (a : X → Z) (ha : Measurable a) (cell : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c))
    (extra : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Finset (Fin n × Fin n))
    (hextra : ∀ c S, MeasurableSet {sample | extra c sample = S})
    (model : C → ((Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T))) →
      Fin n → Fin n → ℝ)
    (hmodel : ∀ c i j, Measurable (fun sample ↦ model c sample i j))
    (c : C) (e : Fin n × Fin n) :
    MeasurableSet {sample | e ∈ (originalRetainedCellOptimizer a cell extra model c sample).edges} :=
  PartialMatching.measurableSet_mem_firstLegalOptimalMatching _
    (measurableSet_originalRetainedCellGraph_eq a ha cell hcell extra hextra c) _ (hmodel c) e

end OTSelector.Reconstruction
