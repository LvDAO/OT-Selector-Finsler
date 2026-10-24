import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellwiseAssignment
import OTSelector.Reconstruction.FinslerPopulationMarkedAssignmentTransfer

/-! Integrability and exact original-iid transfer for the full physical value.
Finite retained edge events suffice; no measurable full-completion choice is
needed when integrating the actual attained original assignment minimum. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace OTSelector.PartialMatching

/-- A varying finite matching cost is a fixed finite sum of its edge events. -/
theorem cost_eq_sum_edgeIndicator {m n : ℕ} (σ : PartialMatching m n)
    (c : Fin m → Fin n → ℝ) :
    σ.cost c = ∑ e : Fin m × Fin n, if e ∈ σ.edges then c e.1 e.2 else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp [cost]

/-- Actual measurable retained edge events and integrable original edge costs
produce an integrable matching cost, including adaptively selected matchings. -/
theorem integrable_sample_cost_of_edge_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (σ : Ω → PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (c : Ω → Fin m → Fin n → ℝ)
    (hci : ∀ i j, Integrable (fun ω ↦ c ω i j) P) :
    Integrable (fun ω ↦ (σ ω).cost (c ω)) P := by
  classical
  have heq : (fun ω ↦ (σ ω).cost (c ω)) = fun ω ↦
      ∑ e : Fin m × Fin n, if e ∈ (σ ω).edges then c ω e.1 e.2 else 0 := by
    funext ω
    exact cost_eq_sum_edgeIndicator _ _
  rw [heq]
  apply integrable_finsetSum
  intro e he
  have heq : (fun ω ↦ if e ∈ (σ ω).edges then c ω e.1 e.2 else 0) =
      {ω | e ∈ (σ ω).edges}.indicator (fun ω ↦ c ω e.1 e.2) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  exact (hci e.1 e.2).indicator (hσ e)

/-- The cardinality of the same actual matching is integrable on a finite law. -/
theorem integrable_sample_card_of_edge_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {m n : ℕ}
    (σ : Ω → PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges}) :
    Integrable (fun ω ↦ ((σ ω).card : ℝ)) P := by
  have heq : (fun ω ↦ ((σ ω).card : ℝ)) = fun ω ↦ (σ ω).cost (fun _ _ ↦ 1) := by
    funext ω
    simp [cost, card]
  rw [heq]
  exact integrable_sample_cost_of_edge_events P σ hσ _ (fun _ _ ↦ integrable_const _)

end OTSelector.PartialMatching

namespace OTSelector.Reconstruction

/-- Original finite cell counts are integrable once their actual cell events
are measurable. The assertion applies before any matching selects endpoints. -/
theorem integrable_partitionCount_of_cell_events
    {Ω C : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {n : ℕ}
    (cell : Ω → Fin n → C) (c : C)
    (hc : ∀ i, MeasurableSet {ω | cell ω i = c}) :
    Integrable (fun ω ↦ partitionCount (cell ω) c) P := by
  classical
  unfold partitionCount partitionIndicator
  apply integrable_finsetSum
  intro i hi
  have heq : (fun ω ↦ if cell ω i = c then (1 : ℝ) else 0) =
      {ω | cell ω i = c}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  exact (integrable_const (1 : ℝ)).indicator (hc i)

/-- A literal original retained-cell event is measurable using the physical
label and the finite original residual mark. -/
theorem measurableSet_originalRetainedCellTag_eq_some
    {Ω X Z C T : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T] [DecidableEq T]
    (a : X → Z) (ha : Measurable a) (cell : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c)) (hdisj : Pairwise (Disjoint on cell))
    (selected : Finset T) (p : Ω → X × T) (hp : Measurable p) (c : C) :
    MeasurableSet {ω | originalRetainedCellTag a cell selected (p ω) = some c} := by
  have heq : {ω | originalRetainedCellTag a cell selected (p ω) = some c} =
      {ω | (p ω).2 ∉ selected} ∩ {ω | a (p ω).1 ∈ cell c} := by
    ext ω
    exact originalRetainedCellTag_eq_some_iff a cell hdisj selected (p ω) c
  rw [heq]
  exact ((selected.measurableSet.compl).preimage (measurable_snd.comp hp)).inter
    ((ha (hcell c)).preimage (measurable_fst.comp hp))

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))]

/-- Original compact cost and bounded probe produce every edge's integrability
on the same actual residual-marked experiment. -/
theorem original_marked_tilted_edge_integrable
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π)
    (n : ℕ) (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {G : ℝ} (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G) (tilt : ℝ) :
    let R := D.refineSubplan ξ hξ
    ∀ i j : Fin n, Integrable (fun sample ↦
      (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
        tilt * probe (sample.1 i).1 (sample.2 j).1) (R.markedLaw n) := by
  let R := D.refineSubplan ξ hξ
  let _instP : IsProbabilityMeasure (R.markedLaw n) := (R.iid_facts hπ n).1
  have hb := R.iid_cost_bounds hπ n
  have hgRaw : ∀ᵐ sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)), ∀ i j, |probe (sample.1 i) (sample.2 j)| ≤ G := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) i)
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) j)).ae hg
  have hgMarked := R.types.iid_original_physical_property hπ _ hgRaw
  dsimp only
  intro i j
  have hc : Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        cost (sample.1 i).1 (sample.2 j).1) :=
    D.measurable_cost.comp (show Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        ((sample.1 i).1, (sample.2 j).1)) from by fun_prop)
  have hp : Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        probe (sample.1 i).1 (sample.2 j).1) := hprobe.comp (show Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        ((sample.1 i).1, (sample.2 j).1)) from by fun_prop)
  have hci : Integrable (fun sample ↦ cost (sample.1 i).1 (sample.2 j).1) (R.markedLaw n) := by
    apply Integrable.of_bound hc.aestronglyMeasurable D.globalBound
    filter_upwards [hb.1, hb.2] with sample hlo hhi
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hlo i j)] using (show cost (sample.1 i).1 (sample.2 j).1 ≤ D.globalBound from hhi i j)
  have hpi : Integrable (fun sample ↦ probe (sample.1 i).1 (sample.2 j).1) (R.markedLaw n) := by
    apply Integrable.of_bound hp.aestronglyMeasurable G
    exact hgMarked.mono fun sample hs ↦ by simpa only [Real.norm_eq_abs] using hs i j
  exact (hci.const_mul _).add (hpi.const_mul tilt)

/-- The original physical minimum is integrable, and forgetting the same RN
marks preserves its exact expectation. No optimizer-selection premise occurs. -/
theorem original_tilted_assignment_integral
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π)
    (n : ℕ) (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {G : ℝ} (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G) (tilt : ℝ) :
    let R := D.refineSubplan ξ hξ
    let value := fun sample : (Fin n → X) × (Fin n → Y) ↦ perturbedAssignmentValue
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * probe (sample.1 i) (sample.2 j)) 0 0
    let markedValue := fun sample :
        (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
      value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1))
    Integrable value ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ∧
      Integrable markedValue (R.markedLaw n) ∧
      (∫ sample, markedValue sample ∂R.markedLaw n) =
        ∫ sample, value sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
          (Measure.pi (fun _ : Fin n ↦ ν)) := by
  let R := D.refineSubplan ξ hξ
  have hm (i j : Fin n) : Measurable (fun sample : (Fin n → X) × (Fin n → Y) ↦
      (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * probe (sample.1 i) (sample.2 j)) :=
    ((D.measurable_cost.comp (show Measurable (fun sample : (Fin n → X) × (Fin n → Y) ↦
      (sample.1 i, sample.2 j)) from by fun_prop)).const_mul _).add
      ((hprobe.comp (show Measurable (fun sample : (Fin n → X) × (Fin n → Y) ↦
        (sample.1 i, sample.2 j)) from by fun_prop)).const_mul tilt)
  have hmarked := Probability.integrable_assignmentValue (R.markedLaw n) _
    (fun i j ↦ (hm i j).comp (show Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1))) from by fun_prop))
    (D.original_marked_tilted_edge_integrable hπ ξ hξ n probe hprobe hg tilt)
  have htransfer := R.types.iid_physical_integral hπ _
    (Probability.measurable_assignmentValue _ hm)
  exact ⟨htransfer.1.mpr hmarked, hmarked, htransfer.2⟩

end PopulationTypedCostData
end OTSelector.Reconstruction
