import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergy
import OTSelector.Reconstruction.HierarchicalIIDAssignment

/-!
# Expected repair budget for an adaptively retained core

Only the original point arrays have iid laws. The core is an arbitrary
measurable function of those arrays. Its actual unused cardinality and crossing
flux remain in the bound; no distribution is assigned to selected orphans.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- A concrete nonnegative majorant for the cost of completing a retained
core. Its histogram terms use all original sample indices. -/
def adaptiveOrphanRepairBudget {X : Type*} {K N : ℕ} {C : Fin K → Type*}
    [∀ k, Fintype (C k)] (σ : OTSelector.PartialMatching N N)
    (cell : (k : Fin K) → X → C k) (x y : Fin N → X)
    (base : ℝ) (weight : Fin K → ℝ) : ℝ :=
  ((N : ℝ) - σ.card) * base + (1 / 2 : ℝ) * ∑ k, weight k *
    ((∑ c, |partitionCount (cell k ∘ x) c - partitionCount (cell k ∘ y) c|) +
      2 * retainedPartitionCrossings σ (cell k ∘ x) (cell k ∘ y))

/-- The explicit budget bounds the added cost of an actual full completion. -/
theorem exists_completion_le_adaptiveOrphanRepairBudget
    {X : Type*} {K N : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (σ : OTSelector.PartialMatching N N) (cell : (k : Fin K) → X → C k)
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ x y : X,
      cell l x = cell l y → cell k x = cell k y)
    (x y : Fin N → X) (cost : Fin N → Fin N → ℝ)
    (base : ℝ) (hb : 0 ≤ base) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hcost : ∀ i j, cost i j ≤
      base + ∑ k, weight k * partitionDistance (cell k (x i)) (cell k (y j))) :
    ∃ τ : OTSelector.PartialMatching N N,
      τ.card = N ∧ σ.edges ⊆ τ.edges ∧
      (∑ e ∈ τ.edges \ σ.edges, cost e.1 e.2) ≤
        adaptiveOrphanRepairBudget σ cell x y base weight := by
  obtain ⟨τ, hτ, hsub, hcost⟩ := exists_completion_hierarchy_original_flux_bound
    σ cell hnested x y cost base hb weight hw hcost
  refine ⟨τ, by simpa using hτ, hsub, ?_⟩
  simpa [adaptiveOrphanRepairBudget] using hcost

/-- The cardinality of a random finite core is measurable whenever all of its
edge inclusion events are measurable. -/
theorem measurable_retained_card {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (σ : Ω → OTSelector.PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges}) :
    Measurable (fun ω ↦ ((σ ω).card : ℝ)) := by
  classical
  have heq : (fun ω ↦ ((σ ω).card : ℝ)) = fun ω ↦
      ∑ e : Fin m × Fin n, if e ∈ (σ ω).edges then (1 : ℝ) else 0 := by
    funext ω
    have hf : (Finset.univ.filter fun e : Fin m × Fin n ↦
        e ∈ (σ ω).edges) = (σ ω).edges := by ext e; simp
    rw [← Finset.sum_filter, hf]
    simp [OTSelector.PartialMatching.card]
  rw [heq]
  exact Finset.measurable_sum _ fun e _ ↦
    Measurable.ite (hσ e) measurable_const measurable_const

/-- Actual retained crossing counts are measurable and integrable, including
when the core was selected using all of the samples. -/
theorem integrable_retainedPartitionCrossings
    {Ω X C : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype C]
    {N : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (σ : Ω → OTSelector.PartialMatching N N)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs ys : Fin N → Ω → X) (hx : ∀ i, Measurable (xs i))
    (hy : ∀ i, Measurable (ys i)) (cell : X → C)
    (hm : ∀ c, MeasurableSet {x | cell x = c}) :
    Integrable (fun ω ↦ retainedPartitionCrossings (σ ω)
      (fun i ↦ cell (xs i ω)) (fun j ↦ cell (ys j ω))) P := by
  classical
  have hne (i j : Fin N) : MeasurableSet {ω | cell (xs i ω) ≠ cell (ys j ω)} := by
    have heq : {ω | cell (xs i ω) = cell (ys j ω)} =
        ⋃ c : C, ({ω | cell (xs i ω) = c} ∩ {ω | cell (ys j ω) = c}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun h ↦ ⟨_, rfl, h.symm⟩, fun ⟨c, hc, hc'⟩ ↦ hc.trans hc'.symm⟩
    rw [show {ω | cell (xs i ω) ≠ cell (ys j ω)} =
      {ω | cell (xs i ω) = cell (ys j ω)}ᶜ by rfl, heq]
    exact (MeasurableSet.iUnion fun c ↦ ((hm c).preimage (hx i)).inter
      ((hm c).preimage (hy j))).compl
  have heq (ω : Ω) : retainedPartitionCrossings (σ ω)
      (fun i ↦ cell (xs i ω)) (fun j ↦ cell (ys j ω)) =
      ∑ e : Fin N × Fin N,
        if e ∈ (σ ω).edges ∧ cell (xs e.1 ω) ≠ cell (ys e.2 ω) then (1 : ℝ) else 0 := by
    unfold retainedPartitionCrossings
    have hf : (Finset.univ.filter fun e : Fin N × Fin N ↦
        e ∈ (σ ω).edges ∧ cell (xs e.1 ω) ≠ cell (ys e.2 ω)) =
        (σ ω).edges.filter (fun e ↦ cell (xs e.1 ω) ≠ cell (ys e.2 ω)) := by
      ext e; simp
    rw [← Finset.sum_filter, hf]
    simp
  simp_rw [heq]
  apply integrable_finsetSum
  intro e he
  have hm : Measurable (fun ω ↦ if e ∈ (σ ω).edges ∧
      cell (xs e.1 ω) ≠ cell (ys e.2 ω) then (1 : ℝ) else 0) :=
    Measurable.ite ((hσ e).inter (hne e.1 e.2)) measurable_const measurable_const
  refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
  filter_upwards with ω
  split_ifs <;> norm_num

/-- An explicit expectation bound for the actual completion budget. All iid
hypotheses concern the original arrays. The two adaptive quantities on the
right are the actual number of unused rows and retained crossing flux. -/
theorem integral_adaptiveOrphanRepairBudget_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {K N : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    (σ : Ω → OTSelector.PartialMatching N N)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs ys : Fin N → Ω → X) (hx : ∀ i, Measurable (xs i))
    (hy : ∀ i, Measurable (ys i)) (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P)
    (cell : (k : Fin K) → X → C k) (hm : ∀ k c, MeasurableSet {x | cell k x = c})
    (base : ℝ) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k) :
    Integrable (fun ω ↦ adaptiveOrphanRepairBudget (σ ω) cell
      (fun i ↦ xs i ω) (fun j ↦ ys j ω) base weight) P ∧
    (∫ ω, adaptiveOrphanRepairBudget (σ ω) cell
      (fun i ↦ xs i ω) (fun j ↦ ys j ω) base weight ∂P) ≤
      (∫ ω, (N : ℝ) - (σ ω).card ∂P) * base + (1 / 2 : ℝ) *
        ∑ k, weight k * (Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) +
          2 * ∫ ω, retainedPartitionCrossings (σ ω)
            (fun i ↦ cell k (xs i ω)) (fun j ↦ cell k (ys j ω)) ∂P) := by
  classical
  have hcard : Integrable (fun ω ↦ ((σ ω).card : ℝ)) P := by
    apply Integrable.of_bound (measurable_retained_card σ hσ).aestronglyMeasurable N
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast ((σ ω).card_le.trans (min_le_left N N))
  have hfree := (integrable_const (N : ℝ)).sub hcard
  have hd (k : Fin K) := iid_partition_discrepancy_bound P μ xs ys hx hy hxi hyi hxl hyl
    hxy (cell k) (hm k)
  have hc (k : Fin K) := integrable_retainedPartitionCrossings P σ hσ xs ys hx hy
    (cell k) (hm k)
  have hterm (k : Fin K) := ((hd k).1.add ((hc k).const_mul 2)).const_mul (weight k)
  have hi := (hfree.mul_const base).add
    ((integrable_finsetSum Finset.univ fun k _ ↦ hterm k).const_mul (1 / 2 : ℝ))
  refine ⟨hi, ?_⟩
  change (∫ ω, ((N : ℝ) - (σ ω).card) * base + (1 / 2 : ℝ) *
    ∑ k, weight k * ((∑ c, |partitionCount (fun i ↦ cell k (xs i ω)) c -
      partitionCount (fun j ↦ cell k (ys j ω)) c|) +
        2 * retainedPartitionCrossings (σ ω) (fun i ↦ cell k (xs i ω))
          (fun j ↦ cell k (ys j ω))) ∂P) ≤ _
  have hsplit := integral_add (hfree.mul_const base)
    ((integrable_finsetSum Finset.univ fun k _ ↦ hterm k).const_mul (1 / 2 : ℝ))
  simp only [Pi.add_apply, Pi.sub_apply] at hsplit
  have hsum := integral_finsetSum Finset.univ (fun k _ ↦ hterm k)
  simp only [Pi.add_apply] at hsum
  rw [hsplit, integral_mul_const, integral_const_mul, hsum]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro k hk
  rw [integral_const_mul]
  have hsplitk := integral_add (hd k).1 ((hc k).const_mul 2)
  rw [hsplitk, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add_left (hd k).2 _) (hw k)

end OTSelector.Reconstruction
