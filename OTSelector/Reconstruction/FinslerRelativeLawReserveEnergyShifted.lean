import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyExpectation

/-!
Actual independent-phase averaging of original iid histograms and adaptive
retained crossing flux. Only original samples carry iid hypotheses.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

private theorem partitionCount_nonneg_le {N : ℕ} {C : Type*}
    (a : Fin N → C) (c : C) : 0 ≤ partitionCount a c ∧ partitionCount a c ≤ N := by
  classical
  unfold partitionCount partitionIndicator
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ by split_ifs <;> norm_num
  · calc
      _ ≤ ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ by split_ifs <;> norm_num
      _ = _ := by simp

/-- A finite histogram of two actual measurable arrays is jointly integrable
under every finite law, independently of how its labels were chosen. -/
theorem integrable_measurable_partition_discrepancy
    {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [Fintype C] [MeasurableSingletonClass C] {N : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (a b : Fin N → Ω → C)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) :
    Integrable (fun ω ↦ ∑ c, |partitionCount (fun i ↦ a i ω) c -
      partitionCount (fun i ↦ b i ω) c|) P := by
  classical
  have hcount (z : Fin N → Ω → C) (hz : ∀ i, Measurable (z i)) (c : C) :
      Measurable (fun ω ↦ partitionCount (fun i ↦ z i ω) c) :=
    Finset.measurable_sum _ fun i _ ↦ Measurable.ite
      ((measurableSet_singleton c).preimage (hz i)) measurable_const measurable_const
  have hm : Measurable (fun ω ↦ ∑ c, |partitionCount (fun i ↦ a i ω) c -
      partitionCount (fun i ↦ b i ω) c|) :=
    Finset.measurable_sum _ fun c _ ↦ by
      simpa only [Function.comp_def, Pi.sub_apply, Real.norm_eq_abs] using measurable_norm.comp ((hcount a ha c).sub (hcount b hb c))
  refine Integrable.of_bound hm.aestronglyMeasurable ((Fintype.card C : ℝ) * (2 * N)) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun c _ ↦ abs_nonneg _)]
  calc
    _ ≤ ∑ _c : C, (2 * (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      have hA := partitionCount_nonneg_le (fun i ↦ a i ω) c
      have hB := partitionCount_nonneg_le (fun i ↦ b i ω) c
      rw [abs_le]
      constructor <;> linarith
    _ = _ := by simp [nsmul_eq_mul]

/-- Auxiliary independent phase randomness does not change the original iid
histogram estimate, for arbitrary common original population law. -/
theorem integral_parametric_original_partition_discrepancy_le
    {Ω Θ X C : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace X] [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q] (μ : Measure X) [IsProbabilityMeasure μ]
    (xs ys : Fin N → Ω → X) (hx : ∀ i, Measurable (xs i))
    (hy : ∀ i, Measurable (ys i)) (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P)
    (cell : Θ → X → C) (hcell : Measurable (fun p : Θ × X ↦ cell p.1 p.2)) :
    Integrable (fun p : Ω × Θ ↦ ∑ c,
      |partitionCount (fun i ↦ cell p.2 (xs i p.1)) c -
        partitionCount (fun i ↦ cell p.2 (ys i p.1)) c|) (P.prod Q) ∧
    (∫ p : Ω × Θ, ∑ c, |partitionCount (fun i ↦ cell p.2 (xs i p.1)) c -
      partitionCount (fun i ↦ cell p.2 (ys i p.1)) c| ∂(P.prod Q)) ≤
        Real.sqrt (2 * (N : ℝ) * Fintype.card C) := by
  have ha (i : Fin N) : Measurable (fun p : Ω × Θ ↦ cell p.2 (xs i p.1)) :=
    hcell.comp (measurable_snd.prodMk ((hx i).comp measurable_fst))
  have hb (i : Fin N) : Measurable (fun p : Ω × Θ ↦ cell p.2 (ys i p.1)) :=
    hcell.comp (measurable_snd.prodMk ((hy i).comp measurable_fst))
  have hi := integrable_measurable_partition_discrepancy (P.prod Q) _ _ ha hb
  refine ⟨hi, ?_⟩
  rw [integral_prod_symm _ hi]
  have hbound (θ : Θ) := (iid_partition_discrepancy_bound P μ xs ys hx hy hxi hyi hxl hyl
    hxy (cell θ) (fun c ↦ (measurableSet_singleton c).preimage
      (hcell.comp (measurable_const.prodMk measurable_id)))).2
  have hmono := integral_mono hi.integral_prod_right (integrable_const
    (Real.sqrt (2 * (N : ℝ) * Fintype.card C))) hbound
  simpa using hmono

/-- Measurability of grid labels when both the phase and point move. -/
theorem measurable_shiftedGridCells_comp {A : Type*} [MeasurableSpace A] {q : ℕ}
    (ell : ℝ) (u z : A → Fin q → ℝ) (hu : Measurable u) (hz : Measurable z) :
    Measurable (fun a ↦ shiftedGridCells ell (u a) (z a)) :=
  measurable_pi_lambda _ fun i ↦ Int.measurable_floor.comp
    (((measurable_pi_apply i).comp hz).sub
      ((measurable_pi_apply i).comp hu) |>.div_const ell)

/-- Arbitrary measurable retained cores have integrable crossing counts under
an actual finite joint law. This does not require any independence of the core. -/
theorem integrable_selected_partition_crossings
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableEq C] {m n : ℕ} (P : Measure A) [IsFiniteMeasure P]
    (σ : A → OTSelector.PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {a | e ∈ (σ a).edges})
    (s : Fin m → A → C) (t : Fin n → A → C)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ j, Measurable (t j)) :
    Integrable (fun a ↦ retainedPartitionCrossings (σ a)
      (fun i ↦ s i a) (fun j ↦ t j a)) P := by
  classical
  have heq (a : A) : retainedPartitionCrossings (σ a)
      (fun i ↦ s i a) (fun j ↦ t j a) =
      ∑ e : Fin m × Fin n, if e ∈ (σ a).edges ∧ s e.1 a ≠ t e.2 a then (1 : ℝ) else 0 := by
    unfold retainedPartitionCrossings
    have hf : (Finset.univ.filter fun e : Fin m × Fin n ↦
        e ∈ (σ a).edges ∧ s e.1 a ≠ t e.2 a) =
        (σ a).edges.filter (fun e ↦ s e.1 a ≠ t e.2 a) := by ext e; simp
    rw [← Finset.sum_filter, hf]
    simp
  simp_rw [heq]
  apply integrable_finsetSum
  intro e he
  have hm : Measurable (fun a ↦ if e ∈ (σ a).edges ∧ s e.1 a ≠ t e.2 a then (1 : ℝ)
      else 0) := Measurable.ite
    ((hσ e).inter (measurableSet_eq_fun (hs e.1) (ht e.2)).compl)
    measurable_const measurable_const
  refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
  filter_upwards with a
  split_ifs <;> norm_num

/-- The expected flux of a core selected from the original sample is bounded
by its actual displacement, after adjoining an independent actual grid phase. -/
theorem integral_selected_shifted_partition_crossings_le
    {Ω Θ C : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableEq C] {m n q : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Θ) [IsProbabilityMeasure Q]
    (σ : Ω → OTSelector.PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs : Fin m → Ω → Fin q → ℝ) (ys : Fin n → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    {ell : ℝ} (hell : 0 < ell) (phase : Θ → Fin q → ℝ) (hp : Measurable phase)
    (hlaw : Q.map phase = shiftedGridPhaseLaw q ell)
    (readout : (Fin q → ℤ) → C) (hr : Measurable readout)
    (hdisp : Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P) :
    Integrable (fun p : Ω × Θ ↦ retainedPartitionCrossings (σ p.1)
      (fun i ↦ readout (shiftedGridCells ell (phase p.2) (xs i p.1)))
      (fun j ↦ readout (shiftedGridCells ell (phase p.2) (ys j p.1)))) (P.prod Q) ∧
    (∫ p : Ω × Θ, retainedPartitionCrossings (σ p.1)
      (fun i ↦ readout (shiftedGridCells ell (phase p.2) (xs i p.1)))
      (fun j ↦ readout (shiftedGridCells ell (phase p.2) (ys j p.1))) ∂(P.prod Q)) ≤
      (∫ ω, retainedCoordinateDisplacement (σ ω)
        (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) / ell := by
  classical
  have ha (i : Fin m) : Measurable (fun p : Ω × Θ ↦
      readout (shiftedGridCells ell (phase p.2) (xs i p.1))) :=
    hr.comp (measurable_shiftedGridCells_comp ell _ _ (hp.comp measurable_snd)
      ((hx i).comp measurable_fst))
  have hb (j : Fin n) : Measurable (fun p : Ω × Θ ↦
      readout (shiftedGridCells ell (phase p.2) (ys j p.1))) :=
    hr.comp (measurable_shiftedGridCells_comp ell _ _ (hp.comp measurable_snd)
      ((hy j).comp measurable_fst))
  have hi := integrable_selected_partition_crossings (P.prod Q) (fun p ↦ σ p.1)
    (fun e ↦ (hσ e).preimage measurable_fst) _ _ ha hb
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  have hbound (ω : Ω) : (∫ θ, retainedPartitionCrossings (σ ω)
      (fun i ↦ readout (shiftedGridCells ell (phase θ) (xs i ω)))
      (fun j ↦ readout (shiftedGridCells ell (phase θ) (ys j ω))) ∂Q) ≤
        retainedCoordinateDisplacement (σ ω) (fun i ↦ xs i ω) (fun j ↦ ys j ω) / ell := by
    have hm : Measurable (fun u : Fin q → ℝ ↦ retainedPartitionCrossings (σ ω)
        (fun i ↦ readout (shiftedGridCells ell u (xs i ω)))
        (fun j ↦ readout (shiftedGridCells ell u (ys j ω)))) := by
      unfold retainedPartitionCrossings
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      apply Finset.measurable_sum
      intro e he
      exact Measurable.ite
        (measurableSet_eq_fun (hr.comp (measurable_shiftedGridCells ell (xs e.1 ω)))
          (hr.comp (measurable_shiftedGridCells ell (ys e.2 ω)))).compl
        measurable_const measurable_const
    have heq := integral_map (μ := Q) hp.aemeasurable hm.aestronglyMeasurable
    rw [hlaw] at heq
    rw [← heq]
    have hread (u : Fin q → ℝ) : retainedPartitionCrossings (σ ω)
        (fun i ↦ readout (shiftedGridCells ell u (xs i ω)))
        (fun j ↦ readout (shiftedGridCells ell u (ys j ω))) ≤
          retainedGridCrossings (σ ω) ell (fun i ↦ xs i ω) (fun j ↦ ys j ω) u := by
      unfold retainedPartitionCrossings retainedGridCrossings
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_le_sum
      intro e he
      by_cases h : shiftedGridCells ell u (xs e.1 ω) = shiftedGridCells ell u (ys e.2 ω)
      · simp [h]
      · simp only [ite_eq_left h]
        split_ifs <;> norm_num
    have : IsProbabilityMeasure (shiftedGridPhaseLaw q ell) :=
      shiftedGridPhaseLaw_probability q hell
    have hleft := integrable_selected_partition_crossings (shiftedGridPhaseLaw q ell)
      (fun _ ↦ σ ω) (fun e ↦ MeasurableSet.const (e ∈ (σ ω).edges)) _ _
      (fun i ↦ hr.comp (measurable_shiftedGridCells ell (xs i ω)))
      (fun j ↦ hr.comp (measurable_shiftedGridCells ell (ys j ω)))
    have hright : Integrable (retainedGridCrossings (σ ω) ell
        (fun i ↦ xs i ω) (fun j ↦ ys j ω)) (shiftedGridPhaseLaw q ell) := by
      apply Integrable.of_bound (measurable_retainedGridCrossings (σ ω) ell
        (fun i ↦ xs i ω) (fun j ↦ ys j ω)).aestronglyMeasurable ((σ ω).card : ℝ)
      filter_upwards with u
      unfold retainedGridCrossings
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun e _ ↦ by
        split_ifs <;> norm_num)]
      calc
        _ ≤ ∑ _e ∈ (σ ω).edges, (1 : ℝ) :=
          Finset.sum_le_sum fun e _ ↦ by split_ifs <;> norm_num
        _ = _ := by simp [OTSelector.PartialMatching.card]
    exact (integral_mono hleft hright hread).trans
      (integral_retainedGridCrossings_le (σ ω) hell (fun i ↦ xs i ω) (fun j ↦ ys j ω))
  have hmono := integral_mono hi.integral_prod_left (hdisp.div_const ell) hbound
  simpa only [integral_div] using hmono

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Finite readouts of actual translated grids, with an explicitly specified
joint law of phases. The phase marginals, rather than residual point laws,
are the randomization used in the repair estimate. -/
def shiftedHierarchyCell {Θ : Type*} {q K : ℕ} {C : Fin K → Type*}
    (ell : Fin K → ℝ) (phase : Fin K → Θ → Fin q → ℝ)
    (readout : (k : Fin K) → (Fin q → ℤ) → C k) (θ : Θ) (k : Fin K)
    (z : Fin q → ℝ) : C k :=
  readout k (shiftedGridCells (ell k) (phase k θ) z)

/-- Explicit expected cost budget for finite shifted-grid repair. The core may
be any measurable selection from the original samples. Every phase marginal
is the actual uniform grid phase. The retained-displacement coefficient is
kept explicitly and no vanishing conclusion is inferred from it. -/
theorem integral_shifted_adaptiveOrphanRepairBudget_le
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    {K N q : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    [∀ k, MeasurableSpace (C k)] [∀ k, MeasurableSingletonClass (C k)]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Θ) [IsProbabilityMeasure Q]
    (μ : Measure (Fin q → ℝ)) [IsProbabilityMeasure μ]
    (σ : Ω → OTSelector.PartialMatching N N)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k)
    (phase : Fin K → Θ → Fin q → ℝ) (hp : ∀ k, Measurable (phase k))
    (hlaw : ∀ k, Q.map (phase k) = shiftedGridPhaseLaw q (ell k))
    (readout : (k : Fin K) → (Fin q → ℤ) → C k) (hr : ∀ k, Measurable (readout k))
    (base : ℝ) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hdisp : Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P) :
    Integrable (fun p : Ω × Θ ↦ adaptiveOrphanRepairBudget (σ p.1)
      (shiftedHierarchyCell ell phase readout p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight) (P.prod Q) ∧
    (∫ p : Ω × Θ, adaptiveOrphanRepairBudget (σ p.1)
      (shiftedHierarchyCell ell phase readout p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight ∂(P.prod Q)) ≤
      (∫ ω, (N : ℝ) - (σ ω).card ∂P) * base +
        (1 / 2 : ℝ) * ∑ k, weight k * Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) +
        (∫ ω, retainedCoordinateDisplacement (σ ω)
          (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) * ∑ k, weight k / ell k := by
  classical
  let D : Fin K → Ω × Θ → ℝ := fun k p ↦ ∑ c,
    |partitionCount (fun i ↦ shiftedHierarchyCell ell phase readout p.2 k (xs i p.1)) c -
      partitionCount (fun i ↦ shiftedHierarchyCell ell phase readout p.2 k (ys i p.1)) c|
  let F : Fin K → Ω × Θ → ℝ := fun k p ↦ retainedPartitionCrossings (σ p.1)
    (fun i ↦ shiftedHierarchyCell ell phase readout p.2 k (xs i p.1))
    (fun j ↦ shiftedHierarchyCell ell phase readout p.2 k (ys j p.1))
  have hcell (k : Fin K) : Measurable (fun p : Θ × (Fin q → ℝ) ↦
      shiftedHierarchyCell ell phase readout p.1 k p.2) :=
    (hr k).comp (measurable_shiftedGridCells_comp (ell k) _ _
      ((hp k).comp measurable_fst) measurable_snd)
  have hd (k : Fin K) : Integrable (D k) (P.prod Q) ∧
      (∫ p, D k p ∂(P.prod Q)) ≤ Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) :=
    integral_parametric_original_partition_discrepancy_le P Q μ xs ys hx hy hxi hyi hxl hyl
      hxy (fun θ z ↦ shiftedHierarchyCell ell phase readout θ k z) (hcell k)
  have hf (k : Fin K) : Integrable (F k) (P.prod Q) ∧
      (∫ p, F k p ∂(P.prod Q)) ≤
      (∫ ω, retainedCoordinateDisplacement (σ ω)
        (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) / ell k :=
    integral_selected_shifted_partition_crossings_le P Q σ hσ xs ys hx hy (hell k)
      (phase k) (hp k) (hlaw k) (readout k) (hr k) hdisp
  have hcard : Integrable (fun ω ↦ ((σ ω).card : ℝ)) P := by
    apply Integrable.of_bound (measurable_retained_card σ hσ).aestronglyMeasurable N
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast ((σ ω).card_le.trans (min_le_left N N))
  have hfree := ((integrable_const (N : ℝ)).sub hcard).comp_fst Q
  have hterm (k : Fin K) := ((hd k).1.add ((hf k).1.const_mul 2)).const_mul (weight k)
  have hsum := integrable_finsetSum Finset.univ (fun k _ ↦ hterm k)
  have hi := (hfree.mul_const base).add (hsum.const_mul (1 / 2 : ℝ))
  refine ⟨hi, ?_⟩
  change (∫ p : Ω × Θ, ((N : ℝ) - (σ p.1).card) * base +
    (1 / 2 : ℝ) * ∑ k, weight k * (D k p + 2 * F k p) ∂(P.prod Q)) ≤ _
  have hsplit := integral_add (hfree.mul_const base) (hsum.const_mul (1 / 2 : ℝ))
  simp only [Pi.add_apply, Pi.sub_apply] at hsplit
  have hsplitSum := integral_finsetSum Finset.univ (fun k _ ↦ hterm k)
  simp only [Pi.add_apply] at hsplitSum
  have hfreeInt : (∫ p : Ω × Θ, (N : ℝ) - (σ p.1).card ∂(P.prod Q)) =
      ∫ ω, (N : ℝ) - (σ ω).card ∂P := by
    simpa using integral_fun_fst (μ := P) (ν := Q) (fun ω ↦ (N : ℝ) - (σ ω).card)
  rw [hsplit, integral_mul_const, integral_const_mul, hsplitSum, hfreeInt]
  have hk (k : Fin K) : (∫ p : Ω × Θ, weight k * (D k p + 2 * F k p) ∂(P.prod Q)) ≤
      weight k * (Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) +
        2 * ((∫ ω, retainedCoordinateDisplacement (σ ω)
          (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) / ell k)) := by
    rw [integral_const_mul, integral_add (hd k).1 ((hf k).1.const_mul 2), integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (hw k)
    exact add_le_add (hd k).2 (mul_le_mul_of_nonneg_left (hf k).2 (by norm_num))
  have hmono := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ hk k)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply (add_le_add_right hmono _).trans_eq
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

end OTSelector.Reconstruction
