import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyShifted

/-!
# Adaptive flux for one actual phase law across a finite hierarchy

A common phase can govern every partition level. The only geometric input is
the proved crossing probability of its actual cell map. All expectations are
under the product of the original iid observations and this independent phase.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Actual one-phase crossing probabilities control the expected crossing flux
of an arbitrary original-observation measurable retained core. -/
theorem integral_selected_phase_partition_crossings_le
    {Ω Θ C : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableEq C] {m n q : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Θ) [IsProbabilityMeasure Q]
    (σ : Ω → OTSelector.PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs : Fin m → Ω → Fin q → ℝ) (ys : Fin n → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    {ell : ℝ} (hell : 0 < ell) (cell : Θ → (Fin q → ℝ) → C)
    (hcell : Measurable (fun p : Θ × (Fin q → ℝ) ↦ cell p.1 p.2))
    (hcross : ∀ x y, Q {θ | cell θ x ≠ cell θ y} ≤
      ENNReal.ofReal ((∑ i, |x i - y i|) / ell))
    (hdisp : Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P) :
    Integrable (fun p : Ω × Θ ↦ retainedPartitionCrossings (σ p.1)
      (fun i ↦ cell p.2 (xs i p.1)) (fun j ↦ cell p.2 (ys j p.1))) (P.prod Q) ∧
    (∫ p : Ω × Θ, retainedPartitionCrossings (σ p.1)
      (fun i ↦ cell p.2 (xs i p.1)) (fun j ↦ cell p.2 (ys j p.1)) ∂(P.prod Q)) ≤
      (∫ ω, retainedCoordinateDisplacement (σ ω)
        (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) / ell := by
  classical
  have ha (i : Fin m) : Measurable (fun p : Ω × Θ ↦ cell p.2 (xs i p.1)) :=
    hcell.comp (measurable_snd.prodMk ((hx i).comp measurable_fst))
  have hb (j : Fin n) : Measurable (fun p : Ω × Θ ↦ cell p.2 (ys j p.1)) :=
    hcell.comp (measurable_snd.prodMk ((hy j).comp measurable_fst))
  have hi := integrable_selected_partition_crossings (P.prod Q) (fun p ↦ σ p.1)
    (fun e ↦ (hσ e).preimage measurable_fst) _ _ ha hb
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  have hbound (ω : Ω) : (∫ θ, retainedPartitionCrossings (σ ω)
      (fun i ↦ cell θ (xs i ω)) (fun j ↦ cell θ (ys j ω)) ∂Q) ≤
      retainedCoordinateDisplacement (σ ω) (fun i ↦ xs i ω) (fun j ↦ ys j ω) / ell := by
    have hm (e : Fin m × Fin n) : MeasurableSet {θ | cell θ (xs e.1 ω) ≠ cell θ (ys e.2 ω)} :=
      (measurableSet_eq_fun (hcell.comp (measurable_id.prodMk measurable_const))
        (hcell.comp (measurable_id.prodMk measurable_const))).compl
    have hterm (e : Fin m × Fin n) : Integrable (fun θ ↦
        if cell θ (xs e.1 ω) ≠ cell θ (ys e.2 ω) then (1 : ℝ) else 0) Q := by
      refine Integrable.of_bound (Measurable.ite (hm e) measurable_const
        measurable_const).aestronglyMeasurable 1 ?_
      filter_upwards with θ
      split_ifs <;> norm_num
    unfold retainedPartitionCrossings retainedCoordinateDisplacement
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [integral_finsetSum _ (fun e _ ↦ hterm e), Finset.sum_div]
    apply Finset.sum_le_sum
    intro e he
    have hrepr : (fun θ ↦ if cell θ (xs e.1 ω) ≠ cell θ (ys e.2 ω) then (1 : ℝ) else 0) =
        {θ | cell θ (xs e.1 ω) ≠ cell θ (ys e.2 ω)}.indicator (fun _ ↦ (1 : ℝ)) := by
      funext θ
      by_cases h : cell θ (xs e.1 ω) = cell θ (ys e.2 ω) <;> simp [Set.indicator, h]
    rw [hrepr, integral_indicator_const 1 (hm e)]
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcross (xs e.1 ω) (ys e.2 ω))
    rw [ENNReal.toReal_ofReal (by positivity)] at hreal
    simpa only [Measure.real, smul_eq_mul, mul_one] using hreal
  have hmono := integral_mono hi.integral_prod_left (hdisp.div_const ell) hbound
  simpa only [integral_div] using hmono

/-- Finite-cutoff repair budget under one actual common phase law, with
its full retained-displacement coefficient explicit. -/
theorem integral_phase_adaptiveOrphanRepairBudget_le
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
    (cell : Θ → (k : Fin K) → (Fin q → ℝ) → C k)
    (hcell : ∀ k, Measurable (fun p : Θ × (Fin q → ℝ) ↦ cell p.1 k p.2))
    (hcross : ∀ k x y, Q {θ | cell θ k x ≠ cell θ k y} ≤
      ENNReal.ofReal ((∑ i, |x i - y i|) / ell k))
    (base : ℝ) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hdisp : Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P) :
    Integrable (fun p : Ω × Θ ↦ adaptiveOrphanRepairBudget (σ p.1)
      (cell p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight) (P.prod Q) ∧
    (∫ p : Ω × Θ, adaptiveOrphanRepairBudget (σ p.1)
      (cell p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight ∂(P.prod Q)) ≤
      (∫ ω, (N : ℝ) - (σ ω).card ∂P) * base +
        (1 / 2 : ℝ) * ∑ k, weight k * Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) +
        (∫ ω, retainedCoordinateDisplacement (σ ω)
          (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) * ∑ k, weight k / ell k := by
  classical
  let D : Fin K → Ω × Θ → ℝ := fun k p ↦ ∑ c,
    |partitionCount (fun i ↦ cell p.2 k (xs i p.1)) c -
      partitionCount (fun i ↦ cell p.2 k (ys i p.1)) c|
  let F : Fin K → Ω × Θ → ℝ := fun k p ↦ retainedPartitionCrossings (σ p.1)
    (fun i ↦ cell p.2 k (xs i p.1))
    (fun j ↦ cell p.2 k (ys j p.1))
  have hd (k : Fin K) : Integrable (D k) (P.prod Q) ∧
      (∫ p, D k p ∂(P.prod Q)) ≤ Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) :=
    integral_parametric_original_partition_discrepancy_le P Q μ xs ys hx hy hxi hyi hxl hyl
      hxy (fun θ z ↦ cell θ k z) (hcell k)
  have hf (k : Fin K) : Integrable (F k) (P.prod Q) ∧
      (∫ p, F k p ∂(P.prod Q)) ≤
      (∫ ω, retainedCoordinateDisplacement (σ ω)
        (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) / ell k :=
    integral_selected_phase_partition_crossings_le P Q σ hσ xs ys hx hy (hell k)
      (fun θ z ↦ cell θ k z) (hcell k) (hcross k) hdisp
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
