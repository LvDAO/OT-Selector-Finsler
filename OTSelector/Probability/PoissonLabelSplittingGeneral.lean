import OTSelector.Probability.MultinomialSplitting
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
# Poisson label splitting for nonuniform label probabilities

The uniform splitting law `map_poisson_label_counts` describes independent labels drawn
uniformly from `Fin K`.  The block hierarchy, however, assigns each cell a volume, so labels
carry arbitrary probabilities `p : Fin K → ℝ≥0` with `∑ b, p b = 1`.

This file generalizes the fixed-`n` multinomial law and the Poisson splitting law:

* for `n` independent labels with law `∑ b, p b • δ b`, the vector of label counts `k` has mass
  `(multinomial univ k) * ∏ b, p b ^ k b`;
* for a Poisson number `N` of such labels, independent of every finite prefix, the vector of
  label counts has independent Poisson coordinates with rates `Λ * p b`.

The proofs follow the uniform ones: the fixed-`n` law is obtained by pushing the labels forward
to the product law on words and counting the words with prescribed letter multiplicities, while
the Poisson law is obtained by conditioning on `N = n` and summing the Poisson series.  The only
new algebraic input is the weighted multinomial identity
`e^{-Λ} Λ^n / n! * (n! / ∏ k_b!) ∏ p_b^{k_b} = ∏ e^{-Λ p_b} (Λ p_b)^{k_b} / k_b!`,
which uses `∑ k_b = n` and `∑ p_b = 1`.

Finally, grouping the labels into the cells of a map `f : Fin K → Fin M` gives independent
Poisson cell counts with rates `Λ * ∑_{b : f b = c} p b`; comparing two independent samples, the
expected total cell discrepancy is at most `sqrt (2 * Λ * M)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1000000

/-! ## Part A: weighted word counts -/

/-- For a word `v` whose letter counts are `k`, the product of the label probabilities over the
letters of `v` equals `∏ b, p b ^ k b`.  This is `Finset.prod_fiberwise'` applied to the fibers
of `v`. -/
theorem prod_pow_labelCount {n K : ℕ} (p : Fin K → ℝ≥0∞) (v : Fin n → Fin K) :
    ∏ b, p b ^ labelCount v b = ∏ i, p (v i) := by
  classical
  have h := Finset.prod_fiberwise' (Finset.univ : Finset (Fin n)) v p
  simp only [labelCount]
  rw [← h]
  apply Finset.prod_congr rfl
  intro b _
  rw [Finset.prod_const]

/-- The weighted label law `∑ b, p b • δ b` is a probability measure when the weights sum
to one. -/
theorem isProbabilityMeasure_sum_smul_dirac {K : ℕ} (p : Fin K → ℝ≥0)
    (hp : ∑ b, p b = 1) :
    IsProbabilityMeasure (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) := by
  have hsum : (∑ b : Fin K, (p b : ℝ≥0∞)) = 1 := by
    rw [← ENNReal.ofNNReal_finsetSum, hp, ENNReal.coe_one]
  have h : HasSum (fun b : Fin K => (p b : ℝ≥0∞)) 1 := by
    simpa only [hsum] using hasSum_fintype (fun b : Fin K => (p b : ℝ≥0∞))
  exact HasSum.isProbabilityMeasure_sum_dirac_ennreal h

/-- Point mass of the product law at a word: it is the product of the weights of its letters. -/
private theorem pi_weighted_singleton {n K : ℕ} (p : Fin K → ℝ≥0)
    (hp : ∑ b, p b = 1) (v : Fin n → Fin K) :
    Measure.pi (fun _ : Fin n =>
        Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) {v} =
      ∏ i, (p (v i) : ℝ≥0∞) := by
  classical
  haveI : IsProbabilityMeasure
      (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) :=
    isProbabilityMeasure_sum_smul_dirac p hp
  rw [Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun i _ => Measure.sum_smul_dirac_singleton)

/-- Mass of the event that a word has letter counts `k`, under the product law with weights
`p`: every word with those counts has mass `∏ b, p b ^ k b`, and there are
`Nat.card {ω // labelCount ω = k}` of them. -/
private theorem pi_weighted_labelCount {n K : ℕ} (p : Fin K → ℝ≥0)
    (hp : ∑ b, p b = 1) (k : Fin K → ℕ) :
    Measure.pi (fun _ : Fin n =>
        Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b))
        {ω : Fin n → Fin K | labelCount ω = k} =
      (Nat.card {ω : Fin n → Fin K // labelCount ω = k} : ℝ≥0∞) *
        ∏ b, (p b : ℝ≥0∞) ^ (k b) := by
  classical
  haveI : IsProbabilityMeasure
      (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) :=
    isProbabilityMeasure_sum_smul_dirac p hp
  set S : Finset (Fin n → Fin K) := Finset.univ.filter (fun ω => labelCount ω = k)
  have hset : {ω : Fin n → Fin K | labelCount ω = k} = (↑S : Set (Fin n → Fin K)) := by
    ext ω; simp [S]
  have hset2 : (↑S : Set (Fin n → Fin K)) = ⋃ v ∈ S, ({v} : Set (Fin n → Fin K)) := by
    ext x; simp
  rw [hset, hset2, measure_biUnion_finset]
  · have hstep : (∑ v ∈ S, Measure.pi (fun _ : Fin n =>
          Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) {v}) =
        ∑ _v ∈ S, ∏ b, (p b : ℝ≥0∞) ^ (k b) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [pi_weighted_singleton p hp v,
        ← prod_pow_labelCount (fun b : Fin K => (p b : ℝ≥0∞)) v,
        (Finset.mem_filter.mp hv).2]
    rw [hstep, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro a _ b _ hab
    exact Set.disjoint_singleton.mpr hab
  · intro b _
    exact measurableSet_singleton b

/-- **Weighted multinomial law.**  If `n` independent labels have law `∑ b, p b • δ b`, then the
probability that the label counts are `k` is the multinomial coefficient times
`∏ b, p b ^ k b`, and it vanishes unless the counts sum to `n`. -/
theorem map_label_counts_singleton_general_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n K : ℕ} [NeZero K] (w : Fin n → Ω → Fin K)
    (hw : ∀ i, AEMeasurable (w i) P) (hi : iIndepFun w P)
    (p : Fin K → ℝ≥0) (hp : ∑ b, p b = 1)
    (hlaw : ∀ i, P.map (w i) = Measure.sum (fun b => (p b : ℝ≥0∞) • Measure.dirac b))
    (k : Fin K → ℕ) :
    P {ξ | labelCount (fun i => w i ξ) = k} =
      if ∑ b, k b = n then
        (Nat.multinomial Finset.univ k : ℝ≥0∞) * ∏ b, (p b : ℝ≥0∞) ^ (k b)
      else 0 := by
  classical
  haveI : IsProbabilityMeasure
      (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) :=
    isProbabilityMeasure_sum_smul_dirac p hp
  let W : Ω → (Fin n → Fin K) := fun ξ i => w i ξ
  have hWae : AEMeasurable W P := aemeasurable_pi_lambda _ hw
  have hjoint : P.map W = Measure.pi (fun _ : Fin n =>
      Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) := by
    have h := iIndepFun.map_fun_eq_pi_map (f := w) hw hi
    rw [show (fun i => P.map (w i)) = (fun _ : Fin n =>
        Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) from
      funext hlaw] at h
    exact h
  have hSmeas : MeasurableSet {ω : Fin n → Fin K | labelCount ω = k} :=
    (measurableSet_singleton k).preimage (measurable_of_countable _)
  have hpre : {ξ | labelCount (fun i => w i ξ) = k} =
      W ⁻¹' {ω : Fin n → Fin K | labelCount ω = k} := rfl
  rw [hpre, ← Measure.map_apply_of_aemeasurable hWae hSmeas, hjoint,
    pi_weighted_labelCount p hp k, Nat.card_eq_fintype_card]
  split_ifs with hk
  · have hcard : Fintype.card {ω : Fin n → Fin K // labelCount ω = k} =
        Nat.multinomial Finset.univ k := by
      rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun ω => funext_iff))]
      rw [← Nat.card_eq_fintype_card]
      exact card_words_with_counts k hk
    rw [hcard]
  · have hempty : IsEmpty {ω : Fin n → Fin K // labelCount ω = k} :=
      ⟨fun x => hk (by rw [← x.2, sum_labelCount])⟩
    have hzero : Fintype.card {ω : Fin n → Fin K // labelCount ω = k} = 0 :=
      Fintype.card_eq_zero_iff.mpr hempty
    rw [hzero]
    simp

/-! ## Part B: the weighted multinomial identity -/

/-- Real-valued weighted multinomial identity: the Poisson mass of `n = ∑ b, k b` times the
multinomial coefficient and the weights `∏ b, p b ^ k b` equals the product of the Poisson
masses of the individual counts with rates `Λ * p b`. -/
private lemma poisson_weighted_multinomial_real {K : ℕ} (Λ : ℝ≥0) (p : Fin K → ℝ≥0)
    (hp : ∑ b, p b = 1) (k : Fin K → ℕ) :
    Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ (∑ b, k b) /
        ((Nat.factorial (∑ b, k b) : ℕ) : ℝ) *
        (∏ b, (p b : ℝ) ^ k b) *
        (Nat.multinomial Finset.univ k : ℝ) =
      ∏ b, Real.exp (-((Λ : ℝ) * (p b : ℝ))) *
        (((Λ : ℝ) * (p b : ℝ)) ^ k b) /
        ((Nat.factorial (k b) : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp at hp
  have hfac_ne : ∀ b : Fin K, (((Nat.factorial (k b) : ℕ) : ℝ)) ≠ 0 := fun b => by
    rw [Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero _
  have hP_ne : (∏ b : Fin K, ((Nat.factorial (k b) : ℕ) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => hfac_ne b)
  have hNfac_ne : (((Nat.factorial (∑ b, k b) : ℕ) : ℝ)) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero _
  have hmult_nat : (∏ b, Nat.factorial (k b)) * Nat.multinomial Finset.univ k =
      Nat.factorial (∑ b, k b) := by
    simpa using Nat.multinomial_spec Finset.univ k
  have hmult : (Nat.multinomial Finset.univ k : ℝ) =
      (((Nat.factorial (∑ b, k b) : ℕ) : ℝ)) /
        (∏ b : Fin K, ((Nat.factorial (k b) : ℕ) : ℝ)) := by
    rw [eq_div_iff hP_ne]
    have h := congrArg (fun m : ℕ => (m : ℝ)) hmult_nat
    push_cast at h
    rw [mul_comm] at h
    exact h
  have hpR : (∑ b : Fin K, (p b : ℝ)) = 1 := by
    rw [← NNReal.coe_sum, hp, NNReal.coe_one]
  have hexp : (∏ b : Fin K, Real.exp (-((Λ : ℝ) * (p b : ℝ)))) =
      Real.exp (-(Λ : ℝ)) := by
    rw [← Real.exp_sum]
    congr 1
    calc ∑ b : Fin K, -((Λ : ℝ) * (p b : ℝ))
        = -((Λ : ℝ) * ∑ b : Fin K, (p b : ℝ)) := by
          rw [Finset.mul_sum, Finset.sum_neg_distrib]
      _ = -(Λ : ℝ) := by rw [hpR, mul_one]
  have hprod : (∏ b : Fin K, (((Λ : ℝ) * (p b : ℝ)) ^ k b)) =
      (Λ : ℝ) ^ (∑ b, k b) * ∏ b : Fin K, (p b : ℝ) ^ k b := by
    calc ∏ b : Fin K, ((Λ : ℝ) * (p b : ℝ)) ^ k b
        = ∏ b : Fin K, ((Λ : ℝ) ^ k b * (p b : ℝ) ^ k b) := by
          exact Finset.prod_congr rfl (fun b _ => by rw [mul_pow])
      _ = (∏ b : Fin K, (Λ : ℝ) ^ k b) * ∏ b : Fin K, (p b : ℝ) ^ k b :=
          Finset.prod_mul_distrib
      _ = (Λ : ℝ) ^ (∑ b, k b) * ∏ b : Fin K, (p b : ℝ) ^ k b := by
          rw [Finset.prod_pow_eq_pow_sum]
  have hR : (∏ b : Fin K, Real.exp (-((Λ : ℝ) * (p b : ℝ))) *
        (((Λ : ℝ) * (p b : ℝ)) ^ k b) /
        ((Nat.factorial (k b) : ℕ) : ℝ)) =
      Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ (∑ b, k b) *
        (∏ b : Fin K, (p b : ℝ) ^ k b) /
        (∏ b : Fin K, ((Nat.factorial (k b) : ℕ) : ℝ)) := by
    rw [Finset.prod_div_distrib]
    rw [Finset.prod_mul_distrib]
    rw [hexp, hprod]
    ring
  rw [hR, hmult]
  field_simp

/-- **Weighted Poisson multinomial identity.**  Multiplying the Poisson mass of
`n = ∑ b, k b` by the multinomial coefficient and the weights `∏ b, p b ^ k b` gives the
product of the Poisson masses with rates `Λ * p b`. -/
theorem poissonMeasure_singleton_mul_weighted_multinomial {K : ℕ} (Λ : ℝ≥0)
    (p : Fin K → ℝ≥0) (hp : ∑ b, p b = 1) (k : Fin K → ℕ) :
    poissonMeasure Λ {∑ b, k b} * (∏ b, (p b : ℝ≥0∞) ^ k b) *
      (Nat.multinomial Finset.univ k : ℝ≥0∞) =
      ∏ b, poissonMeasure (Λ * p b) {k b} := by
  classical
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp at hp
  have hB : (∏ b : Fin K, (p b : ℝ≥0∞) ^ k b) =
      ENNReal.ofReal (∏ b : Fin K, (p b : ℝ) ^ k b) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun b _ => by positivity)]
    exact Finset.prod_congr rfl (fun b _ => by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal])
  have hleft : poissonMeasure Λ {∑ b, k b} * (∏ b : Fin K, (p b : ℝ≥0∞) ^ k b) *
      (Nat.multinomial Finset.univ k : ℝ≥0∞) =
      ENNReal.ofReal (Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ (∑ b, k b) /
        ((Nat.factorial (∑ b, k b) : ℕ) : ℝ) * (∏ b : Fin K, (p b : ℝ) ^ k b) *
        (Nat.multinomial Finset.univ k : ℝ)) := by
    rw [poissonMeasure_singleton, hB, ← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have hright : (∏ b : Fin K, poissonMeasure (Λ * p b) {k b}) =
      ENNReal.ofReal (∏ b : Fin K, Real.exp (-((Λ : ℝ) * (p b : ℝ))) *
        (((Λ : ℝ) * (p b : ℝ)) ^ k b) /
        ((Nat.factorial (k b) : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun b _ => by positivity)]
    apply Finset.prod_congr rfl
    intro b _
    rw [poissonMeasure_singleton]
    congr 1
  rw [hleft, hright, ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  exact poisson_weighted_multinomial_real Λ p hp k

/-! ## Part C: Poisson splitting with nonuniform labels -/

/-- **Poisson splitting of independent nonuniform labels.**  If `N` is Poisson with rate `Λ`,
the labels are independent with law `∑ b, p b • δ b`, and `N` is independent of every finite
prefix of the label sequence, then the count vector of the first `N` labels has independent
Poisson coordinates with rates `Λ * p b`. -/
theorem map_poisson_label_counts_general
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K)
    (p : Fin K → ℝ≥0) (hp : ∑ b, p b = 1)
    (hN : P.map N = poissonMeasure Λ)
    (hw : ∀ n, iIndepFun (fun i : Fin n => w i) P)
    (hlaw : ∀ i, P.map (w i) = Measure.sum (fun b => (p b : ℝ≥0∞) • Measure.dirac b))
    (hindep : ∀ n, IndepFun N (fun ξ => fun i : Fin n => w i ξ) P) :
    P.map (fun ξ => fun b => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card) =
      Measure.pi (fun b : Fin K => poissonMeasure (Λ * p b)) := by
  classical
  haveI : IsProbabilityMeasure
      (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) :=
    isProbabilityMeasure_sum_smul_dirac p hp
  have hNae : AEMeasurable N P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hN]
    exact IsProbabilityMeasure.ne_zero (poissonMeasure Λ)
  have hwae : ∀ i : ℕ, AEMeasurable (w i) P := by
    intro i
    apply AEMeasurable.of_map_ne_zero
    rw [hlaw i]
    exact IsProbabilityMeasure.ne_zero
      (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b))
  have hmkN : Measurable (hNae.mk N) := hNae.measurable_mk
  have hmkw : ∀ i : ℕ, Measurable ((hwae i).mk (w i)) := fun i => (hwae i).measurable_mk
  let mkCount : Ω → (Fin K → ℕ) :=
    prefixLabelCount (hNae.mk N) (fun i => (hwae i).mk (w i))
  have hmkCount : Measurable mkCount := by
    apply measurable_to_countable'
    intro k
    have hset : {ξ | mkCount ξ = k} =
        ⋃ n, ({ξ | hNae.mk N ξ = n} ∩
          {ξ | labelCount (fun i : Fin n => (hwae i).mk (w i) ξ) = k}) := by
      ext ξ
      simp only [mkCount, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨hNae.mk N ξ, rfl, h⟩
      · rintro ⟨n, hn, hk⟩; subst hn; exact hk
    change MeasurableSet {ξ | mkCount ξ = k}
    rw [hset]
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.inter
    · exact hmkN (measurableSet_singleton n)
    · exact ((measurable_of_countable (fun ω : Fin n → Fin K => labelCount ω)).comp
        (measurable_pi_lambda _ (fun i => hmkw i))) (measurableSet_singleton k)
  have hcount_ae : AEMeasurable (prefixLabelCount N w) P := by
    refine ⟨mkCount, hmkCount, ?_⟩
    have hN_ae : N =ᵐ[P] hNae.mk N := hNae.ae_eq_mk
    have hw_ae : ∀ i, w i =ᵐ[P] (hwae i).mk (w i) := fun i => (hwae i).ae_eq_mk
    have hall : ∀ᵐ ξ ∂P, (∀ i, w i ξ = (hwae i).mk (w i) ξ) ∧ N ξ = hNae.mk N ξ := by
      have h1 : ∀ᵐ ξ ∂P, ∀ i : ℕ, w i ξ = (hwae i).mk (w i) ξ :=
        ae_all_iff.mpr hw_ae
      filter_upwards [h1, hN_ae] with ξ h1' hN'
      exact ⟨h1', hN'⟩
    filter_upwards [hall] with ξ hξ
    obtain ⟨hwi, hNi⟩ := hξ
    change (fun b => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card) =
      (fun b => (Finset.univ.filter fun i : Fin ((hNae.mk N) ξ) =>
        (hwae i).mk (w i) ξ = b).card)
    rw [show hNae.mk N ξ = N ξ from hNi.symm]
    funext b
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    rw [hwi i]
  refine Measure.ext_of_singleton (fun k => ?_)
  rw [Measure.pi_singleton]
  change (P.map (prefixLabelCount N w)) {k} =
    ∏ b, poissonMeasure (Λ * p b) {k b}
  rw [Measure.map_apply_of_aemeasurable hcount_ae (measurableSet_singleton k)]
  change P (prefixLabelCount N w ⁻¹' {k}) = _
  let A : ℕ → Set Ω := fun n =>
    N ⁻¹' {n} ∩ (fun ξ => fun i : Fin n => w i ξ) ⁻¹' {ω : Fin n → Fin K | labelCount ω = k}
  have hUnion : prefixLabelCount N w ⁻¹' {k} = ⋃ n, A n := by
    ext ξ
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨N ξ, rfl, h⟩
    · rintro ⟨n, hn, hk⟩
      subst hn
      exact hk
  have hSmeas (n : ℕ) : MeasurableSet {ω : Fin n → Fin K | labelCount ω = k} :=
    (measurableSet_singleton k).preimage (measurable_of_countable _)
  have hA_null : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    apply NullMeasurableSet.inter
    · exact hNae.nullMeasurableSet_preimage (measurableSet_singleton n)
    · have hWae : AEMeasurable (fun ξ => fun i : Fin n => w i ξ) P :=
        aemeasurable_pi_lambda _ (fun i => hwae i)
      exact hWae.nullMeasurableSet_preimage (hSmeas n)
  have hdisj : Pairwise (Function.onFun (AEDisjoint P) A) := by
    intro m n hmn
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro ξ hξm hξn
    exact hmn (hξm.1.symm.trans hξn.1)
  have hA_apply (n : ℕ) : P (A n) =
      poissonMeasure Λ {n} *
        (if ∑ b, k b = n then
          (Nat.multinomial Finset.univ k : ℝ≥0∞) * ∏ b, (p b : ℝ≥0∞) ^ (k b)
        else 0) := by
    simp only [A]
    rw [(hindep n).measure_inter_preimage_eq_mul {n}
      {ω : Fin n → Fin K | labelCount ω = k} (measurableSet_singleton n) (hSmeas n)]
    congr 1
    · rw [← Measure.map_apply_of_aemeasurable hNae (measurableSet_singleton n), hN]
    · exact map_label_counts_singleton_general_ae (fun i : Fin n => w i)
        (fun i => hwae i) (hw n) p hp (fun i => hlaw i) k
  rw [hUnion, measure_iUnion₀ hdisj hA_null]
  rw [tsum_eq_single (∑ b, k b)]
  · rw [hA_apply, ite_eq_left rfl]
    rw [← mul_assoc, mul_right_comm]
    exact poissonMeasure_singleton_mul_weighted_multinomial Λ p hp k
  · intro n hn
    rw [hA_apply, ite_eq_right (fun h => hn h.symm)]
    simp

/-! ## Part D: grouped block discrepancy -/

/-- Pushing the weighted label law through a cell map groups the probabilities by fiber. -/
private theorem map_sum_smul_dirac_comp {K M : ℕ} (p : Fin K → ℝ≥0) (f : Fin K → Fin M) :
    Measure.map f (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) =
      Measure.sum (fun c : Fin M =>
        ((∑ b ∈ Finset.univ with f b = c, p b : ℝ≥0) : ℝ≥0∞) •
          Measure.dirac c) := by
  classical
  have hf : Measurable f := measurable_of_countable f
  refine Measure.ext_of_singleton (fun c => ?_)
  rw [Measure.map_apply hf (measurableSet_singleton c),
    Measure.sum_apply _ (hf (measurableSet_singleton c)),
    Measure.sum_smul_dirac_singleton]
  have hterm : ∀ b : Fin K,
      ((p b : ℝ≥0∞) • Measure.dirac b) (f ⁻¹' {c}) =
        if f b = c then (p b : ℝ≥0∞) else 0 := by
    intro b
    rw [Measure.smul_apply, Measure.dirac_apply]
    by_cases h : f b = c
    · rw [Set.indicator_of_mem (by simpa using h)]
      simp [h]
    · rw [Set.indicator_of_notMem (by simpa using h)]
      simp [h]
  simp_rw [hterm]
  rw [tsum_fintype, ← Finset.sum_filter, ← ENNReal.ofNNReal_finsetSum]

/-- **Grouped block discrepancy bound.**  For independent labels with probabilities `p`, the
counts in the cells of a map `f : Fin K → Fin M` are independent Poisson variables with rates
`Λ * ∑_{b : f b = c} p b`.  Consequently the expected total cell discrepancy between two
independent samples is at most `sqrt (2 * Λ * M)`.

The bound is proved by applying the general splitting law to the composed label map, then
comparing the resulting product of Poisson laws with `integral_sum_abs_sub_poissonPi_le` and
bounding the sum of square roots by Cauchy–Schwarz. -/
theorem integral_grouped_label_discrepancy_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K M : ℕ} [NeZero K] [NeZero M] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K)
    (f : Fin K → Fin M) (p : Fin K → ℝ≥0) (hp : ∑ b, p b = 1)
    (hN : P.map N = poissonMeasure Λ)
    (hw : ∀ n, iIndepFun (fun i : Fin n => w i) P)
    (hlaw : ∀ i, P.map (w i) = Measure.sum (fun b => (p b : ℝ≥0∞) • Measure.dirac b))
    (hindep : ∀ n, IndepFun N (fun ξ => fun i : Fin n => w i ξ) P) :
    ∫ z : Ω × Ω, (∑ c : Fin M,
        |((Finset.univ.filter (fun i : Fin (N z.1) => f (w i z.1) = c)).card : ℝ) -
         ((Finset.univ.filter (fun i : Fin (N z.2) => f (w i z.2) = c)).card : ℝ)|)
      ∂(P.prod P) ≤
      Real.sqrt (2 * (Λ : ℝ) * (Fintype.card (Fin M) : ℝ)) := by
  classical
  haveI : IsProbabilityMeasure
      (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b)) :=
    isProbabilityMeasure_sum_smul_dirac p hp
  have hNae : AEMeasurable N P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hN]
    exact IsProbabilityMeasure.ne_zero (poissonMeasure Λ)
  have hwae : ∀ i : ℕ, AEMeasurable (w i) P := by
    intro i
    apply AEMeasurable.of_map_ne_zero
    rw [hlaw i]
    exact IsProbabilityMeasure.ne_zero
      (Measure.sum (fun b : Fin K => (p b : ℝ≥0∞) • Measure.dirac b))
  let q : Fin M → ℝ≥0 :=
    fun c => ∑ b ∈ Finset.univ with f b = c, p b
  have hq : ∑ c : Fin M, q c = 1 := by
    change (∑ c : Fin M,
      ∑ b ∈ Finset.univ with f b = c, p b) = 1
    rw [Finset.sum_fiberwise (Finset.univ : Finset (Fin K)) f p]
    simpa using hp
  have hlaw_f : ∀ i, P.map (fun ξ => f (w i ξ)) =
      Measure.sum (fun c : Fin M => (q c : ℝ≥0∞) • Measure.dirac c) := by
    intro i
    have hcomp : AEMeasurable (fun ξ => f (w i ξ)) P :=
      (measurable_of_countable f).comp_aemeasurable (hwae i)
    refine Measure.ext_of_singleton (fun c => ?_)
    rw [Measure.map_apply_of_aemeasurable hcomp (measurableSet_singleton c)]
    have hpre : (fun ξ => f (w i ξ)) ⁻¹' {c} = (w i) ⁻¹' (f ⁻¹' {c}) := rfl
    rw [hpre, ← Measure.map_apply_of_aemeasurable (hwae i)
      ((measurable_of_countable f) (measurableSet_singleton c)), hlaw i]
    rw [← Measure.map_apply (measurable_of_countable f) (measurableSet_singleton c)]
    rw [map_sum_smul_dirac_comp p f]
  let g : Ω → Fin M → ℕ := fun ξ c =>
    (Finset.univ.filter fun i : Fin (N ξ) => f (w i ξ) = c).card
  have hsplit : P.map g = Measure.pi (fun c : Fin M => poissonMeasure (Λ * q c)) := by
    have hw' : ∀ n, iIndepFun (fun i : Fin n => fun ξ => f (w i ξ)) P := by
      intro n
      exact (hw n).comp (fun _ : Fin n => f) (fun _ => measurable_of_countable f)
    have hindep' : ∀ n, IndepFun N (fun ξ => fun i : Fin n => f (w i ξ)) P := by
      intro n
      have h := (hindep n).comp measurable_id
        (measurable_of_countable (fun v : Fin n → Fin K => fun i => f (v i)))
      have hfun : ((fun v : Fin n → Fin K => fun i => f (v i)) ∘
          (fun ξ => fun i : Fin n => w i ξ)) =
          (fun ξ => fun i : Fin n => f (w i ξ)) := rfl
      rwa [hfun] at h
    exact map_poisson_label_counts_general Λ N (fun i ξ => f (w i ξ)) q hq hN hw'
      hlaw_f hindep'
  let π : Fin M → Measure ℕ := fun c => poissonMeasure (Λ * q c)
  let F : (Fin M → ℕ) × (Fin M → ℕ) → ℝ :=
    fun z => ∑ c, |((z.1 c : ℕ) : ℝ) - ((z.2 c : ℕ) : ℝ)|
  have hFmeas : Measurable F := measurable_of_countable F
  have hgae : AEMeasurable g P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hsplit]
    exact IsProbabilityMeasure.ne_zero (Measure.pi π)
  have hg'_meas : Measurable (hgae.mk g) := hgae.measurable_mk
  have hgg' : g =ᵐ[P] hgae.mk g := hgae.ae_eq_mk
  have hpair : (P.prod P).map (fun z : Ω × Ω => (g z.1, g z.2)) =
      (Measure.pi π).prod (Measure.pi π) := by
    have hpair_ae : (fun z : Ω × Ω => (g z.1, g z.2)) =ᵐ[P.prod P]
        (fun z => (hgae.mk g z.1, hgae.mk g z.2)) := by
      have h1 : (fun z : Ω × Ω => g z.1) =ᵐ[P.prod P]
          (fun z => hgae.mk g z.1) :=
        (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae_eq_comp hgg'
      have h2 : (fun z : Ω × Ω => g z.2) =ᵐ[P.prod P]
          (fun z => hgae.mk g z.2) :=
        (Measure.quasiMeasurePreserving_snd (μ := P) (ν := P)).ae_eq_comp hgg'
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
    rw [Measure.map_congr hpair_ae]
    change (P.prod P).map (Prod.map (hgae.mk g) (hgae.mk g)) =
      (Measure.pi π).prod (Measure.pi π)
    rw [← Measure.map_prod_map P P hg'_meas hg'_meas, ← Measure.map_congr hgg', hsplit]
  have hIntegral : ∫ z : Ω × Ω, F (g z.1, g z.2) ∂(P.prod P) =
      ∫ w : (Fin M → ℕ) × (Fin M → ℕ), F w ∂((Measure.pi π).prod (Measure.pi π)) := by
    have hφae : AEMeasurable (fun z : Ω × Ω => (g z.1, g z.2)) (P.prod P) := by
      apply AEMeasurable.of_map_ne_zero
      rw [hpair]
      exact IsProbabilityMeasure.ne_zero ((Measure.pi π).prod (Measure.pi π))
    have hF : AEStronglyMeasurable F
        (Measure.map (fun z : Ω × Ω => (g z.1, g z.2)) (P.prod P)) := by
      rw [hpair]
      exact hFmeas.aestronglyMeasurable
    have h := integral_map hφae hF
    rw [hpair] at h
    exact h.symm
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ (Fin M)
  have hmp : MeasurePreserving e (Measure.pi (fun c => (π c).prod (π c)))
      ((Measure.pi π).prod (Measure.pi π)) :=
    measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin M) π π
  have hIntegral2 :
      ∫ w : (Fin M → ℕ) × (Fin M → ℕ), F w ∂((Measure.pi π).prod (Measure.pi π)) =
      ∫ x : Fin M → ℕ × ℕ, (∑ c, |((x c).1 : ℝ) - ((x c).2 : ℝ)|)
        ∂(Measure.pi (fun c => (π c).prod (π c))) := by
    rw [← hmp.integral_comp e.measurableEmbedding F]
    congr with x
  have hCS : (∑ c : Fin M, Real.sqrt (2 * ((Λ * q c : ℝ≥0) : ℝ))) ≤
      Real.sqrt (2 * (Λ : ℝ) * (Fintype.card (Fin M) : ℝ)) := by
    have hqR : (∑ c : Fin M, (q c : ℝ)) = 1 := by
      rw [← NNReal.coe_sum, hq, NNReal.coe_one]
    have hCSq : (∑ c : Fin M, Real.sqrt (q c : ℝ)) ≤
        Real.sqrt (Fintype.card (Fin M) : ℝ) := by
      have h := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset (Fin M)))
        (f := fun c : Fin M => (q c : ℝ)) (g := fun _ => (1 : ℝ))
        (fun c => by positivity) (fun c => by positivity)
      simpa [hqR] using h
    have hstep1 : (∑ c : Fin M, Real.sqrt (2 * ((Λ * q c : ℝ≥0) : ℝ))) =
        Real.sqrt (2 * (Λ : ℝ)) * ∑ c : Fin M, Real.sqrt (q c : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      have hcast : ((Λ * q c : ℝ≥0) : ℝ) = (Λ : ℝ) * (q c : ℝ) := by
        push_cast
        ring
      rw [hcast,
        show 2 * ((Λ : ℝ) * (q c : ℝ)) = (2 * (Λ : ℝ)) * (q c : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
    rw [hstep1]
    calc Real.sqrt (2 * (Λ : ℝ)) * ∑ c : Fin M, Real.sqrt (q c : ℝ)
        ≤ Real.sqrt (2 * (Λ : ℝ)) * Real.sqrt (Fintype.card (Fin M) : ℝ) :=
          mul_le_mul_of_nonneg_left hCSq (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * (Λ : ℝ) * (Fintype.card (Fin M) : ℝ)) := by
          rw [← Real.sqrt_mul (by positivity)]
  change ∫ z : Ω × Ω, F (g z.1, g z.2) ∂(P.prod P) ≤
    Real.sqrt (2 * (Λ : ℝ) * (Fintype.card (Fin M) : ℝ))
  calc ∫ z : Ω × Ω, F (g z.1, g z.2) ∂(P.prod P)
      = ∫ x : Fin M → ℕ × ℕ, (∑ c, |((x c).1 : ℝ) - ((x c).2 : ℝ)|)
          ∂(Measure.pi (fun c => (π c).prod (π c))) := by
        rw [hIntegral, hIntegral2]
    _ ≤ ∑ c : Fin M, Real.sqrt (2 * ((Λ * q c : ℝ≥0) : ℝ)) :=
        integral_sum_abs_sub_poissonPi_le (fun c : Fin M => Λ * q c)
    _ ≤ Real.sqrt (2 * (Λ : ℝ) * (Fintype.card (Fin M) : ℝ)) := hCS

end OTSelector.Probability
