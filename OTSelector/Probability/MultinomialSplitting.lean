import OTSelector.Probability.Dirichlet.CavityWordCount
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Multinomial splitting of independent labels

This file counts words with prescribed letter multiplicities and derives the two splitting laws
used by the finite-volume matching pressure decomposition:

* for `n` independent uniform labels, the vector of label counts has the multinomial law;
* for a Poisson number `N` of labels, independent of the label sequence, the vector of label counts
  has independent Poisson coordinates with rate `Λ / K`.

The fixed-`n` law is proved by pulling the labels back to the product law on words and counting the
words with prescribed counts.  The Poisson law is then obtained by conditioning on `N = n`,
using the fixed-`n` point masses and the Poisson series.  No global measurability of `N` or of the
individual labels is assumed: it follows from the stated distributional hypotheses because
`Measure.map` is zero for non-a.e.-measurable functions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1000000

/-! ## Part A: words with prescribed letter counts -/

/-- The number of words `Fin n → Fin K` whose letter `b` occurs exactly `k b` times is the
multinomial coefficient. -/
theorem card_words_with_counts {n K : ℕ} [NeZero K] (k : Fin K → ℕ)
    (hk : ∑ b, k b = n) :
    Nat.card {w : Fin n → Fin K //
      ∀ b, (Finset.univ.filter fun i => w i = b).card = k b} =
      Nat.multinomial Finset.univ k := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 :=
    ⟨K - 1, (Nat.sub_one_add_one (NeZero.ne K)).symm⟩
  have h := OTSelector.Probability.card_capacityFeasible_eq_multinomial
    (n := K') (K := n) k hk
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun w => by
    simp [OTSelector.CapacityFeasible, Fintype.card_subtype]))

/-! ## The uniform probability measure on a finite type

Mathlib does not provide a measure-level uniform distribution on a finite type, so we define it as
the normalized sum of Dirac masses. -/

/-- The uniform probability measure on a finite type. -/
noncomputable def uniformMeasure (α : Type*) [MeasurableSpace α] [Fintype α] : Measure α :=
  (Fintype.card α : ℝ≥0∞)⁻¹ • ∑ a : α, Measure.dirac a

lemma uniformMeasure_singleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (a : α) :
    uniformMeasure α {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  classical
  rw [uniformMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

lemma uniformMeasure_apply_univ {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] :
    uniformMeasure α Set.univ = 1 := by
  classical
  rw [uniformMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply, Set.indicator_univ, Pi.one_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (by simp)

instance uniformMeasure_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] [Nonempty α] :
    IsProbabilityMeasure (uniformMeasure α) :=
  ⟨uniformMeasure_apply_univ⟩

lemma uniformMeasure_ne_zero {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] :
    uniformMeasure α ≠ 0 :=
  IsProbabilityMeasure.ne_zero (uniformMeasure α)

/-! ## Part B: the fixed-`n` multinomial law -/

/-- The vector of letter counts of a word. -/
def labelCount {n K : ℕ} (w : Fin n → Fin K) : Fin K → ℕ :=
  fun b => (Finset.univ.filter fun i => w i = b).card

/-- The letter counts of a word always sum to its length. -/
lemma sum_labelCount {n K : ℕ} (w : Fin n → Fin K) :
    ∑ b, labelCount w b = n := by
  classical
  simpa [labelCount] using (Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin K)))
    (f := w) (fun _ _ => Finset.mem_univ _)).symm

private lemma pi_uniform_singleton {n K : ℕ} [NeZero K] (ω : Fin n → Fin K) :
    Measure.pi (fun _ : Fin n => uniformMeasure (Fin K)) {ω} =
      ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n := by
  rw [Measure.pi_singleton]
  simp [uniformMeasure_singleton, Finset.prod_const]

private lemma pi_uniform_labelCount {n K : ℕ} [NeZero K] (k : Fin K → ℕ) :
    Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))
        {ω : Fin n → Fin K | labelCount ω = k} =
      (Nat.card {ω : Fin n → Fin K // labelCount ω = k} : ℝ≥0∞) *
        ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n := by
  classical
  set S : Finset (Fin n → Fin K) := Finset.univ.filter (fun ω => labelCount ω = k)
  have hset : {ω : Fin n → Fin K | labelCount ω = k} = (↑S : Set (Fin n → Fin K)) := by
    ext ω; simp [S]
  have hset2 : (↑S : Set (Fin n → Fin K)) = ⋃ p ∈ S, ({p} : Set (Fin n → Fin K)) := by
    ext x; simp
  rw [hset, hset2, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun p _ => pi_uniform_singleton p)]
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro a ha b hb hab
    exact Set.disjoint_singleton.mpr hab
  · intro b hb
    exact measurableSet_singleton b

/-- Point masses of the multinomial law, stated with a.e. measurable labels. -/
theorem map_label_counts_singleton_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n K : ℕ} [NeZero K] (w : Fin n → Ω → Fin K)
    (hw : ∀ i, AEMeasurable (w i) P) (hi : iIndepFun w P)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K)) (k : Fin K → ℕ) :
    P {ξ | labelCount (fun i => w i ξ) = k} =
      if ∑ b, k b = n then
        (Nat.multinomial Finset.univ k : ℝ≥0∞) / (Fintype.card (Fin K) : ℝ≥0∞) ^ n
      else 0 := by
  classical
  let W : Ω → (Fin n → Fin K) := fun ξ i => w i ξ
  have hWae : AEMeasurable W P := aemeasurable_pi_lambda _ hw
  have hjoint : P.map W = Measure.pi (fun _ : Fin n => uniformMeasure (Fin K)) := by
    have h := iIndepFun.map_fun_eq_pi_map (f := w) hw hi
    rw [show (fun i => P.map (w i)) = (fun _ : Fin n => uniformMeasure (Fin K)) from
      funext hlaw] at h
    exact h
  have hSmeas : MeasurableSet {ω : Fin n → Fin K | labelCount ω = k} :=
    (measurableSet_singleton k).preimage (measurable_of_countable _)
  have hpre : {ξ | labelCount (fun i => w i ξ) = k} =
      W ⁻¹' {ω : Fin n → Fin K | labelCount ω = k} := rfl
  rw [hpre, ← Measure.map_apply_of_aemeasurable hWae hSmeas, hjoint, pi_uniform_labelCount]
  rw [Nat.card_eq_fintype_card]
  split_ifs with hk
  · have hcard : Fintype.card {ω : Fin n → Fin K // labelCount ω = k} =
        Nat.multinomial Finset.univ k := by
      rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun ω => funext_iff))]
      rw [← Nat.card_eq_fintype_card]
      exact card_words_with_counts k hk
    rw [hcard, div_eq_mul_inv, ← ENNReal.inv_pow]
  · have hempty : IsEmpty {ω : Fin n → Fin K // labelCount ω = k} :=
      ⟨fun x => hk (by rw [← x.2, sum_labelCount])⟩
    have hzero : Fintype.card {ω : Fin n → Fin K // labelCount ω = k} = 0 :=
      Fintype.card_eq_zero_iff.mpr hempty
    rw [hzero]
    simp

/-- Point masses of the multinomial law for measurable labels. -/
theorem map_label_counts_singleton {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n K : ℕ} [NeZero K] (w : Fin n → Ω → Fin K)
    (hw : ∀ i, Measurable (w i)) (hi : iIndepFun w P)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K)) (k : Fin K → ℕ) :
    P {ξ | labelCount (fun i => w i ξ) = k} =
      if ∑ b, k b = n then
        (Nat.multinomial Finset.univ k : ℝ≥0∞) / (Fintype.card (Fin K) : ℝ≥0∞) ^ n
      else 0 :=
  map_label_counts_singleton_ae w (fun i => (hw i).aemeasurable) hi hlaw k

/-- The full multinomial law.  Since `Fin K → ℕ` is infinite, the sum runs over the subtype of
count vectors with total `n` (equivalently, over the finite support of the law). -/
theorem map_label_counts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n K : ℕ} [NeZero K] (w : Fin n → Ω → Fin K)
    (hw : ∀ i, Measurable (w i)) (hi : iIndepFun w P)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K)) :
    P.map (fun ξ => labelCount (fun i => w i ξ)) =
      Measure.sum (fun k : {k : Fin K → ℕ // ∑ b, k b = n} =>
        ((Nat.multinomial Finset.univ k.1 : ℝ≥0∞) /
          (Fintype.card (Fin K) : ℝ≥0∞) ^ n) • Measure.dirac k.1) := by
  classical
  refine Measure.ext_of_singleton (fun k => ?_)
  have hfae : AEMeasurable (fun ξ => labelCount (fun i => w i ξ)) P :=
    (measurable_of_countable (fun ω : Fin n → Fin K => labelCount ω)).comp_aemeasurable
      (aemeasurable_pi_lambda _ (fun i => (hw i).aemeasurable))
  rw [Measure.map_apply_of_aemeasurable hfae (measurableSet_singleton k)]
  change P {ξ | labelCount (fun i => w i ξ) = k} = _
  rw [map_label_counts_singleton w hw hi hlaw k]
  rw [Measure.sum_apply _ (measurableSet_singleton k)]
  split_ifs with hk
  · rw [tsum_eq_single (⟨k, hk⟩ : {k : Fin K → ℕ // ∑ b, k b = n})]
    · simp [Measure.smul_apply]
    · intro k' hk'
      have hne : k'.1 ≠ k := fun h => hk' (Subtype.ext h)
      simp [Measure.smul_apply, hne]
  · have hzero : ∀ k' : {k : Fin K → ℕ // ∑ b, k b = n},
        (((Nat.multinomial Finset.univ k'.1 : ℝ≥0∞) /
          (Fintype.card (Fin K) : ℝ≥0∞) ^ n) • Measure.dirac k'.1) {k} = 0 := by
      intro k'
      have hne : k'.1 ≠ k := fun h => hk (h ▸ k'.2)
      simp [Measure.smul_apply, hne]
    rw [tsum_congr hzero, tsum_zero]

/-! ## Algebraic identity for the Poisson splitting -/

private lemma poisson_multinomial_real {K : ℕ} [NeZero K] (Λ : ℝ≥0) (k : Fin K → ℕ) :
    Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ (∑ b, k b) /
        ((Nat.factorial (∑ b, k b) : ℕ) : ℝ) *
        ((Nat.multinomial Finset.univ k : ℝ) / (K : ℝ) ^ (∑ b, k b)) =
      ∏ b, Real.exp (-((Λ : ℝ) / (K : ℝ))) *
        ((Λ : ℝ) / (K : ℝ)) ^ k b /
        ((Nat.factorial (k b) : ℕ) : ℝ) := by
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hfac : ∀ b : Fin K, (((Nat.factorial (k b) : ℕ) : ℝ)) ≠ 0 := fun b => by
    rw [Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero _
  have hfacprod : ((∏ b : Fin K, ((Nat.factorial (k b) : ℕ) : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => hfac b)
  have hmult_nat : (∏ b : Fin K, Nat.factorial (k b)) * Nat.multinomial Finset.univ k =
      Nat.factorial (∑ b, k b) := by
    simpa using Nat.multinomial_spec Finset.univ k
  have hmult : (Nat.multinomial Finset.univ k : ℝ) *
      (∏ b : Fin K, ((Nat.factorial (k b) : ℕ) : ℝ)) =
      (((Nat.factorial (∑ b, k b) : ℕ) : ℝ)) := by
    have h := congrArg (fun m : ℕ => (m : ℝ)) hmult_nat
    push_cast at h
    rw [mul_comm] at h
    exact h
  have hmult_div : (Nat.multinomial Finset.univ k : ℝ) =
      (((Nat.factorial (∑ b, k b) : ℕ) : ℝ)) /
        (∏ b : Fin K, ((Nat.factorial (k b) : ℕ) : ℝ)) := by
    rw [eq_div_iff hfacprod]
    exact hmult
  have hexp : Real.exp (-((Λ : ℝ) / (K : ℝ))) ^ K = Real.exp (-(Λ : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hR : (∏ b : Fin K, Real.exp (-((Λ : ℝ) / (K : ℝ))) *
        ((Λ : ℝ) / (K : ℝ)) ^ k b /
        ((Nat.factorial (k b) : ℕ) : ℝ)) =
      Real.exp (-(Λ : ℝ)) * ((Λ : ℝ) / (K : ℝ)) ^ (∑ b, k b) /
        (∏ b : Fin K, ((Nat.factorial (k b) : ℕ) : ℝ)) := by
    rw [Finset.prod_div_distrib]
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, hexp]
  rw [hR, hmult_div]
  rw [div_pow]
  field_simp

private lemma poissonMeasure_singleton_mul_multinomial {K : ℕ} [NeZero K] (Λ : ℝ≥0)
    (k : Fin K → ℕ) :
    poissonMeasure Λ {∑ b, k b} *
        ((Nat.multinomial Finset.univ k : ℝ≥0∞) / (K : ℝ≥0∞) ^ (∑ b, k b)) =
      ∏ b, poissonMeasure (Λ / (K : ℝ≥0)) {k b} := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hcoef : ((Nat.multinomial Finset.univ k : ℝ≥0∞) / (K : ℝ≥0∞) ^ (∑ b, k b)) =
      ENNReal.ofReal ((Nat.multinomial Finset.univ k : ℝ) / (K : ℝ) ^ (∑ b, k b)) := by
    have h1 : ((Nat.multinomial Finset.univ k : ℝ≥0∞)) =
        ENNReal.ofReal (Nat.multinomial Finset.univ k : ℝ) :=
      (ENNReal.ofReal_natCast _).symm
    have h2 : ((K : ℝ≥0∞) ^ (∑ b, k b)) =
        ENNReal.ofReal ((K : ℝ) ^ (∑ b, k b)) := by
      rw [← ENNReal.ofReal_natCast (K), ← ENNReal.ofReal_pow hKpos.le]
    rw [h1, h2, ← ENNReal.ofReal_div_of_pos (pow_pos hKpos _)]
  have hleft : poissonMeasure Λ {∑ b, k b} *
        ((Nat.multinomial Finset.univ k : ℝ≥0∞) / (K : ℝ≥0∞) ^ (∑ b, k b)) =
      ENNReal.ofReal (Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ (∑ b, k b) /
        ((Nat.factorial (∑ b, k b) : ℕ) : ℝ) *
        ((Nat.multinomial Finset.univ k : ℝ) / (K : ℝ) ^ (∑ b, k b))) := by
    rw [poissonMeasure_singleton, hcoef, ← ENNReal.ofReal_mul (by positivity)]
  have hright : (∏ b, poissonMeasure (Λ / (K : ℝ≥0)) {k b}) =
      ENNReal.ofReal (∏ b, Real.exp (-((Λ : ℝ) / (K : ℝ))) *
        ((Λ : ℝ) / (K : ℝ)) ^ k b / ((Nat.factorial (k b) : ℕ) : ℝ)) := by
    calc
      (∏ b, poissonMeasure (Λ / (K : ℝ≥0)) {k b})
          = ∏ b, ENNReal.ofReal (Real.exp (-((Λ : ℝ) / (K : ℝ))) *
              ((Λ : ℝ) / (K : ℝ)) ^ k b / ((Nat.factorial (k b) : ℕ) : ℝ)) := by
            apply Finset.prod_congr rfl
            intro b _
            rw [poissonMeasure_singleton]
            congr 1
      _ = ENNReal.ofReal (∏ b, Real.exp (-((Λ : ℝ) / (K : ℝ))) *
              ((Λ : ℝ) / (K : ℝ)) ^ k b / ((Nat.factorial (k b) : ℕ) : ℝ)) := by
            rw [ENNReal.ofReal_prod_of_nonneg]
            intro b _
            positivity
  rw [hleft, hright, ENNReal.ofReal_eq_ofReal_iff]
  · exact poisson_multinomial_real Λ k
  · positivity
  · positivity

/-! ## Part C: Poisson splitting -/

/-- The vector of letter counts among the first `N ξ` letters. -/
def prefixLabelCount {Ω : Type*} {K : ℕ} (N : Ω → ℕ) (w : ℕ → Ω → Fin K) (ξ : Ω) :
    Fin K → ℕ :=
  fun b => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card

/-- **Poisson splitting of iid uniform labels.**  If `N` is Poisson with rate `Λ` and is
independent of every finite prefix of an iid uniform label sequence, then the count vector of the
first `N` labels has independent Poisson coordinates with rate `Λ / K`. -/
theorem map_poisson_label_counts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K)
    (hN : P.map N = poissonMeasure Λ)
    (hw : ∀ n, iIndepFun (fun i : Fin n => w i) P)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K))
    (hindep : ∀ n, IndepFun N (fun ξ => fun i : Fin n => w i ξ) P) :
    P.map (fun ξ => fun b => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card) =
      Measure.pi (fun _ : Fin K => poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0))) := by
  classical
  have hNae : AEMeasurable N P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hN]
    exact IsProbabilityMeasure.ne_zero (poissonMeasure Λ)
  have hwae : ∀ i : ℕ, AEMeasurable (w i) P := by
    intro i
    apply AEMeasurable.of_map_ne_zero
    rw [hlaw i]
    exact IsProbabilityMeasure.ne_zero (uniformMeasure (Fin K))
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
    ∏ b, poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {k b}
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
          (Nat.multinomial Finset.univ k : ℝ≥0∞) / (Fintype.card (Fin K) : ℝ≥0∞) ^ n
        else 0) := by
    simp only [A]
    rw [(hindep n).measure_inter_preimage_eq_mul {n}
      {ω : Fin n → Fin K | labelCount ω = k} (measurableSet_singleton n) (hSmeas n)]
    congr 1
    · rw [← Measure.map_apply_of_aemeasurable hNae (measurableSet_singleton n), hN]
    · exact map_label_counts_singleton_ae (fun i : Fin n => w i) (fun i => hwae i) (hw n)
        (fun i => hlaw i) k
  rw [hUnion, measure_iUnion₀ hdisj hA_null]
  rw [tsum_eq_single (∑ b, k b)]
  · rw [hA_apply, ite_eq_left rfl]
    simp only [Fintype.card_fin]
    exact poissonMeasure_singleton_mul_multinomial Λ k
  · intro n hn
    rw [hA_apply, ite_eq_right (fun h => hn h.symm)]
    simp

end OTSelector.Probability
