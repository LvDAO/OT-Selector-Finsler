import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.MarkedBlockLaw
import OTSelector.Probability.PoissonLabelSplittingGeneral
import OTSelector.Probability.MarkedTileBlockIdentity
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Poisson thinning for a finite mixture of mark laws

Let `C` be a finite type of labels with weights `w : C → ℝ≥0` summing to one, and
let `α c` be the mark law of label `c`.  The mixture mark law on `C × A` is

`mixtureMarkLaw w α = ∑ c, w c • (α c).map (fun a => (c, a))`.

This file proves the Poisson thinning law for the points of one label: if a marked
Poisson cloud with marks in `C × A` has intensity `r`, then the sub-cloud of the
points whose label is `c`, enumerated in increasing order, is a marked Poisson cloud
with mark law `α c` and intensity `r * w c`.

The thinning statement is proved in the canonical `BlockData` encoding (the count
together with the finite list of selected points), as in `MarkedBlockLaw`.  The
corresponding statement in the infinite-sequence encoding `MarkedCloudSpace` is
obtained by composing with the encoding map `z ↦ ⟨z.1, fun j : Fin z.1 => z.2 j⟩`;
the tail of the infinite sequence beyond the count carries no information and is
not part of the thinning law.

The proof follows the block-splitting development: condition on the label word of
a finite prefix, observe that the label word law factorizes over labels, and that
conditionally on the label word the marks are independent with the label-dependent
laws.  The count of the label `c` is then binomial, and Poissonization turns the
binomial mixture into a Poisson law of rate `r * w c`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {A : Type*} [MeasurableSpace A]

/-! ## The mixture mark law -/

/-- The mixture mark law of a finite family of probability measures with weights
`w`.  A point is `(c, a)` where the label `c` has weight `w c` and, conditionally
on the label, the mark `a` has law `α c`. -/
noncomputable def mixtureMarkLaw {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] (w : C → ℝ≥0)
    (α : C → Measure A) : Measure (C × A) :=
  ∑ c : C, (w c : ℝ≥0∞) • (α c).map (fun a => (c, a))

/-- The total mass of the mixture mark law is the total weight. -/
theorem mixtureMarkLaw_univ {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] (w : C → ℝ≥0)
    (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)] :
    mixtureMarkLaw w α Set.univ = ∑ c : C, (w c : ℝ≥0∞) := by
  classical
  have hterm : ∀ d : C, ((α d).map (fun a => (d, a))) (Set.univ : Set (C × A)) = 1 := by
    intro d
    rw [Measure.map_apply (f := fun a => (d, a)) (measurable_const.prodMk measurable_id) MeasurableSet.univ]
    simp
  rw [mixtureMarkLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, hterm, mul_one]

/-- The mixture mark law is a probability measure when the weights sum to one. -/
theorem mixtureMarkLaw_isProbability {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] (w : C → ℝ≥0)
    (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)]
    (hw : ∑ c, w c = 1) : IsProbabilityMeasure (mixtureMarkLaw w α) :=
  ⟨by
    rw [mixtureMarkLaw_univ w α, ← ENNReal.ofNNReal_finsetSum, hw, ENNReal.coe_one]⟩

/-- **Fiber identity.**  The mass of the points of label `c` whose mark lies in a
measurable set `S` is the weight of `c` times the mark mass `α c S`. -/
theorem mixtureMarkLaw_fiber {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C]
    (w : C → ℝ≥0) (α : C → Measure A) (c : C) {S : Set A} (hS : MeasurableSet S) :
    mixtureMarkLaw w α (Prod.fst ⁻¹' {c} ∩ Prod.snd ⁻¹' S) =
      ENNReal.ofReal (w c) * α c S := by
  classical
  have hT : MeasurableSet
      (Prod.fst ⁻¹' {c} ∩ Prod.snd ⁻¹' S : Set (C × A)) :=
    (measurable_fst (measurableSet_singleton c)).inter (measurable_snd hS)
  have hterm : ∀ d : C,
      ((α d).map (fun a => (d, a))) (Prod.fst ⁻¹' {c} ∩ Prod.snd ⁻¹' S) =
        if d = c then α c S else 0 := by
    intro d
    rw [Measure.map_apply (f := fun a => (d, a)) (measurable_const.prodMk measurable_id) hT]
    by_cases hdc : d = c
    · subst hdc
      have hpre : (fun a => (d, a)) ⁻¹'
          (Prod.fst ⁻¹' {d} ∩ Prod.snd ⁻¹' S : Set (C × A)) = S := by
        ext a
        simp
      rw [hpre]
      simp
    · have hpre : (fun a => (d, a)) ⁻¹'
          (Prod.fst ⁻¹' {c} ∩ Prod.snd ⁻¹' S : Set (C × A)) = ∅ := by
        ext a
        simp [hdc]
      rw [hpre, measure_empty]
      simp [hdc]
  rw [mixtureMarkLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [hterm]
  rw [Finset.sum_eq_single c]
  · simp [ENNReal.ofReal_coe_nnreal]
  · intro d _ hdc
    simp [hdc]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- Fiber identity in product form: the mass of the box `{c} ×ˢ S`. -/
theorem mixtureMarkLaw_prod_singleton {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C]
    (w : C → ℝ≥0) (α : C → Measure A) (c : C) {S : Set A} (hS : MeasurableSet S) :
    mixtureMarkLaw w α ({c} ×ˢ S) = ENNReal.ofReal (w c) * α c S := by
  rw [show ({c} ×ˢ S : Set (C × A)) = Prod.fst ⁻¹' {c} ∩ Prod.snd ⁻¹' S from by
    ext p
    simp]
  exact mixtureMarkLaw_fiber w α c hS

/-- The mass of all points of label `c` is the weight of `c`. -/
theorem mixtureMarkLaw_fst_singleton {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C]
    (w : C → ℝ≥0) (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)] (c : C) :
    mixtureMarkLaw w α (Prod.fst ⁻¹' {c}) = ENNReal.ofReal (w c) := by
  rw [show (Prod.fst ⁻¹' {c} : Set (C × A)) =
      Prod.fst ⁻¹' {c} ∩ Prod.snd ⁻¹' (Set.univ : Set A) from by
    ext p
    simp]
  rw [mixtureMarkLaw_fiber w α c MeasurableSet.univ, measure_univ, mul_one]

/-- The law of the label coordinate under the mixture mark law. -/
theorem mixtureMarkLaw_fst {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C]
    (w : C → ℝ≥0) (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)] :
    (mixtureMarkLaw w α).map Prod.fst =
      ∑ c : C, (w c : ℝ≥0∞) • Measure.dirac c := by
  classical
  rw [mixtureMarkLaw, Measure.map_finset_sum' (f := Prod.fst) measurable_fst.aemeasurable]
  apply Finset.sum_congr rfl
  intro c _
  rw [Measure.map_smul]
  congr 1
  calc ((α c).map (fun a => (c, a))).map Prod.fst
      = (α c).map (Prod.fst ∘ (fun a => (c, a))) := by
        rw [Measure.map_map (g := Prod.fst) (f := fun a => (c, a)) measurable_fst (measurable_const.prodMk measurable_id)]
    _ = (α c).map (fun _ => c) := by rfl
    _ = (α c Set.univ) • Measure.dirac c := Measure.map_const _ _
    _ = Measure.dirac c := by rw [measure_univ, one_smul]

/-- The law of the mark coordinate under the mixture mark law: the mixture of the
mark laws with the same weights. -/
theorem mixtureMarkLaw_snd {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] [DecidableEq C]
    (w : C → ℝ≥0) (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)] :
    (mixtureMarkLaw w α).map Prod.snd = ∑ c : C, (w c : ℝ≥0∞) • α c := by
  classical
  rw [mixtureMarkLaw, Measure.map_finset_sum' (f := Prod.snd) measurable_snd.aemeasurable]
  apply Finset.sum_congr rfl
  intro c _
  rw [Measure.map_smul]
  congr 1
  calc ((α c).map (fun a => (c, a))).map Prod.snd
      = (α c).map (Prod.snd ∘ (fun a => (c, a))) := by
        rw [Measure.map_map (g := Prod.snd) (f := fun a => (c, a)) measurable_snd (measurable_const.prodMk measurable_id)]
    _ = (α c).map id := by rfl
    _ = α c := Measure.map_id


/-! ## Label-dependent weighted splitting of a finite marked sequence -/

section WeightedSplitting

variable {γ Pos : Type*} [Fintype γ] [DecidableEq γ] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [MeasurableSpace Pos]

/-- The joint law of a label and a mark when the mark law depends on the label:
label `d` has weight `p d` and, conditionally on the label, the mark has law `ν d`. -/
noncomputable def mixturePointLaw (p : γ → ℝ≥0) (ν : γ → Measure Pos) :
    Measure (γ × Pos) :=
  ∑ d : γ, (p d : ℝ≥0∞) • (Measure.dirac d).prod (ν d)

/-- The total mass of the label-dependent point law. -/
theorem mixturePointLaw_univ (p : γ → ℝ≥0) (ν : γ → Measure Pos)
    [∀ d, IsProbabilityMeasure (ν d)] :
    mixturePointLaw p ν Set.univ = ∑ d : γ, (p d : ℝ≥0∞) := by
  classical
  have hterm : ∀ d : γ,
      ((Measure.dirac d).prod (ν d)) (Set.univ : Set (γ × Pos)) = 1 := by
    intro d
    rw [show (Set.univ : Set (γ × Pos)) = Set.univ ×ˢ Set.univ from by
      ext q
      simp]
    rw [Measure.prod_prod, measure_univ, measure_univ, mul_one]
  rw [mixturePointLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, hterm, mul_one]

/-- The label-dependent point law is a probability measure when the weights sum to
one. -/
theorem mixturePointLaw_isProbability (p : γ → ℝ≥0) (ν : γ → Measure Pos)
    [∀ d, IsProbabilityMeasure (ν d)] (hp : ∑ d, p d = 1) :
    IsProbabilityMeasure (mixturePointLaw p ν) :=
  ⟨by
    rw [mixturePointLaw_univ p ν, ← ENNReal.ofNNReal_finsetSum, hp, ENNReal.coe_one]⟩

/-- **Factorization of a finite product of label-dependent mixtures.**  The iid
sequence of pairs `(label, mark)` is a mixture, over label words `u`, of the
product laws with deterministic labels `u` and independent marks `ν (u i)`. -/
theorem pi_mixturePointLaw {n : ℕ} (p : γ → ℝ≥0) (ν : γ → Measure Pos)
    [∀ d, IsProbabilityMeasure (ν d)] (hp : ∑ d, p d = 1) :
    Measure.pi (fun _ : Fin n => mixturePointLaw p ν) =
      Measure.sum (fun u : Fin n → γ =>
        (∏ i, (p (u i) : ℝ≥0∞)) •
          Measure.pi (fun i : Fin n => (Measure.dirac (u i)).prod (ν (u i)))) := by
  classical
  haveI : IsProbabilityMeasure (mixturePointLaw p ν) :=
    mixturePointLaw_isProbability p ν hp
  refine Measure.pi_eq ?_
  intro s hs
  rw [Measure.sum_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  rw [tsum_fintype]
  have hprod : (∏ i : Fin n, (mixturePointLaw p ν) (s i)) =
      ∏ i : Fin n, ∑ d : γ, (p d : ℝ≥0∞) * (Measure.dirac d).prod (ν d) (s i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [mixturePointLaw, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
  rw [hprod]
  rw [← Finset.sum_prod_piFinset (s := (Finset.univ : Finset γ))
       (g := fun (i : Fin n) (d : γ) =>
         (p d : ℝ≥0∞) * (Measure.dirac d).prod (ν d) (s i))]
  rw [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.prod_mul_distrib]

/-- The number of occurrences of a label in a word. -/
def labelCountGen {n : ℕ} (u : Fin n → γ) (b : γ) : ℕ :=
  (Finset.univ.filter (fun i => u i = b)).card

/-- The set of positions of a label in a word. -/
def labelPositionsGen {n : ℕ} (u : Fin n → γ) (b : γ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u i = b)

lemma labelCountGen_eq_card_positions {n : ℕ} (u : Fin n → γ) (b : γ) :
    labelCountGen u b = (labelPositionsGen u b).card := rfl

lemma labelCountGen_le {n : ℕ} (u : Fin n → γ) (b : γ) : labelCountGen u b ≤ n := by
  unfold labelCountGen
  simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
    (fun i => u i = b)

/-- The block data of the label `b` among a finite marked word `z : Fin n → γ × Pos`:
the number of positions carrying `b` and the marks at those positions, in order. -/
def blockDataOfPairsGen {n : ℕ} (b : γ) (z : Fin n → γ × Pos) : BlockData Pos :=
  let s := Finset.univ.filter (fun i => (z i).1 = b)
  ⟨s.card, fun j => (z ((s.orderIsoOfFin rfl) j).1).2⟩

/-- The block data of a label among the first `N ξ` points of an infinite marked
sequence. -/
def prefixBlockDataGen {Ω : Type*} (N : Ω → ℕ) (w : ℕ → Ω → γ)
    (x : ℕ → Ω → Pos) (b : γ) (ξ : Ω) : BlockData Pos :=
  let s := Finset.univ.filter (fun i : Fin (N ξ) => w i ξ = b)
  ⟨s.card, fun j => x ((s.orderIsoOfFin rfl) j).1 ξ⟩

/-- The binomial weight of observing `m` points of a label with probability `p`
among `n` points. -/
def binomWeight (n : ℕ) (p : ℝ≥0) (m : ℕ) : ℝ≥0∞ :=
  (n.choose m : ℝ≥0∞) * (p : ℝ≥0∞) ^ m * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ (n - m)

lemma binomWeight_eq_zero_of_lt {n m : ℕ} {p : ℝ≥0} (h : n < m) :
    binomWeight n p m = 0 := by
  unfold binomWeight
  rw [Nat.choose_eq_zero_of_lt h]
  simp

/-! ## The combinatorial weight of one label -/

/-- The product of the two-point weights `a` (for label `0`) and `c` (for label
`1`) over a word is determined by the number of zeros. -/
lemma prod_ite_zero_fin_two {n : ℕ} (v : Fin n → Fin 2) (a c : ℝ≥0∞) :
    (∏ i, (if v i = 0 then a else c)) =
      a ^ labelCountGen v (0 : Fin 2) * c ^ (n - labelCountGen v (0 : Fin 2)) := by
  classical
  rw [Finset.prod_ite]
  rw [Finset.prod_const, Finset.prod_const]
  have hcard : (Finset.univ.filter (fun i : Fin n => ¬ v i = 0)).card =
      n - labelCountGen v (0 : Fin 2) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => v i = 0)
    simp only [Finset.card_univ, Fintype.card_fin, labelCountGen] at h ⊢
    omega
  rw [hcard]
  simp [labelCountGen]

/-- **Weight of the words carrying a prescribed number of a label.**  Summing the
product of the label weights over all words with exactly `m` occurrences of `b`
gives the binomial weight.  The proof projects the label alphabet onto the two
classes `b` and `not b`, for which the sum factorizes over the coordinates. -/
theorem sum_weights_labelCount {n : ℕ} (p : γ → ℝ≥0) (hp : ∑ d, p d = 1)
    (b : γ) (m : ℕ) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin n → γ => labelCountGen u b = m),
        ∏ i, (p (u i) : ℝ≥0∞)) = binomWeight n (p b) m := by
  classical
  let φ : γ → Fin 2 := fun d => if d = b then 0 else 1
  let q : ℝ≥0 := ∑ d ∈ Finset.univ.erase b, p d
  have hpb_le : p b ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ) (f := p)
      (fun i _ => by positivity) (Finset.mem_univ b)
    simpa [hp] using h
  have hsum_erase : p b + q = 1 := by
    have h := Finset.add_sum_erase (s := Finset.univ) (f := p) (Finset.mem_univ b)
    rw [h]
    exact hp
  have hq : q = 1 - p b := by
    rw [eq_comm, tsub_eq_iff_eq_add_of_le hpb_le, add_comm]
    exact hsum_erase.symm
  let s : Finset (Fin n → γ) :=
    Finset.univ.filter (fun u => labelCountGen u b = m)
  let t : Finset (Fin n → Fin 2) :=
    Finset.univ.filter (fun v => labelCountGen v (0 : Fin 2) = m)
  have hcount : ∀ u : Fin n → γ,
      labelCountGen (fun i => φ (u i)) (0 : Fin 2) = labelCountGen u b := by
    intro u
    unfold labelCountGen
    congr 1
    ext i
    simp [φ]
  have hmap : ∀ u ∈ s, (fun i => φ (u i)) ∈ t := by
    intro u hu
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [hcount u, hu]
  rw [show (Finset.univ.filter (fun u : Fin n → γ => labelCountGen u b = m)) = s from rfl]
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (f := fun u : Fin n → γ => ∏ i, (p (u i) : ℝ≥0∞))]
  have hinner : ∀ v : Fin n → Fin 2, labelCountGen v (0 : Fin 2) = m →
      (∑ u ∈ s.filter (fun u => (fun i => φ (u i)) = v),
          ∏ i, (p (u i) : ℝ≥0∞)) =
        ∏ i, (if v i = 0 then (p b : ℝ≥0∞) else (q : ℝ≥0∞)) := by
    intro v hv
    have hfilter : s.filter (fun u => (fun i => φ (u i)) = v) =
        Fintype.piFinset
          (fun i : Fin n => Finset.univ.filter (fun d : γ => φ d = v i)) := by
      ext u
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hfun⟩ i
        exact congrFun hfun i
      · intro hfun
        refine ⟨?_, funext hfun⟩
        rw [← hcount u]
        have hveq : (fun i => φ (u i)) = v := funext hfun
        rw [hveq, hv]
    rw [hfilter]
    rw [← Finset.prod_univ_sum
      (t := fun i : Fin n => Finset.univ.filter (fun d : γ => φ d = v i))
      (f := fun (i : Fin n) (d : γ) => (p d : ℝ≥0∞))]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hvi : v i = 0
    · rw [if_pos hvi]
      have hset : (Finset.univ.filter (fun d : γ => φ d = v i)) = {b} := by
        rw [hvi]
        ext d
        simp [φ]
      rw [hset]
      simp
    · have hvi1 : v i = 1 := Fin.eq_one_of_ne_zero (v i) hvi
      rw [if_neg hvi, hvi1]
      have hset : (Finset.univ.filter (fun d : γ => φ d = (1 : Fin 2))) =
          Finset.univ.erase b := by
        ext d
        simp [φ]
      rw [hset]
      rw [show q = (∑ j ∈ Finset.univ.erase b, p j) from rfl]
      rw [ENNReal.ofNNReal_finsetSum]
  have hstep : (∑ v ∈ t, ∑ u ∈ s.filter (fun u => (fun i => φ (u i)) = v),
        ∏ i, (p (u i) : ℝ≥0∞)) =
      ∑ v ∈ t, ∏ i, (if v i = 0 then (p b : ℝ≥0∞) else (q : ℝ≥0∞)) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact hinner v (Finset.mem_filter.mp hv).2
  rw [hstep]
  have hconst : ∀ v ∈ t,
      (∏ i, (if v i = 0 then (p b : ℝ≥0∞) else (q : ℝ≥0∞))) =
        (p b : ℝ≥0∞) ^ m * (q : ℝ≥0∞) ^ (n - m) := by
    intro v hv
    have hv' : labelCountGen v (0 : Fin 2) = m := (Finset.mem_filter.mp hv).2
    rw [prod_ite_zero_fin_two v (p b : ℝ≥0∞) (q : ℝ≥0∞), hv']
  rw [Finset.sum_congr rfl hconst]
  rw [Finset.sum_const]
  have hcard : (t.card : ℝ≥0∞) = (n.choose m : ℝ≥0∞) := by
    have hcardNat : t.card = Nat.card {v : Fin n → Fin 2 // labelCountGen v (0 : Fin 2) = m} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcardNat]
    rw [show (Nat.card {v : Fin n → Fin 2 // labelCountGen v (0 : Fin 2) = m}) =
        Nat.card {v : Fin n → Fin 2 //
          (Finset.univ.filter (fun i => v i = (0 : Fin 2))).card = m} from rfl]
    rw [card_words_fiber_count (n := n) (K := 2) (b := (0 : Fin 2)) m]
    simp
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, hcard, smul_eq_mul]
  rw [hq]
  rw [binomWeight]
  ring


/-! ## Reindexing a finite product along a finset -/

/-- The first `s.card` coordinates of a finite product, reindexed along `s`, have
the product law of the corresponding factors. -/
lemma map_pi_fiber_general {ι : Type*} [Fintype ι] [LinearOrder ι]
    {α : Type*} [MeasurableSpace α] (ν : ι → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (s : Finset ι) :
    (Measure.pi (fun i : ι => ν i)).map
        (fun y : ι → α => fun j : Fin s.card => y (s.orderIsoOfFin rfl j).1) =
      Measure.pi (fun j : Fin s.card => ν (s.orderIsoOfFin rfl j).1) := by
  classical
  let e : Fin s.card ≃o ↥s := s.orderIsoOfFin rfl
  apply (Measure.pi_eq ?_).symm
  intro A hA
  rw [Measure.map_apply]
  · have hpre : (fun y : ι → α => fun j : Fin s.card => y (e j).1) ⁻¹'
        Set.pi Set.univ A =
        Set.pi Set.univ (fun i : ι => if h : i ∈ s then A (e.symm ⟨i, h⟩) else Set.univ) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h i
        by_cases hi : i ∈ s
        · rw [dite_eq_left hi]
          have := h (e.symm ⟨i, hi⟩)
          simpa using this
        · rw [dite_eq_right hi]
          exact Set.mem_univ _
      · intro h j
        have := h ((e j).1)
        rw [dite_eq_left (e j).2, e.symm_apply_apply] at this
        exact this
    rw [hpre, Measure.pi_pi]
    have hprod : (∏ i : ι, ν i (if h : i ∈ s then A (e.symm ⟨i, h⟩) else Set.univ)) =
        ∏ j : Fin s.card, ν (e j).1 (A j) := by
      have h1 : (∏ i : ι, ν i (if h : i ∈ s then A (e.symm ⟨i, h⟩) else Set.univ)) =
          ∏ i ∈ s, ν i (if h : i ∈ s then A (e.symm ⟨i, h⟩) else Set.univ) := by
        rw [Finset.prod_subset (Finset.subset_univ s)]
        intro x _ hx
        rw [dite_eq_right hx, measure_univ]
      rw [h1, Finset.prod_subtype s (fun x => Iff.rfl)]
      have h2 : ∀ i : ↥s,
          ν (i : ι) (if h : (i : ι) ∈ s then A (e.symm ⟨(i : ι), h⟩) else Set.univ) =
            ν (i : ι) (A (e.symm i)) := by
        intro i
        rw [dite_eq_left i.2]
      simp_rw [h2]
      exact Fintype.prod_equiv e.symm (fun i : ↥s => ν (i : ι) (A (e.symm i)))
        (fun j => ν (e j).1 (A j)) (fun i => by
          show ν (i : ι) (A (e.symm i)) = ν (e (e.symm i)).1 (A (e.symm i))
          rw [e.apply_symm_apply])
    exact hprod
  · exact measurable_pi_lambda _ fun j => measurable_pi_apply _
  · exact MeasurableSet.univ_pi hA

/-! ## Measurability of the block-data map -/

lemma measurable_uFiber_blockData {n : ℕ} (u : Fin n → γ) (b : γ) :
    Measurable (fun y : Fin n → Pos =>
      (⟨(Finset.univ.filter (fun i => u i = b)).card,
        fun j => y (((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl) j).1⟩ :
        BlockData Pos)) := by
  let s := Finset.univ.filter (fun i => u i = b)
  have hproj : Measurable (fun y : Fin n → Pos => fun j : Fin s.card =>
      y ((s.orderIsoOfFin rfl j).1)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  exact (measurable_sigma_mk s.card).comp hproj

lemma measurable_blockDataOfPairsGen {n : ℕ} (b : γ) :
    Measurable (blockDataOfPairsGen (Pos := Pos) (n := n) b) := by
  classical
  let e := MeasurableEquiv.arrowProdEquivProdArrow γ Pos (Fin n)
  have hcomp : Measurable ((blockDataOfPairsGen (Pos := Pos) (n := n) b) ∘ e.symm) := by
    intro S hS
    have hu : ∀ u : Fin n → γ, Measurable (fun y : Fin n → Pos =>
        (⟨(Finset.univ.filter (fun i => u i = b)).card,
          fun j => y (((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl) j).1⟩ :
          BlockData Pos)) := fun u => measurable_uFiber_blockData u b
    have hUnion : ((blockDataOfPairsGen (Pos := Pos) (n := n) b) ∘ e.symm) ⁻¹' S =
        ⋃ u : Fin n → γ, ({u} : Set (Fin n → γ)) ×ˢ
          ((fun y : Fin n → Pos =>
            (⟨(Finset.univ.filter (fun i => u i = b)).card,
              fun j => y (((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl) j).1⟩ :
              BlockData Pos)) ⁻¹' S) := by
      ext p
      constructor
      · intro hp
        change (blockDataOfPairsGen (Pos := Pos) (n := n) b) (e.symm p) ∈ S at hp
        have hval : (blockDataOfPairsGen (Pos := Pos) (n := n) b) (e.symm p) =
            (⟨(Finset.univ.filter (fun i => p.1 i = b)).card,
              fun j => p.2 (((Finset.univ.filter (fun i => p.1 i = b)).orderIsoOfFin rfl) j).1⟩ :
              BlockData Pos) := by
          rfl
        rw [hval] at hp
        exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_prod.mpr ⟨Set.mem_singleton _, hp⟩⟩
      · intro hp
        rcases Set.mem_iUnion.mp hp with ⟨u, hu'⟩
        rcases Set.mem_prod.mp hu' with ⟨hpu, huf⟩
        have hpu_eq : p.1 = u := Set.mem_singleton_iff.mp hpu
        change (blockDataOfPairsGen (Pos := Pos) (n := n) b) (e.symm p) ∈ S
        have hval : (blockDataOfPairsGen (Pos := Pos) (n := n) b) (e.symm p) =
            (⟨(Finset.univ.filter (fun i => p.1 i = b)).card,
              fun j => p.2 (((Finset.univ.filter (fun i => p.1 i = b)).orderIsoOfFin rfl) j).1⟩ :
              BlockData Pos) := by
          rfl
        rw [hval, hpu_eq]
        exact huf
    rw [hUnion]
    exact MeasurableSet.iUnion fun u =>
      MeasurableSet.prod (measurableSet_singleton u) ((hu u) hS)
  have hEq : blockDataOfPairsGen (Pos := Pos) (n := n) b =
      ((blockDataOfPairsGen (Pos := Pos) (n := n) b) ∘ e.symm) ∘ e := by
    funext z
    simp [e]
  rw [hEq]
  exact hcomp.comp e.measurable


/-- **One component of the label-word decomposition.**  Conditionally on a label
word `u`, the block data of `b` consists of the marks at the positions labelled
`b`; those marks are iid with law `ν b`, and their count is the number of
occurrences of `b` in `u`. -/
lemma map_blockDataOfPairsGen_pi_component {n : ℕ} (u : Fin n → γ)
    (ν : γ → Measure Pos) [∀ d, IsProbabilityMeasure (ν d)] (b : γ) :
    (Measure.pi (fun i : Fin n => (Measure.dirac (u i)).prod (ν (u i)))).map
        (blockDataOfPairsGen (Pos := Pos) b) =
      (Measure.pi (fun _ : Fin (labelCountGen u b) => ν b)).map
        (fun y => (⟨labelCountGen u b, y⟩ : BlockData Pos)) := by
  classical
  let s := Finset.univ.filter (fun i : Fin n => u i = b)
  have hs : s.card = labelCountGen u b := rfl
  let Φ : (Fin n → Pos) → (Fin n → γ × Pos) := fun y i => (u i, y i)
  let F : (Fin n → Pos) → (Fin s.card → Pos) := fun y j => y ((s.orderIsoOfFin rfl j).1)
  let H : (Fin s.card → Pos) → BlockData Pos := fun z => ⟨s.card, z⟩
  have hΦ : Measurable Φ :=
    measurable_pi_lambda _ (fun i => measurable_const.prodMk (measurable_pi_apply i))
  have hF : Measurable F := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hH : Measurable H := measurable_sigma_mk s.card
  have hM : (Measure.pi (fun i : Fin n => (Measure.dirac (u i)).prod (ν (u i)))) =
      (Measure.pi (fun i : Fin n => ν (u i))).map Φ := by
    rw [Measure.pi_map_pi (μ := fun i => ν (u i)) (f := fun i z => (u i, z))
      (fun i => (measurable_const.prodMk measurable_id).aemeasurable)]
    congr 1
    funext i
    rw [Measure.dirac_prod]
  have hcomp : blockDataOfPairsGen (Pos := Pos) b ∘ Φ = H ∘ F := by
    funext y
    rfl
  calc
    (Measure.pi (fun i : Fin n => (Measure.dirac (u i)).prod (ν (u i)))).map
        (blockDataOfPairsGen (Pos := Pos) b)
        = ((Measure.pi (fun i : Fin n => ν (u i))).map Φ).map
            (blockDataOfPairsGen (Pos := Pos) b) := by rw [← hM]
    _ = (Measure.pi (fun i : Fin n => ν (u i))).map
          ((blockDataOfPairsGen (Pos := Pos) b) ∘ Φ) := by
        rw [Measure.map_map (measurable_blockDataOfPairsGen b) hΦ]
    _ = (Measure.pi (fun i : Fin n => ν (u i))).map (H ∘ F) := by rw [hcomp]
    _ = ((Measure.pi (fun i : Fin n => ν (u i))).map F).map H := by
        rw [Measure.map_map hH hF]
    _ = (Measure.pi (fun j : Fin s.card => ν (u ((s.orderIsoOfFin rfl j).1)))).map H := by
        rw [map_pi_fiber_general (ν := fun i => ν (u i)) s]
    _ = (Measure.pi (fun _ : Fin s.card => ν b)).map H := by
        have hfam : (fun j : Fin s.card => ν (u ((s.orderIsoOfFin rfl j).1))) =
            fun _ : Fin s.card => ν b := by
          funext j
          congr 1
          exact (Finset.mem_filter.mp (s.orderIsoOfFin rfl j).2).2
        rw [hfam]
    _ = (Measure.pi (fun _ : Fin (labelCountGen u b) => ν b)).map
          (fun y => (⟨labelCountGen u b, y⟩ : BlockData Pos)) := rfl


/-- A finite sum of measures vanishes outside a finset when all summands there
vanish. -/
lemma measure_sum_eq_finset_sum_of_zero {α : Type*} [MeasurableSpace α]
    (f : ℕ → Measure α) (s : Finset ℕ) (h : ∀ m ∉ s, f m = 0) :
    Measure.sum f = ∑ m ∈ s, f m := by
  ext S hS
  rw [Measure.sum_apply _ hS, Measure.finsetSum_apply]
  exact tsum_eq_sum (fun m hm => by rw [h m hm]; simp)

/-- **Fixed-`n` marked splitting for label-dependent mark laws.**  For iid pairs
`(label, mark)` with joint law `mixturePointLaw p ν`, the block data of the label
`b` has law `blockDataLaw (ν b) (binomWeight n (p b))`: its size is binomial with
parameters `(n, p b)` and, conditionally on the size, the marks are iid `ν b`. -/
theorem map_blockDataOfPairsGen_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (w : Fin n → Ω → γ) (x : Fin n → Ω → Pos)
    (hw : ∀ i, Measurable (w i)) (hx : ∀ i, Measurable (x i))
    (hi : iIndepFun (fun i : Fin n => fun ξ => (w i ξ, x i ξ)) P)
    (p : γ → ℝ≥0) (hp : ∑ d, p d = 1)
    (ν : γ → Measure Pos) [∀ d, IsProbabilityMeasure (ν d)]
    (hjointlaw : ∀ i, P.map (fun ξ => (w i ξ, x i ξ)) = mixturePointLaw p ν)
    (b : γ) :
    P.map (fun ξ => blockDataOfPairsGen (Pos := Pos) b
        (fun i : Fin n => (w i ξ, x i ξ))) =
      blockDataLaw (ν b) (fun m => binomWeight n (p b) m) := by
  classical
  let Z : Ω → (Fin n → γ × Pos) := fun ξ i => (w i ξ, x i ξ)
  let G : ℕ → Measure (BlockData Pos) := fun m =>
    (Measure.pi (fun _ : Fin m => ν b)).map (fun y => (⟨m, y⟩ : BlockData Pos))
  have hZmeas : Measurable Z :=
    measurable_pi_lambda _ (fun i => (hw i).prod (hx i))
  have hZ : P.map Z = Measure.pi (fun _ : Fin n => mixturePointLaw p ν) := by
    have hae : ∀ i, AEMeasurable (fun ξ => (w i ξ, x i ξ)) P :=
      fun i => (hw i).prod (hx i) |>.aemeasurable
    have h := iIndepFun.map_fun_eq_pi_map
      (f := fun i : Fin n => fun ξ => (w i ξ, x i ξ)) hae hi
    rwa [show (fun i => P.map (fun ξ => (w i ξ, x i ξ))) =
      (fun _ : Fin n => mixturePointLaw p ν) from funext hjointlaw] at h
  have hmap : P.map (fun ξ => blockDataOfPairsGen (Pos := Pos) b (Z ξ)) =
      (P.map Z).map (blockDataOfPairsGen (Pos := Pos) b) := by
    rw [Measure.map_map (measurable_blockDataOfPairsGen b) hZmeas]
    rfl
  rw [hmap, hZ, pi_mixturePointLaw p ν hp]
  rw [Measure.map_sum (measurable_blockDataOfPairsGen b).aemeasurable]
  simp_rw [Measure.map_smul]
  simp_rw [map_blockDataOfPairsGen_pi_component (ν := ν) (b := b)]
  -- group the label words by the number of occurrences of `b`
  rw [Measure.sum_fintype]
  have hmem : ∀ u ∈ (Finset.univ : Finset (Fin n → γ)),
      labelCountGen u b ∈ Finset.range (n + 1) := by
    intro u _
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (labelCountGen_le u b)
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin n → γ)))
    (t := Finset.range (n + 1))
    (g := fun u => labelCountGen u b)
    (f := fun u => (∏ i, (p (u i) : ℝ≥0∞)) • G (labelCountGen u b)) hmem]
  have hinner : ∀ m : ℕ,
      (∑ u ∈ Finset.univ.filter (fun u : Fin n → γ => labelCountGen u b = m),
        (∏ i, (p (u i) : ℝ≥0∞)) • G (labelCountGen u b)) =
      (∑ u ∈ Finset.univ.filter (fun u : Fin n → γ => labelCountGen u b = m),
        ∏ i, (p (u i) : ℝ≥0∞)) • G m := by
    intro m
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro u hu
    rw [(Finset.mem_filter.mp hu).2]
  simp_rw [hinner]
  simp_rw [sum_weights_labelCount (p := p) hp b]
  rw [blockDataLaw,
    measure_sum_eq_finset_sum_of_zero (f := fun m => binomWeight n (p b) m • G m)
      (s := Finset.range (n + 1)) (by
        intro m hm
        rw [Finset.mem_range, not_lt] at hm
        rw [binomWeight_eq_zero_of_lt hm, zero_smul])]


/-! ## Poissonization -/

/-- A shifted `tsum` in `ℝ≥0∞` when the initial terms vanish. -/
lemma tsum_shift_of_zero {f : ℕ → ℝ≥0∞} {m : ℕ} (hf : ∀ n < m, f n = 0) :
    (∑' n, f n) = ∑' j, f (m + j) := by
  have hN : Tendsto (fun j : ℕ => m + j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat m
  rw [ENNReal.tsum_eq_iSup_nat' (N := fun j : ℕ => m + j) hN]
  rw [ENNReal.tsum_eq_iSup_nat]
  congr 1
  funext j
  rw [Finset.sum_range_add]
  have hzero : (∑ i ∈ Finset.range m, f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hf i (Finset.mem_range.mp hi)
  rw [hzero, zero_add]

/-- The total mass of the Poisson law, summed over its atoms. -/
lemma poisson_tsum_singleton (r : ℝ≥0) :
    (∑' n, poissonMeasure r {n}) = 1 := by
  calc
    (∑' n, poissonMeasure r {n})
        = ∑' n, ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) ) := by
          simp_rw [poissonMeasure_singleton]
    _ = ENNReal.ofReal (∑' n, Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) ) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            (hasSum_one_poissonMeasure r).summable]
    _ = ENNReal.ofReal 1 := by rw [(hasSum_one_poissonMeasure r).tsum_eq]
    _ = 1 := ENNReal.ofReal_one

/-- **Poisson mixing of the binomial weights.**  Summing the binomial weight of
observing `m` successes among `n` Bernoulli(`p`) trials against the Poisson law of
rate `Λ` gives the Poisson mass of `m` at rate `Λ * p`. -/
lemma poisson_mix_binom (Λ p : ℝ≥0) (hp : p ≤ 1) (m : ℕ) :
    (∑' n, poissonMeasure Λ {n} * binomWeight n p m) =
      poissonMeasure (Λ * p) {m} := by
  classical
  let q : ℝ≥0 := 1 - p
  have hpq : p + q = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hp
  let p2 : Fin 2 → ℝ≥0 := fun e => if e = 0 then p else q
  have hp2 : ∑ e : Fin 2, p2 e = 1 := by
    rw [Fin.sum_univ_two]
    simp [p2, hpq]
  have hstep : ∀ j : ℕ,
      poissonMeasure Λ {m + j} * binomWeight (m + j) p m =
        poissonMeasure (Λ * p) {m} * poissonMeasure (Λ * q) {j} := by
    intro j
    let k : Fin 2 → ℕ := fun e => if e = 0 then m else j
    have hk0 : k 0 = m := by simp [k]
    have hk1 : k 1 = j := by simp [k]
    have hsumk : ∑ e : Fin 2, k e = m + j := by
      rw [Fin.sum_univ_two, hk0, hk1]
    have hprod : (∏ e : Fin 2, (p2 e : ℝ≥0∞) ^ k e) =
        (p : ℝ≥0∞) ^ m * (q : ℝ≥0∞) ^ j := by
      rw [Fin.prod_univ_two]
      simp [p2, k, hk0, hk1]
    have hmult : (Nat.multinomial Finset.univ k : ℝ≥0∞) =
        ((m + j).choose m : ℝ≥0∞) := by
      rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
      rw [Nat.binomial_eq_choose (by decide)]
      simp [k, hk0, hk1]
    have hrhs : (∏ e : Fin 2, poissonMeasure (Λ * p2 e) {k e}) =
        poissonMeasure (Λ * p) {m} * poissonMeasure (Λ * q) {j} := by
      rw [Fin.prod_univ_two]
      simp [p2, k, hk0, hk1]
    have h := poissonMeasure_singleton_mul_weighted_multinomial Λ p2 hp2 k
    rw [hsumk, hprod, hmult, hrhs] at h
    rw [binomWeight]
    rw [show m + j - m = j from Nat.add_sub_cancel_left m j]
    convert h using 1 <;> ring
  calc
    (∑' n, poissonMeasure Λ {n} * binomWeight n p m)
        = ∑' j, poissonMeasure Λ {m + j} * binomWeight (m + j) p m := by
          apply tsum_shift_of_zero
          intro n hn
          rw [binomWeight_eq_zero_of_lt hn, mul_zero]
    _ = ∑' j, poissonMeasure (Λ * p) {m} * poissonMeasure (Λ * q) {j} :=
          tsum_congr hstep
    _ = poissonMeasure (Λ * p) {m} * ∑' j, poissonMeasure (Λ * q) {j} := by
          rw [ENNReal.tsum_mul_left]
    _ = poissonMeasure (Λ * p) {m} * 1 := by rw [poisson_tsum_singleton]
    _ = poissonMeasure (Λ * p) {m} := mul_one _


/-- An independently counted prefix has the exact mixture of its finite-prefix
laws with the original count distribution. -/
lemma map_count_prefix_gen
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : Measure ℕ) [IsProbabilityMeasure κ] (N : Ω → ℕ) (Y : ∀ _n, Ω → β)
    (hN : P.map N = κ)
    (hY : ∀ n, Measurable (Y n))
    (hindep : ∀ n, IndepFun N (Y n) P) :
    P.map (fun ξ => Y (N ξ) ξ) =
      Measure.sum (fun n => κ {n} • P.map (Y n)) := by
  classical
  have hNae : AEMeasurable N P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hN]
    exact IsProbabilityMeasure.ne_zero κ
  have hmkN : Measurable (hNae.mk N) := hNae.measurable_mk
  have hYjoint : Measurable (fun p : ℕ × Ω => Y p.1 p.2) := by
    intro T hT
    have hpre : (fun p : ℕ × Ω => Y p.1 p.2) ⁻¹' T =
        ⋃ n, ({n} : Set ℕ) ×ˢ (Y n ⁻¹' T) := by
      ext p
      simp
    rw [hpre]
    exact MeasurableSet.iUnion (fun n =>
      MeasurableSet.prod (measurableSet_singleton n) (hY n hT))
  have hYmk_meas : Measurable (fun ξ => Y (hNae.mk N ξ) ξ) := by
    have hpair : Measurable (fun ξ : Ω => (hNae.mk N ξ, ξ)) := hmkN.prod measurable_id
    simpa only [Function.comp_def] using hYjoint.comp hpair
  have hYmk_ae : (fun ξ => Y (N ξ) ξ) =ᵐ[P] (fun ξ => Y (hNae.mk N ξ) ξ) := by
    filter_upwards [hNae.ae_eq_mk] with ξ hξ
    rw [hξ]
  have hYae : AEMeasurable (fun ξ => Y (N ξ) ξ) P :=
    hYmk_meas.aemeasurable.congr hYmk_ae.symm
  ext S hS
  rw [Measure.map_apply_of_aemeasurable hYae hS]
  have hUnion : (fun ξ => Y (N ξ) ξ) ⁻¹' S =
      ⋃ n, (N ⁻¹' {n}) ∩ (Y n ⁻¹' S) := by
    ext ξ
    simp
  have hNull (n : ℕ) : NullMeasurableSet ((N ⁻¹' {n}) ∩ (Y n ⁻¹' S)) P := by
    apply NullMeasurableSet.inter
    · exact hNae.nullMeasurableSet_preimage (measurableSet_singleton n)
    · exact (hY n hS).nullMeasurableSet
  have hdisj : Pairwise (Function.onFun (AEDisjoint P)
      (fun n => (N ⁻¹' {n}) ∩ (Y n ⁻¹' S))) := by
    intro m n hmn
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro ξ hξm hξn
    exact hmn (hξm.1.symm.trans hξn.1)
  rw [hUnion, measure_iUnion₀ hdisj hNull]
  have hterm (n : ℕ) : P ((N ⁻¹' {n}) ∩ (Y n ⁻¹' S)) =
      κ {n} * (P.map (Y n)) S := by
    rw [(hindep n).measure_inter_preimage_eq_mul {n} S
      (measurableSet_singleton n) hS]
    congr 1
    · rw [← Measure.map_apply_of_aemeasurable hNae (measurableSet_singleton n), hN]
    · rw [Measure.map_apply_of_aemeasurable (hY n).aemeasurable hS]
  simp_rw [hterm]
  rw [Measure.sum_apply _ hS]
  simp_rw [Measure.smul_apply, smul_eq_mul]

/-- The Poisson specialization keeps the original prefix-law API. -/
lemma map_poisson_prefix_gen
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Λ : ℝ≥0) (N : Ω → ℕ) (Y : ∀ _n, Ω → β)
    (hN : P.map N = poissonMeasure Λ)
    (hY : ∀ n, Measurable (Y n))
    (hindep : ∀ n, IndepFun N (Y n) P) :
    P.map (fun ξ => Y (N ξ) ξ) =
      Measure.sum (fun n => poissonMeasure Λ {n} • P.map (Y n)) := by
  exact map_count_prefix_gen (poissonMeasure Λ) N Y hN hY hindep

/-- A mixture of original finite block laws has the exactly mixed count weights.
The identity requires no limiting approximation of either count distribution. -/
lemma blockDataLaw_mix_gen {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (weight target : ℕ → ℝ≥0∞)
    (prob : ℕ → ℕ → ℝ≥0∞)
    (hthin : ∀ m, (∑' n, weight n * prob n m) =
      target m) :
    Measure.sum (fun n => weight n • blockDataLaw ν (prob n)) =
      blockDataLaw ν (fun m => target m) := by
  classical
  let G : ℕ → Measure (BlockData Pos) := fun m =>
    (Measure.pi (fun _ : Fin m => ν)).map (fun y => (⟨m, y⟩ : BlockData Pos))
  have hBD : ∀ (prob' : ℕ → ℝ≥0∞) (S : Set (BlockData Pos)), MeasurableSet S →
      (blockDataLaw ν prob') S = ∑' m, prob' m * G m S := by
    intro prob' S hS
    rw [blockDataLaw, Measure.sum_apply _ hS]
    simp_rw [Measure.smul_apply, smul_eq_mul]
    simp only [G]
  ext S hS
  rw [Measure.sum_apply _ hS]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  have hval (n : ℕ) : (blockDataLaw ν (prob n)) S =
      ∑' m, prob n m * G m S := hBD (prob n) S hS
  simp_rw [hval]
  rw [hBD (fun m => target m) S hS]
  calc
    (∑' n, weight n * (∑' m, prob n m * G m S))
        = ∑' n, ∑' m, weight n * (prob n m * G m S) := by
          congr 1 with n
          rw [ENNReal.tsum_mul_left]
    _ = ∑' m, ∑' n, weight n * (prob n m * G m S) :=
          ENNReal.tsum_comm
    _ = ∑' m, (∑' n, weight n * prob n m) * G m S := by
          congr 1 with m
          rw [← ENNReal.tsum_mul_right]
          congr 1 with n
          ring
    _ = ∑' m, target m * G m S := by
          congr 1 with m
          rw [hthin m]


/-- The Poisson specialization of the general exact mixture identity. -/
lemma blockDataLaw_poisson_mix_gen {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (Λ c : ℝ≥0)
    (prob : ℕ → ℕ → ℝ≥0∞)
    (hthin : ∀ m, (∑' n, poissonMeasure Λ {n} * prob n m) =
      poissonMeasure c {m}) :
    Measure.sum (fun n => poissonMeasure Λ {n} • blockDataLaw ν (prob n)) =
      blockDataLaw ν (fun m => poissonMeasure c {m}) := by
  exact blockDataLaw_mix_gen ν (fun n ↦ poissonMeasure Λ {n})
    (fun m ↦ poissonMeasure c {m}) prob hthin

/-- **Poisson marked splitting for label-dependent mark laws.**  Let `N` be
Poisson with rate `Λ`, independent of every finite prefix of an iid sequence of
pairs `(label, mark)` with joint law `mixturePointLaw p ν`.  Then the block data
of the label `b` has law `blockDataLaw (ν b)` with Poisson size of rate
`Λ * p b`: the size is Poisson and, conditionally on it, the marks are iid
`ν b`. -/
theorem map_poisson_blockDataOfPairsGen
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → γ) (x : ℕ → Ω → Pos)
    (p : γ → ℝ≥0) (hp : ∑ d, p d = 1)
    (ν : γ → Measure Pos) [∀ d, IsProbabilityMeasure (ν d)]
    (hN : P.map N = poissonMeasure Λ)
    (hpair : ∀ n, iIndepFun (fun i : Fin n => fun ξ => (w i ξ, x i ξ)) P)
    (hw : ∀ i, Measurable (w i)) (hx : ∀ i, Measurable (x i))
    (hjointlaw : ∀ i, P.map (fun ξ => (w i ξ, x i ξ)) = mixturePointLaw p ν)
    (hindep : ∀ n, IndepFun N (fun ξ => fun i : Fin n => (w i ξ, x i ξ)) P)
    (b : γ) :
    P.map (prefixBlockDataGen (Pos := Pos) N w x b) =
      blockDataLaw (ν b) (fun m => poissonMeasure (Λ * p b) {m}) := by
  classical
  let Y : ∀ n, Ω → BlockData Pos := fun n ξ =>
    blockDataOfPairsGen (Pos := Pos) b (fun i : Fin n => (w i ξ, x i ξ))
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    exact (measurable_blockDataOfPairsGen (Pos := Pos) b).comp
      (measurable_pi_lambda _ (fun i => (hw i).prod (hx i)))
  have hindepY : ∀ n, IndepFun N (Y n) P := by
    intro n
    have h := (hindep n).comp measurable_id
      (measurable_blockDataOfPairsGen (Pos := Pos) b)
    simpa [Function.comp_def, id_eq, Y] using h
  have hpoisson := map_poisson_prefix_gen Λ N Y hN hY hindepY
  have hYlaw : ∀ n, P.map (Y n) =
      blockDataLaw (ν b) (fun m => binomWeight n (p b) m) := by
    intro n
    have h := map_blockDataOfPairsGen_law
      (w := fun i : Fin n => w i) (x := fun i : Fin n => x i)
      (fun i => hw i) (fun i => hx i) (hpair n) p hp ν
      (fun i => hjointlaw (i : ℕ)) b
    have hfun : (fun ξ => blockDataOfPairsGen (Pos := Pos) b
        (fun i : Fin n => (w i ξ, x i ξ))) = Y n := by
      funext ξ
      rfl
    rw [← hfun]
    exact h
  rw [show (fun ξ => Y (N ξ) ξ) = prefixBlockDataGen (Pos := Pos) N w x b from rfl]
    at hpoisson
  simp_rw [hYlaw] at hpoisson
  have hpb_le : p b ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ) (f := p)
      (fun i _ => by positivity) (Finset.mem_univ b)
    simpa [hp] using h
  rw [hpoisson]
  exact blockDataLaw_poisson_mix_gen (ν b) Λ (Λ * p b)
    (fun n m => binomWeight n (p b) m)
    (fun m => poisson_mix_binom Λ (p b) hpb_le m)

end WeightedSplitting

/-! ## The canonical block-data encoding of a marked cloud -/

/-- The canonical `BlockData` encoding of a marked cloud: its count and the used
prefix of its points.  The tail of the infinite sequence is discarded. -/
noncomputable def cloudEncode {q : ℕ} {A : Type*} (z : MarkedCloudSpace q A) :
    BlockData ((Fin q → ℝ) × A) :=
  ⟨z.1, fun j => z.2 j⟩

theorem measurable_cloudEncode {q : ℕ} {A : Type*} [MeasurableSpace A] :
    Measurable (cloudEncode (q := q) (A := A)) := by
  classical
  intro S hS
  have hpre : cloudEncode (q := q) (A := A) ⁻¹' S =
      ⋃ n : ℕ, (Prod.fst ⁻¹' {n}) ∩
        (Prod.snd ⁻¹' ((fun y : ℕ → (Fin q → ℝ) × A =>
          (⟨n, fun j : Fin n => y j⟩ : BlockData ((Fin q → ℝ) × A))) ⁻¹' S)) := by
    ext z
    constructor
    · intro hz
      refine Set.mem_iUnion.mpr ⟨z.1, ?_⟩
      exact ⟨rfl, hz⟩
    · intro hz
      obtain ⟨n, hn, hzS⟩ := Set.mem_iUnion.mp hz
      have h1 : z.1 = n := hn
      subst h1
      exact hzS
  rw [hpre]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact measurable_fst (measurableSet_singleton n)
  · refine measurable_snd ?_
    exact ((measurable_sigma_mk (β := fun m => Fin m → ((Fin q → ℝ) × A)) n).comp
      (measurable_pi_lambda (fun (y : ℕ → (Fin q → ℝ) × A) (j : Fin n) => y j)
        (fun j => measurable_pi_apply (j : ℕ)))) hS

/-- The label/mark reorganization of a marked sequence used for thinning: each
point is replaced by `(label, (position, mark))`. -/
noncomputable def cloudEncodePairs {q : ℕ} {C A : Type*} (z : MarkedCloudSpace q (C × A)) :
    BlockData (C × ((Fin q → ℝ) × A)) :=
  ⟨z.1, fun j => ((z.2 j).2.1, ((z.2 j).1, (z.2 j).2.2))⟩

theorem measurable_cloudEncodePairs {q : ℕ} {C A : Type*} [MeasurableSpace C]
    [MeasurableSpace A] :
    Measurable (cloudEncodePairs (q := q) (C := C) (A := A)) := by
  classical
  have hpt : Measurable (fun p : (Fin q → ℝ) × (C × A) =>
      (p.2.1, (p.1, p.2.2))) := by fun_prop
  let Φ : ℕ → (ℕ → (Fin q → ℝ) × (C × A)) → BlockData (C × ((Fin q → ℝ) × A)) :=
    fun n y => (⟨n, fun j : Fin n => (fun p : (Fin q → ℝ) × (C × A) =>
      (p.2.1, (p.1, p.2.2))) (y j)⟩ : BlockData (C × ((Fin q → ℝ) × A)))
  have hΦ : ∀ n, Measurable (Φ n) := by
    intro n
    exact (measurable_sigma_mk (β := fun m => Fin m → (C × ((Fin q → ℝ) × A))) n).comp
      (measurable_pi_lambda (fun (y : ℕ → (Fin q → ℝ) × (C × A)) (j : Fin n) =>
          (fun p : (Fin q → ℝ) × (C × A) => (p.2.1, (p.1, p.2.2))) (y j))
        (fun j => hpt.comp (measurable_pi_apply (j : ℕ))))
  intro S hS
  have hpre : cloudEncodePairs (q := q) (C := C) (A := A) ⁻¹' S =
      Set.iUnion (fun n : ℕ =>
        (Prod.fst ⁻¹' {n}) ∩ (Prod.snd ⁻¹' (Φ n ⁻¹' S))) := by
    ext z
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨z.1, rfl, hz⟩
    · intro hz
      obtain ⟨n, hn, hzS⟩ := Set.mem_iUnion.mp hz
      have h1 : z.1 = n := hn
      subst h1
      exact hzS
  rw [hpre]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact measurable_fst (measurableSet_singleton n)
  · exact measurable_snd ((hΦ n) hS)

/-- The block data of a label `c` in a `BlockData`-encoded marked word. -/
noncomputable def blockDataLabelCloud {γ Pos : Type*} [DecidableEq γ] (c : γ)
    (d : BlockData (γ × Pos)) : BlockData Pos :=
  blockDataOfPairsGen (Pos := Pos) c d.2

lemma measurableSet_sigmaMk_image {γ Pos : Type*} [MeasurableSpace γ] [MeasurableSpace Pos]
    {n : ℕ} {T : Set (Fin n → γ × Pos)} (hT : MeasurableSet T) :
    MeasurableSet (Sigma.mk n '' T : Set (BlockData (γ × Pos))) := by
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  by_cases han : a = n
  · subst han
    have hpre : (fun y : Fin a → γ × Pos => (⟨a, y⟩ : BlockData (γ × Pos))) ⁻¹'
        (Sigma.mk a '' T) = T := by
      ext y
      constructor
      · rintro ⟨y', hy', heq⟩
        rw [Sigma.mk.injEq] at heq
        obtain ⟨-, h2⟩ := heq
        rwa [eq_of_heq h2] at hy'
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [hpre]
    exact hT
  · have hpre : (fun y : Fin a → γ × Pos => (⟨a, y⟩ : BlockData (γ × Pos))) ⁻¹'
        (Sigma.mk n '' T) = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false,
        not_exists, not_and]
      rintro y' _ heq
      rw [Sigma.mk.injEq] at heq
      exact han heq.1.symm
    rw [hpre]
    exact MeasurableSet.empty

theorem measurable_blockDataLabelCloud {γ Pos : Type*} [Fintype γ] [DecidableEq γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace Pos] (c : γ) :
    Measurable (blockDataLabelCloud (Pos := Pos) c) := by
  classical
  intro S hS
  have hUnion : (blockDataLabelCloud (Pos := Pos) c) ⁻¹' S =
      ⋃ n : ℕ, Sigma.mk n '' ((fun y : Fin n → γ × Pos =>
        blockDataOfPairsGen (Pos := Pos) c y) ⁻¹' S) := by
    ext d
    rw [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hd
      refine ⟨d.1, ?_⟩
      rw [Set.mem_image]
      exact ⟨d.2, hd, rfl⟩
    · rintro ⟨n, hdn⟩
      rw [Set.mem_image] at hdn
      obtain ⟨y, hy, hd⟩ := hdn
      rw [← hd]
      exact hy
  rw [hUnion]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_sigmaMk_image ((measurable_blockDataOfPairsGen (n := n) c) hS)

/-- The encoded label cloud of `labelCloud c z` is the block data of the label
`c` among the points of `z`. -/
lemma cloudEncode_labelCloud_eq {q : ℕ} {C A : Type*} [DecidableEq C] (c : C)
    (z : MarkedCloudSpace q (C × A)) :
    cloudEncode (labelCloud c z) =
      blockDataOfPairsGen (Pos := (Fin q → ℝ) × A) c
        (fun i : Fin z.1 => ((z.2 i).2.1, ((z.2 i).1, (z.2 i).2.2))) := by
  classical
  unfold cloudEncode labelCloud blockDataOfPairsGen labelFilter
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext j
    simp only [dif_pos j.isLt]

theorem measurable_cloudEncode_labelCloud {q : ℕ} {C A : Type*} [Fintype C]
    [DecidableEq C] [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace A]
    (c : C) :
    Measurable (fun z : MarkedCloudSpace q (C × A) => cloudEncode (labelCloud c z)) := by
  classical
  have hfun : (fun z : MarkedCloudSpace q (C × A) => cloudEncode (labelCloud c z)) =
      (blockDataLabelCloud (Pos := (Fin q → ℝ) × A) c) ∘ cloudEncodePairs := by
    funext z
    exact cloudEncode_labelCloud_eq c z
  rw [hfun]
  exact (measurable_blockDataLabelCloud (Pos := (Fin q → ℝ) × A) c).comp
    (measurable_cloudEncodePairs (q := q) (C := C) (A := A))

theorem aemeasurable_cloudEncode_labelCloud
    (q : ℕ) {C A : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableSpace A]
    (α : Measure (C × A)) [IsProbabilityMeasure α] (r : ℝ≥0) (c : C) :
    AEMeasurable (fun z : MarkedCloudSpace q (C × A) =>
      cloudEncode (labelCloud c z)) (markedPoissonLaw q (C × A) α r) :=
  (measurable_cloudEncode_labelCloud (q := q) (C := C) (A := A) c).aemeasurable



/-! ## The encoded thinning law for the marked Poisson cloud -/

/-- Pushing a measure forward along `p ↦ (c, p)` gives the product with a Dirac
mass at `c`. -/
theorem map_prodMk_const {C P : Type*} [MeasurableSpace C] [MeasurableSpace P]
    (ρ : Measure P) [SigmaFinite ρ] (c : C) :
    ρ.map (fun p : P => (c, p)) = (Measure.dirac c).prod ρ := by
  classical
  refine (Measure.prod_eq (μ := Measure.dirac c) (ν := ρ)
    (μν := ρ.map (fun p : P => (c, p))) ?_).symm
  intro s t hs ht
  rw [Measure.map_apply measurable_prodMk_left (hs.prod ht)]
  have hpre : (fun p : P => (c, p)) ⁻¹' (s ×ˢ t) = if c ∈ s then t else ∅ := by
    ext p
    by_cases hc : c ∈ s <;> simp [hc]
  rw [hpre, Measure.dirac_apply' c hs]
  by_cases hc : c ∈ s <;> simp [hc]

/-- A finite sum of s-finite measures is s-finite. -/
theorem sFinite_finsetSum_measure {ι β : Type*} [MeasurableSpace β] (s : Finset ι)
    (ν : ι → Measure β) [∀ i, SFinite (ν i)] : SFinite (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (inferInstance : SFinite (0 : Measure β))
  | insert a s ha ih => rw [Finset.sum_insert ha]; infer_instance

/-- The product of a measure with a finite sum of measures is the finite sum of
the products. -/
theorem prod_finsetSum_measure {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (s : Finset ι) (ν : ι → Measure β) [∀ i, SFinite (ν i)] :
    μ.prod (∑ i ∈ s, ν i) = ∑ i ∈ s, μ.prod (ν i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Measure.prod_zero]
  | insert a s ha ih =>
      haveI hs : SFinite (∑ i ∈ s, ν i) := sFinite_finsetSum_measure s ν
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.prod_add, ih]

set_option maxHeartbeats 1000000 in
/-- **The one-point law of the mixture mark measure.**  A uniform position and a
mark with law `mixtureMarkLaw w α` give, after reorganizing the coordinates, a
label with weight `w` and a label-dependent mark law `cube × α c`. -/
theorem map_onePoint_mixtureMarkLaw
    (q : ℕ) {C A : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableSpace A]
    (w : C → ℝ≥0) (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)] :
    ((cubeMeasure (Fin q) 1).prod (mixtureMarkLaw w α)).map
      (fun p : (Fin q → ℝ) × (C × A) => ((p.2).1, (p.1, (p.2).2))) =
    mixturePointLaw w (fun c => (cubeMeasure (Fin q) 1).prod (α c)) := by
  classical
  haveI hcube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have hF : Measurable (fun p : (Fin q → ℝ) × (C × A) =>
      ((p.2).1, (p.1, (p.2).2))) := by fun_prop
  rw [mixtureMarkLaw, prod_finsetSum_measure (cubeMeasure (Fin q) 1) Finset.univ
    (fun c : C => (w c : ℝ≥0∞) • (α c).map (fun a => (c, a)))]
  rw [Measure.map_finset_sum' hF.aemeasurable]
  rw [mixturePointLaw]
  apply Finset.sum_congr rfl
  intro c _
  rw [Measure.prod_smul_right, Measure.map_smul]
  congr 1
  have hg : Measurable (fun a : A => (c, a)) := measurable_const.prodMk measurable_id
  have hmap := Measure.map_prod_map (cubeMeasure (Fin q) 1) (α c)
    (measurable_id : Measurable (id : (Fin q → ℝ) → (Fin q → ℝ))) hg
  have hmap' : (cubeMeasure (Fin q) 1).prod ((α c).map (fun a => (c, a))) =
      Measure.map (Prod.map id (fun a => (c, a))) ((cubeMeasure (Fin q) 1).prod (α c)) := by
    simpa only [Measure.map_id] using hmap
  rw [hmap']
  rw [Measure.map_map hF (measurable_id.prodMap hg)]
  have hcomp : ((fun p : (Fin q → ℝ) × (C × A) =>
        ((p.2).1, (p.1, (p.2).2))) ∘ Prod.map id (fun a : A => (c, a))) =
      fun p : (Fin q → ℝ) × A => (c, p) := by
    funext p
    simp
  rw [hcomp]
  exact map_prodMk_const ((cubeMeasure (Fin q) 1).prod (α c)) c

/-- **The one-point law of a marked Poisson cloud.**  The joint law of the label
and the reorganized point `(position, mark)` of any index is the pushed-forward
one-point law of the marked cube. -/
theorem map_markedPair_law
    (q : ℕ) {C A : Type*} [MeasurableSpace C] [MeasurableSpace A]
    (α : Measure (C × A)) [IsProbabilityMeasure α] (r : ℝ≥0) (i : ℕ) :
    (markedPoissonLaw q (C × A) α r).map
        (fun z : MarkedCloudSpace q (C × A) =>
          ((z.2 i).2.1, ((z.2 i).1, (z.2 i).2.2))) =
      ((cubeMeasure (Fin q) 1).prod α).map
        (fun p : (Fin q → ℝ) × (C × A) => ((p.2).1, (p.1, (p.2).2))) := by
  classical
  have hpt : Measurable (fun p : (Fin q → ℝ) × (C × A) =>
      ((p.2).1, (p.1, (p.2).2))) := by fun_prop
  have hseq : Measurable (fun s : ℕ → (Fin q → ℝ) × (C × A) =>
      ((s i).2.1, ((s i).1, (s i).2.2))) :=
    hpt.comp (measurable_pi_apply i)
  rw [markedPoissonLaw]
  rw [show (fun z : MarkedCloudSpace q (C × A) =>
      ((z.2 i).2.1, ((z.2 i).1, (z.2 i).2.2))) =
      (fun s : ℕ → (Fin q → ℝ) × (C × A) =>
        ((s i).2.1, ((s i).1, (s i).2.2))) ∘ Prod.snd from rfl]
  rw [← Measure.map_map hseq measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  rw [markedSeqLaw]
  rw [show (fun s : ℕ → (Fin q → ℝ) × (C × A) =>
      ((s i).2.1, ((s i).1, (s i).2.2))) =
      (fun p : (Fin q → ℝ) × (C × A) => ((p.2).1, (p.1, (p.2).2))) ∘
        (fun s : ℕ → (Fin q → ℝ) × (C × A) => s i) from rfl]
  rw [← Measure.map_map hpt (measurable_pi_apply i), Measure.infinitePi_map_eval]

/-- **The encoded thinning law, one cloud.**  The label-`c` sub-cloud of a marked
Poisson cloud with the mixture mark law, encoded as block data, has the law of a
local marked Poisson cloud of intensity `r * w c` and mark law `α c`. -/
theorem map_labelCloudEncode_markedPoissonLaw
    (q : ℕ) {C A : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableSpace A]
    (w : C → ℝ≥0) (hw : ∑ c, w c = 1)
    (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)]
    [IsProbabilityMeasure (mixtureMarkLaw w α)]
    (r : ℝ≥0) (c : C) :
    ((markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r).map
      (fun z => cloudEncode (labelCloud c z))) =
    (markedPoissonLaw q A (α c) (r * w c)).map (cloudEncode (q := q) (A := A)) := by
  classical
  haveI hcube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : IsProbabilityMeasure (mixtureMarkLaw w α) := mixtureMarkLaw_isProbability w α hw
  -- The one-point mark law of the local model.
  let ν : C → Measure ((Fin q → ℝ) × A) :=
    fun d => (cubeMeasure (Fin q) 1).prod (α d)
  haveI hν : ∀ d, IsProbabilityMeasure (ν d) := fun d => inferInstance
  -- The pair map.
  let pairMap : (Fin q → ℝ) × (C × A) → C × ((Fin q → ℝ) × A) :=
    fun p => ((p.2).1, (p.1, (p.2).2))
  have hpairMap : Measurable pairMap := by fun_prop
  -- The engine hypotheses.
  have hN : (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r).map
      (fun z => z.1) = poissonMeasure r := by
    rw [markedPoissonLaw, Measure.map_fst_prod, measure_univ, one_smul]
  have hpointSeq : iIndepFun (fun (i : ℕ) (s : ℕ → (Fin q → ℝ) × (C × A)) =>
      pairMap (s i)) (markedSeqLaw q (C × A) (mixtureMarkLaw w α)) := by
    rw [markedSeqLaw]
    exact iIndepFun_infinitePi_apply_comp ((cubeMeasure (Fin q) 1).prod (mixtureMarkLaw w α))
      pairMap hpairMap
  have hpair : ∀ n, iIndepFun (fun i : Fin n =>
      fun ξ : MarkedCloudSpace q (C × A) =>
        (((ξ.2 i).2.1), (((ξ.2 i).1), ((ξ.2 i).2.2)))) 
      (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r) := by
    intro n
    rw [markedPoissonLaw]
    exact (iIndepFun_snd_prod
      (ν₁ := poissonMeasure r) (ν₂ := markedSeqLaw q (C × A) (mixtureMarkLaw w α))
      (Y := fun i s => pairMap (s i))
      (fun i => hpairMap.comp (measurable_pi_apply i)) hpointSeq).precomp
      (g := fun i : Fin n => (i : ℕ)) (fun i j hij => Fin.ext hij)
  have hwmeas : ∀ i, Measurable (fun ξ : MarkedCloudSpace q (C × A) =>
      (ξ.2 i).2.1) := by
    intro i; fun_prop
  have hxmeas : ∀ i, Measurable (fun ξ : MarkedCloudSpace q (C × A) =>
      ((ξ.2 i).1, (ξ.2 i).2.2)) := by
    intro i; fun_prop
  have hjoint : ∀ i, (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r).map
      (fun ξ => ((ξ.2 i).2.1, ((ξ.2 i).1, (ξ.2 i).2.2))) =
      mixturePointLaw w ν := by
    intro i
    rw [map_markedPair_law]
    exact map_onePoint_mixtureMarkLaw q w α
  have hindep : ∀ n, IndepFun (fun ξ : MarkedCloudSpace q (C × A) => ξ.1)
      (fun ξ => fun i : Fin n =>
        (((ξ.2 i).2.1), (((ξ.2 i).1), ((ξ.2 i).2.2))))
      (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r) := by
    intro n
    rw [markedPoissonLaw]
    exact indepFun_prod (X := (id : ℕ → ℕ))
      (Y := fun s : ℕ → (Fin q → ℝ) × (C × A) => fun i : Fin n => pairMap (s i))
      measurable_id (measurable_pi_lambda _ fun i =>
        hpairMap.comp (measurable_pi_apply (i : ℕ)))
  -- Apply the engine.
  have hengine := map_poisson_blockDataOfPairsGen
    (P := markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r)
    (r) (fun ξ => ξ.1) (fun i ξ => (ξ.2 i).2.1)
    (fun i ξ => ((ξ.2 i).1, (ξ.2 i).2.2))
    w hw ν hN hpair hwmeas hxmeas hjoint hindep c
  -- Identify the two sides.
  have hleft : (fun ξ : MarkedCloudSpace q (C × A) =>
        prefixBlockDataGen (Pos := (Fin q → ℝ) × A) (fun ξ => ξ.1)
          (fun i ξ => (ξ.2 i).2.1) (fun i ξ => ((ξ.2 i).1, (ξ.2 i).2.2)) c ξ) =
      (fun ξ => cloudEncode (labelCloud c ξ)) := by
    funext ξ
    exact (cloudEncode_labelCloud_eq c ξ).symm
  change Measure.map (fun ξ => prefixBlockDataGen (Pos := (Fin q → ℝ) × A) (fun ξ => ξ.1)
      (fun i ξ => (ξ.2 i).2.1) (fun i ξ => ((ξ.2 i).1, (ξ.2 i).2.2)) c ξ)
      (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r) = _ at hengine
  rw [hleft] at hengine
  have hright : blockDataLaw (ν c) (fun m => poissonMeasure (r * w c) {m}) =
      (markedPoissonLaw q A (α c) (r * w c)).map (cloudEncode (q := q) (A := A)) := by
    rw [blockDataLaw_eq_map_cloud]
    congr 1
  rw [hright] at hengine
  exact hengine

/-- **The encoded thinning law, two clouds.**  The two-colour version obtained
from the single-cloud law by `Measure.map_prod_map`. -/
theorem map_labelCloudEncode_twoMarkedCloudLaw
    (q : ℕ) {C A B : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C]
    [MeasurableSingletonClass C] [MeasurableSpace A] [MeasurableSpace B]
    (w : C → ℝ≥0) (hw : ∑ c, w c = 1)
    (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)]
    (β : C → Measure B) [∀ c, IsProbabilityMeasure (β c)]
    [IsProbabilityMeasure (mixtureMarkLaw w α)]
    [IsProbabilityMeasure (mixtureMarkLaw w β)]
    (r : ℝ≥0) (c : C) :
    ((twoMarkedCloudLaw q (C × A) (C × B) (mixtureMarkLaw w α) (mixtureMarkLaw w β) r).map
      (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
        (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2)))) =
    ((twoMarkedCloudLaw q A B (α c) (β c) (r * w c)).map
      (fun y : TwoMarkedCloudSpace q A B =>
        (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2))) := by
  classical
  haveI : IsProbabilityMeasure (mixtureMarkLaw w α) := mixtureMarkLaw_isProbability w α hw
  haveI : IsProbabilityMeasure (mixtureMarkLaw w β) := mixtureMarkLaw_isProbability w β hw
  haveI : IsProbabilityMeasure (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r) :=
    inferInstance
  haveI : IsProbabilityMeasure (markedPoissonLaw q (C × B) (mixtureMarkLaw w β) r) :=
    inferInstance
  haveI : IsProbabilityMeasure (markedPoissonLaw q A (α c) (r * w c)) := inferInstance
  haveI : IsProbabilityMeasure (markedPoissonLaw q B (β c) (r * w c)) := inferInstance
  have hmeasA : Measurable (fun z : MarkedCloudSpace q (C × A) =>
      cloudEncode (labelCloud c z)) := measurable_cloudEncode_labelCloud (q := q) (A := A) c
  have hmeasB : Measurable (fun z : MarkedCloudSpace q (C × B) =>
      cloudEncode (labelCloud c z)) := measurable_cloudEncode_labelCloud (q := q) (A := B) c
  unfold twoMarkedCloudLaw
  rw [show (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
      (cloudEncode (labelCloud c ω.1), cloudEncode (labelCloud c ω.2))) =
      Prod.map (fun z : MarkedCloudSpace q (C × A) => cloudEncode (labelCloud c z))
        (fun z : MarkedCloudSpace q (C × B) => cloudEncode (labelCloud c z)) from rfl]
  rw [← Measure.map_prod_map
    (markedPoissonLaw q (C × A) (mixtureMarkLaw w α) r)
    (markedPoissonLaw q (C × B) (mixtureMarkLaw w β) r) hmeasA hmeasB]
  rw [show (fun y : TwoMarkedCloudSpace q A B =>
      (cloudEncode (q := q) (A := A) y.1, cloudEncode (q := q) (A := B) y.2)) =
      Prod.map (cloudEncode (q := q) (A := A)) (cloudEncode (q := q) (A := B)) from rfl]
  rw [← Measure.map_prod_map
    (markedPoissonLaw q A (α c) (r * w c))
    (markedPoissonLaw q B (β c) (r * w c))
    (measurable_cloudEncode (q := q) (A := A))
    (measurable_cloudEncode (q := q) (A := B))]
  rw [map_labelCloudEncode_markedPoissonLaw (q := q) (A := A) w hw α r c,
    map_labelCloudEncode_markedPoissonLaw (q := q) (A := B) w hw β r c]
