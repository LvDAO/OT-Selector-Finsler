/-
Copyright (c) 2026 LvDAO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OTSelector.Probability.MultinomialSplitting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Marked splitting of iid labels and points

This file upgrades the multinomial splitting of iid labels
(`OTSelector.Probability.MultinomialSplitting`) to the marked (point-level)
setting.  For an iid sequence of pairs `(w i, x i)` with uniform labels
`w i : Fin K` and iid marks `x i : Pos`, a label `b : Fin K` selects the
subsequence of marks whose label equals `b`.  The selected block is encoded by
the pair `(m, y)` where `m` is the number of selected positions and
`y : Fin m → Pos` enumerates the selected marks in the order of their
positions.

The main fixed-`n` result is `map_blockData`: the law of the block data of a
single label is the mixture `blockDataLaw ν (fiberCountLaw n K)` of the mark
clouds, where the block size has the binomial law obtained by counting words
with a prescribed number of occurrences of one label.

The file also records the joint (multi-block) law, in the correct form: the
count vector is multinomial and, conditionally on the count vector `k`, the
blocks are independent with mark clouds `ν^{k b}`.  The product of independent
binomial block-size laws is *not* the joint law of the block data, since the
block sizes are constrained to sum to `n`; the joint law is the mixture
`map_blockData_joint` below.  The Poisson version of the single-block law is
`map_poisson_blockData`.

The coordinate convention of the surrounding development is respected: labels
live in `Fin K` and marks in `Pos`; formal points are `(height, mark)` and
physical points are `(mark, height)`.  This file is independent of that
convention and only splits the label coordinate.
-/

open MeasureTheory ProbabilityTheory
open MeasurableSpace
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1000000

abbrev BlockData (Pos : Type*) := Σ m : ℕ, (Fin m → Pos)

noncomputable def blockDataLaw {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (prob : ℕ → ℝ≥0∞) :
    Measure (BlockData Pos) :=
  Measure.sum (fun m => prob m •
    (Measure.pi (fun _ : Fin m => ν)).map (fun y => (⟨m, y⟩ : BlockData Pos)))

noncomputable def fiberCountLaw (n K : ℕ) : ℕ → ℝ≥0∞ :=
  fun m => (n.choose m : ℝ≥0∞) * ((K - 1 : ℕ) : ℝ≥0∞) ^ (n - m) *
    ((K : ℝ≥0∞)⁻¹) ^ n

def blockPoints {n K : ℕ} {Ω Pos : Type*} [MeasurableSpace Pos]
    (w : Fin n → Ω → Fin K) (x : Fin n → Ω → Pos) (b : Fin K) (ξ : Ω)
    (j : Fin (labelCount (fun i => w i ξ) b)) : Pos :=
  x ((Finset.univ.filter (fun i => w i ξ = b)).orderIsoOfFin (by
    simp [labelCount]) j).1 ξ

def blockDataOfPairs {n K : ℕ} {Pos : Type*} [MeasurableSpace Pos]
    (b : Fin K) (z : Fin n → Fin K × Pos) : BlockData Pos :=
  let s := Finset.univ.filter (fun i => (z i).1 = b)
  ⟨s.card, fun j => (z ((s.orderIsoOfFin rfl) j).1).2⟩

def blockDataOfWordPoints {n K : ℕ} {Pos : Type*} [MeasurableSpace Pos]
    (b : Fin K) (p : (Fin n → Fin K) × (Fin n → Pos)) : BlockData Pos :=
  let s := Finset.univ.filter (fun i => p.1 i = b)
  ⟨s.card, fun j => p.2 ((s.orderIsoOfFin rfl) j).1⟩

lemma measurable_sigma_mk {α : Type*} {β : α → Type*} [m : ∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (@Sigma.mk α β a) := by
  intro s hs
  have hs' : MeasurableSet[(⨅ a, (m a).map (Sigma.mk a))] s := hs
  rw [MeasurableSpace.measurableSet_iInf] at hs'
  exact hs' a

private lemma map_pi_fiber {ι : Type*} [Fintype ι] [LinearOrder ι] {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (s : Finset ι) :
    (Measure.pi (fun _ : ι => ν)).map
        (fun y : ι → α => fun j : Fin s.card => y (s.orderIsoOfFin rfl j).1) =
      Measure.pi (fun _ : Fin s.card => ν) := by
  classical
  let e : Fin s.card ≃o ↥s := s.orderIsoOfFin rfl
  apply (Measure.pi_eq ?_).symm
  intro A hA
  rw [Measure.map_apply]
  · have hpre : (fun y : ι → α => fun j : Fin s.card => y (e j).1) ⁻¹' Set.pi Set.univ A =
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
    have hprod : (∏ i : ι, ν (if h : i ∈ s then A (e.symm ⟨i, h⟩) else Set.univ))
        = ∏ j : Fin s.card, ν (A j) := by
      have h1 : (∏ i : ι, ν (if h : i ∈ s then A (e.symm ⟨i, h⟩) else Set.univ))
          = ∏ i ∈ s, ν (if h : i ∈ s then A (e.symm ⟨i, h⟩) else Set.univ) := by
        rw [Finset.prod_subset (Finset.subset_univ s)]
        intro x _ hx
        rw [dite_eq_right hx, measure_univ]
      rw [h1, Finset.prod_subtype s (fun x => Iff.rfl)]
      have h2 : ∀ i : ↥s, ν (if h : (i : ι) ∈ s then A (e.symm ⟨(i : ι), h⟩) else Set.univ)
          = ν (A (e.symm i)) := by
        intro i
        rw [dite_eq_left i.2]
      simp_rw [h2]
      exact Fintype.prod_equiv e.symm (fun i : ↥s => ν (A (e.symm i)))
        (fun j => ν (A j)) (fun i => rfl)
    exact hprod
  · exact measurable_pi_lambda _ fun j => measurable_pi_apply _
  · exact MeasurableSet.univ_pi hA

private def fiberToFun {n K : ℕ} (b : Fin K) (m : ℕ)
    (u : {u : Fin n → Fin K // (Finset.univ.filter fun i => u i = b).card = m}) :
    Σ s : {s : Finset (Fin n) // s.card = m},
      ({i : Fin n // i ∉ (s : Finset (Fin n))} → {c : Fin K // c ≠ b}) :=
  let s : Finset (Fin n) := Finset.univ.filter fun i => u.1 i = b
  ⟨⟨s, u.2⟩, fun i => ⟨u.1 i, by simpa [s] using i.2⟩⟩

private def fiberInvFun {n K : ℕ} (b : Fin K) (m : ℕ)
    (p : Σ s : {s : Finset (Fin n) // s.card = m},
      ({i : Fin n // i ∉ (s : Finset (Fin n))} → {c : Fin K // c ≠ b})) :
    {u : Fin n → Fin K // (Finset.univ.filter fun i => u i = b).card = m} :=
  ⟨fun i => if h : i ∈ p.1.1 then b else (p.2 ⟨i, h⟩).1, by
    have hs : (Finset.univ.filter fun i =>
        (if h : i ∈ p.1.1 then b else (p.2 ⟨i, h⟩).1) = b) = p.1.1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hi
        rw [dite_eq_right hi] at h
        exact (p.2 ⟨i, hi⟩).2 h
      · intro hi
        rw [dite_eq_left hi]
    rw [hs, p.1.2]⟩

private lemma fiberInvFun_filter {n K : ℕ} (b : Fin K) (m : ℕ)
    (p : Σ s : {s : Finset (Fin n) // s.card = m},
      ({i : Fin n // i ∉ (s : Finset (Fin n))} → {c : Fin K // c ≠ b})) :
    (Finset.univ.filter fun i =>
        (fiberInvFun b m p).1 i = b) = p.1.1 := by
  rcases p with ⟨⟨s, hs⟩, g⟩
  dsimp only [fiberInvFun]
  have hs' : (Finset.univ.filter fun i =>
      (if h : i ∈ s then b else (g ⟨i, h⟩).1) = b) = s := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hi
      rw [dite_eq_right hi] at h
      exact (g ⟨i, hi⟩).2 h
    · intro hi
      rw [dite_eq_left hi]
  exact hs'

private def fiberWordEquiv {n K : ℕ} (b : Fin K) (m : ℕ) :
    {u : Fin n → Fin K // (Finset.univ.filter fun i => u i = b).card = m} ≃
      Σ s : {s : Finset (Fin n) // s.card = m},
        ({i : Fin n // i ∉ (s : Finset (Fin n))} → {c : Fin K // c ≠ b}) where
  toFun := fiberToFun b m
  invFun := fiberInvFun b m
  left_inv u := by
    apply Subtype.ext
    funext i
    simp only [fiberToFun, fiberInvFun]
    split_ifs with h
    · have hu : u.1 i = b := by simpa using h
      simp [hu]
    · simp [h]
  right_inv p := by
    rcases p with ⟨⟨s, hs⟩, g⟩
    have hs_eq : (Finset.univ.filter fun i =>
        (fiberInvFun b m ⟨⟨s, hs⟩, g⟩).1 i = b) = s :=
      fiberInvFun_filter b m ⟨⟨s, hs⟩, g⟩
    simp only [fiberToFun]
    apply Sigma.ext
    · exact Subtype.ext hs_eq
    · apply Function.hfunext
      · exact congrArg (fun t : Finset (Fin n) => {i : Fin n // i ∉ t}) hs_eq
      · intro i j hij
        apply heq_of_eq
        apply Subtype.ext
        dsimp only
        have hpq : ∀ x : Fin n,
            (x ∉ Finset.univ.filter fun i =>
              (fiberInvFun b m ⟨⟨s, hs⟩, g⟩).1 i = b) ↔ (x ∉ s) := by
          intro x; rw [hs_eq]
        have hval : i.1 = j.1 := (Subtype.heq_iff_coe_eq hpq).mp hij
        rw [hval]
        simp only [fiberInvFun]
        split_ifs with hi
        · exact absurd hi j.2
        · rfl

lemma card_words_fiber_count {n K : ℕ} (b : Fin K) (m : ℕ) :
    Nat.card {u : Fin n → Fin K // (Finset.univ.filter fun i => u i = b).card = m} =
      n.choose m * (K - 1) ^ (n - m) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (fiberWordEquiv b m), Fintype.card_sigma]
  have hterm : ∀ s : {s : Finset (Fin n) // s.card = m},
      Fintype.card ({i : Fin n // i ∉ (s : Finset (Fin n))} → {c : Fin K // c ≠ b})
        = (K - 1) ^ (n - m) := by
    intro s
    rw [Fintype.card_fun]
    have hc : Fintype.card {c : Fin K // c ≠ b} = K - 1 := by
      rw [Fintype.card_subtype_compl (p := fun c : Fin K => c = b),
        Fintype.card_subtype_eq, Fintype.card_fin]
    have hd : Fintype.card {i : Fin n // i ∉ (s : Finset (Fin n))} = n - m := by
      rw [Fintype.card_subtype_compl (p := fun i : Fin n => i ∈ (s : Finset (Fin n)))]
      have hs : Fintype.card {i : Fin n // i ∈ (s : Finset (Fin n))} = m := by
        rw [Fintype.card_coe, s.2]
      rw [hs, Fintype.card_fin]
    rw [hc, hd]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

private lemma pi_uniform_set {n K : ℕ} [NeZero K] (p : (Fin n → Fin K) → Prop)
    [DecidablePred p] :
    (Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))) {u : Fin n → Fin K | p u} =
      (Nat.card {u : Fin n → Fin K // p u} : ℝ≥0∞) *
        ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n := by
  classical
  set S : Finset (Fin n → Fin K) := Finset.univ.filter p
  have hset : {u : Fin n → Fin K | p u} = (↑S : Set (Fin n → Fin K)) := by
    ext u; simp [S]
  have hset2 : (↑S : Set (Fin n → Fin K)) = ⋃ q ∈ S, ({q} : Set (Fin n → Fin K)) := by
    ext x; simp
  rw [hset, hset2, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun q _ => ?_)]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    · rw [Measure.pi_singleton]
      simp [uniformMeasure_singleton, Finset.prod_const]
  · intro a ha b hb hab
    exact Set.disjoint_singleton.mpr hab
  · intro b hb
    exact measurableSet_singleton b

lemma pi_uniform_fiber_count {n K : ℕ} [NeZero K] (b : Fin K) (m : ℕ) :
    (Measure.pi (fun _ : Fin n => uniformMeasure (Fin K)))
        {u : Fin n → Fin K | (Finset.univ.filter fun i => u i = b).card = m} =
      fiberCountLaw n K m := by
  classical
  rw [pi_uniform_set]
  rw [card_words_fiber_count b m]
  simp only [fiberCountLaw, Fintype.card_fin]
  push_cast
  ring


private lemma map_blockDataOfWordPoints
    {n K : ℕ} [NeZero K] {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (b : Fin K) :
    ((Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))).prod
        (Measure.pi (fun _ : Fin n => ν))).map (blockDataOfWordPoints (Pos := Pos) b) =
      Measure.sum (fun u : Fin n → Fin K =>
        ((Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))) {u}) •
          ((Measure.pi (fun _ : Fin (labelCount u b) => ν)).map
            (fun y => (⟨labelCount u b, y⟩ : BlockData Pos)))) := by
  classical
  let ρ : Measure (Fin n → Fin K) := Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))
  let σ : Measure (Fin n → Pos) := Measure.pi (fun _ : Fin n => ν)
  let g : (Fin n → Fin K) × (Fin n → Pos) → BlockData Pos := blockDataOfWordPoints b
  have hprod : ρ.prod σ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • ((Measure.dirac u).prod σ)) := by
    conv_lhs => rw [show ρ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • Measure.dirac u) from (Measure.sum_smul_dirac ρ).symm]
    rw [Measure.prod_sum_left]
    congr 1
    funext u
    rw [Measure.prod_smul_left]
  have hg_ae : AEMeasurable g (Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • ((Measure.dirac u).prod σ))) := by
    apply AEMeasurable.sum_measure
    intro u
    rw [Measure.dirac_prod]
    by_cases hc : ρ {u} = 0
    · rw [hc, zero_smul]
      exact aemeasurable_zero_measure
    · rw [aemeasurable_smul_measure_iff hc]
      let gu : (Fin n → Fin K) × (Fin n → Pos) → BlockData Pos :=
        fun p => ⟨labelCount u b, fun j =>
          p.2 ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1⟩
      have hgu : Measurable gu := by
        have hproj : Measurable (fun p : (Fin n → Fin K) × (Fin n → Pos) =>
            fun j : Fin (labelCount u b) =>
              p.2 ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1) :=
          measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp measurable_snd)
        exact (measurable_sigma_mk (labelCount u b)).comp hproj
      have heq : g =ᵐ[σ.map (Prod.mk u)] gu := by
        rw [Filter.EventuallyEq, ae_iff]
        apply measure_mono_null
          (t := {x : (Fin n → Fin K) × (Fin n → Pos) | x.1 ≠ u})
        · intro x hx
          simp only [Set.mem_ofPred_eq] at hx ⊢
          intro hxu
          apply hx
          cases x with
          | mk a b =>
            simp only at hxu
            subst hxu
            rfl
        · rw [Measure.map_apply measurable_prodMk_left (by measurability)]
          simp
      exact hgu.aemeasurable.congr heq.symm
  rw [hprod, Measure.map_sum hg_ae]
  congr 1
  funext u
  rw [Measure.map_smul]
  congr 1
  -- now: ((dirac u).prod σ).map g = (ν^m).map (Sigma.mk m)
  rw [Measure.dirac_prod]
  have hg_u : AEMeasurable g (σ.map (Prod.mk u)) := by
    let gu : (Fin n → Fin K) × (Fin n → Pos) → BlockData Pos :=
      fun p => ⟨labelCount u b, fun j =>
        p.2 ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1⟩
    have hgu : Measurable gu := by
      have hproj : Measurable (fun p : (Fin n → Fin K) × (Fin n → Pos) =>
          fun j : Fin (labelCount u b) =>
            p.2 ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1) :=
        measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp measurable_snd)
      exact (measurable_sigma_mk (labelCount u b)).comp hproj
    have heq : g =ᵐ[σ.map (Prod.mk u)] gu := by
      rw [Filter.EventuallyEq, ae_iff]
      apply measure_mono_null
        (t := {x : (Fin n → Fin K) × (Fin n → Pos) | x.1 ≠ u})
      · intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        intro hxu
        apply hx
        cases x with
        | mk a b =>
          simp only at hxu
          subst hxu
          rfl
      · rw [Measure.map_apply measurable_prodMk_left (by measurability)]
        simp
    exact hgu.aemeasurable.congr heq.symm
  have hproj_meas : Measurable (fun y : Fin n → Pos => fun j : Fin (labelCount u b) =>
      y ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hcomp : g ∘ Prod.mk u =
      (fun y : Fin (labelCount u b) → Pos => (⟨labelCount u b, y⟩ : BlockData Pos)) ∘
        (fun y : Fin n → Pos => fun j : Fin (labelCount u b) =>
          y ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1) := by
    funext y
    rfl
  calc
    (σ.map (Prod.mk u)).map g = σ.map (g ∘ Prod.mk u) :=
      AEMeasurable.map_map_of_aemeasurable hg_u measurable_prodMk_left.aemeasurable
    _ = σ.map ((fun y : Fin (labelCount u b) → Pos =>
            (⟨labelCount u b, y⟩ : BlockData Pos)) ∘
          (fun y : Fin n → Pos => fun j : Fin (labelCount u b) =>
            y ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1)) := by
          rw [hcomp]
    _ = (σ.map (fun y : Fin n → Pos => fun j : Fin (labelCount u b) =>
            y ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1)).map
          (fun y : Fin (labelCount u b) → Pos => (⟨labelCount u b, y⟩ : BlockData Pos)) :=
          (AEMeasurable.map_map_of_aemeasurable (measurable_sigma_mk _).aemeasurable
            hproj_meas.aemeasurable).symm
    _ = (Measure.pi (fun _ : Fin (labelCount u b) => ν)).map
          (fun y : Fin (labelCount u b) → Pos => (⟨labelCount u b, y⟩ : BlockData Pos)) := by
          have hinner : Measure.map (fun y : Fin n → Pos => fun j : Fin (labelCount u b) =>
              y ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1)
              (Measure.pi (fun _ : Fin n => ν))
              = Measure.pi (fun _ : Fin (labelCount u b) => ν) :=
            map_pi_fiber (ι := Fin n) ν (Finset.univ.filter (fun i => u i = b))
          simp only [σ]
          rw [hinner]


private lemma Measure.sum_eq_finset_sum_of_zero {α : Type*} [MeasurableSpace α]
    (f : ℕ → Measure α) (s : Finset ℕ) (h : ∀ m ∉ s, f m = 0) :
    Measure.sum f = ∑ m ∈ s, f m := by
  ext S hS
  rw [Measure.sum_apply _ hS, Measure.finsetSum_apply]
  exact tsum_eq_sum (fun m hm => by rw [h m hm]; simp)

private lemma card_fiber_mul {n K : ℕ} (b : Fin K) (m : ℕ) :
    (Nat.card {u : Fin n → Fin K // labelCount u b = m} : ℝ≥0∞) *
        ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n = fiberCountLaw n K m := by
  have hcard : Nat.card {u : Fin n → Fin K // labelCount u b = m} =
      n.choose m * (K - 1) ^ (n - m) := by
    rw [show Nat.card {u : Fin n → Fin K // labelCount u b = m} =
        Nat.card {u : Fin n → Fin K //
          (Finset.univ.filter fun i => u i = b).card = m} from
      Nat.card_congr (Equiv.subtypeEquivRight (fun u => by simp [labelCount]))]
    exact card_words_fiber_count b m
  rw [hcard]
  simp only [fiberCountLaw, Fintype.card_fin]
  push_cast
  ring

private lemma sum_block_terms
    {n K : ℕ} [NeZero K] {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (b : Fin K) :
    Measure.sum (fun u : Fin n → Fin K =>
        ((Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))) {u}) •
          ((Measure.pi (fun _ : Fin (labelCount u b) => ν)).map
            (fun y => (⟨labelCount u b, y⟩ : BlockData Pos))))
      = blockDataLaw ν (fiberCountLaw n K) := by
  classical
  let c : ℝ≥0∞ := ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n
  have hconst : ∀ u : Fin n → Fin K,
      (Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))) {u} = c := by
    intro u
    rw [Measure.pi_singleton]
    simp [c, uniformMeasure_singleton, Finset.prod_const]
  simp_rw [hconst]
  rw [Measure.sum_fintype]
  rw [blockDataLaw]
  rw [Measure.sum_eq_finset_sum_of_zero (s := Finset.range (n + 1)) (f := fun m =>
      fiberCountLaw n K m • (Measure.pi (fun _ : Fin m => ν)).map
        (fun y => (⟨m, y⟩ : BlockData Pos))) ?_]
  · rw [← Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.range (n + 1))
      (g := fun u : Fin n → Fin K => labelCount u b)
      (f := fun m => c • (Measure.pi (fun _ : Fin m => ν)).map
        (fun y => (⟨m, y⟩ : BlockData Pos))) ?_]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
      congr 1
      have hcard : ((Finset.univ.filter (fun u : Fin n → Fin K =>
          labelCount u b = m)).card : ℝ≥0∞) =
          (Nat.card {u : Fin n → Fin K // labelCount u b = m} : ℝ≥0∞) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hcard, card_fiber_mul]
    · intro u _
      rw [Finset.mem_range]
      have hle : labelCount u b ≤ ∑ i, labelCount u i :=
        Finset.single_le_sum (s := Finset.univ) (f := fun i => labelCount u i)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ b)
      rw [sum_labelCount] at hle
      exact Nat.lt_succ_of_le hle
  · intro m hm
    rw [Finset.mem_range, not_lt] at hm
    have hchoose : n.choose m = 0 := Nat.choose_eq_zero_of_lt hm
    simp [fiberCountLaw, hchoose]


private lemma aemeasurable_blockDataOfWordPoints
    {n K : ℕ} [NeZero K] {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (b : Fin K) :
    AEMeasurable (blockDataOfWordPoints (Pos := Pos) b)
      ((Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))).prod
        (Measure.pi (fun _ : Fin n => ν))) := by
  classical
  let ρ : Measure (Fin n → Fin K) := Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))
  let σ : Measure (Fin n → Pos) := Measure.pi (fun _ : Fin n => ν)
  let g : (Fin n → Fin K) × (Fin n → Pos) → BlockData Pos := blockDataOfWordPoints b
  have hprod : ρ.prod σ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • ((Measure.dirac u).prod σ)) := by
    conv_lhs => rw [show ρ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • Measure.dirac u) from (Measure.sum_smul_dirac ρ).symm]
    rw [Measure.prod_sum_left]
    congr 1
    funext u
    rw [Measure.prod_smul_left]
  rw [hprod]
  apply AEMeasurable.sum_measure
  intro u
  rw [Measure.dirac_prod]
  by_cases hc : ρ {u} = 0
  · rw [hc, zero_smul]
    exact aemeasurable_zero_measure
  · rw [aemeasurable_smul_measure_iff hc]
    let gu : (Fin n → Fin K) × (Fin n → Pos) → BlockData Pos :=
      fun p => ⟨labelCount u b, fun j =>
        p.2 ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1⟩
    have hgu : Measurable gu := by
      have hproj : Measurable (fun p : (Fin n → Fin K) × (Fin n → Pos) =>
          fun j : Fin (labelCount u b) =>
            p.2 ((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl j).1) :=
        measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp measurable_snd)
      exact (measurable_sigma_mk (labelCount u b)).comp hproj
    have heq : g =ᵐ[σ.map (Prod.mk u)] gu := by
      rw [Filter.EventuallyEq, ae_iff]
      apply measure_mono_null
        (t := {x : (Fin n → Fin K) × (Fin n → Pos) | x.1 ≠ u})
      · intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        intro hxu
        apply hx
        cases x with
        | mk a b =>
          simp only at hxu
          subst hxu
          rfl
      · rw [Measure.map_apply measurable_prodMk_left (by measurability)]
        simp
    exact hgu.aemeasurable.congr heq.symm

/-- **Fixed-`n` marked splitting.**  For iid pairs `(w i, x i)` with uniform labels and
marks distributed as `ν`, the marked block of a single label `b` has law
`blockDataLaw ν (fiberCountLaw n K)`: the block size has the binomial word-count law and,
conditionally on the size, the marks are iid `ν`. -/
theorem map_blockData {Ω Pos : Type*} [MeasurableSpace Ω] [MeasurableSpace Pos]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure Pos} [IsProbabilityMeasure ν]
    {n K : ℕ} [NeZero K] (w : Fin n → Ω → Fin K) (x : Fin n → Ω → Pos)
    (hw : ∀ i, Measurable (w i)) (hx : ∀ i, Measurable (x i))
    (hi : iIndepFun (fun i : Fin n => fun ξ => (w i ξ, x i ξ)) P)
    (hlaw_w : ∀ i, P.map (w i) = uniformMeasure (Fin K))
    (hlaw_x : ∀ i, P.map (x i) = ν)
    (hindep_wx : ∀ i, IndepFun (w i) (x i) P) (b : Fin K) :
    P.map (fun ξ => (⟨labelCount (fun i => w i ξ) b, blockPoints w x b ξ⟩ : BlockData Pos)) =
      blockDataLaw ν (fiberCountLaw n K) := by
  classical
  let ρ : Measure (Fin n → Fin K) := Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))
  let σ : Measure (Fin n → Pos) := Measure.pi (fun _ : Fin n => ν)
  let g : (Fin n → Fin K) × (Fin n → Pos) → BlockData Pos := blockDataOfWordPoints b
  let Z : Ω → Fin n → Fin K × Pos := fun ξ i => (w i ξ, x i ξ)
  let Z' : Ω → (Fin n → Fin K) × (Fin n → Pos) := fun ξ => (fun i => w i ξ, fun i => x i ξ)
  have hpairlaw : ∀ i, P.map (fun ξ => (w i ξ, x i ξ)) = (uniformMeasure (Fin K)).prod ν := by
    intro i
    rw [(hindep_wx i).map_prod_eq_prod_map_map (hw i).aemeasurable (hx i).aemeasurable,
      hlaw_w i, hlaw_x i]
  have hZ : P.map Z = Measure.pi (fun _ : Fin n => (uniformMeasure (Fin K)).prod ν) := by
    have h := iIndepFun.map_fun_eq_pi_map
      (f := fun i : Fin n => fun ξ => (w i ξ, x i ξ))
      (fun i => (hw i).prod (hx i) |>.aemeasurable) hi
    rwa [show (fun i => P.map (fun ξ => (w i ξ, x i ξ))) =
      (fun _ : Fin n => (uniformMeasure (Fin K)).prod ν) from funext hpairlaw] at h
  have hZmeas : Measurable Z := by
    exact measurable_pi_lambda _ (fun i => (hw i).prod (hx i))
  have hZ'meas : Measurable Z' := by
    exact (measurable_pi_lambda _ hw).prod (measurable_pi_lambda _ hx)
  have hZ' : P.map Z' = ρ.prod σ := by
    let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin K) Pos (Fin n)
    have hmap : P.map Z' = (P.map Z).map e := by
      rw [Measure.map_map (μ := P) e.measurable hZmeas]
      congr 1
    rw [hmap, hZ]
    exact (measurePreserving_arrowProdEquivProdArrow (Fin K) Pos (Fin n)
      (fun _ => uniformMeasure (Fin K)) (fun _ => ν)).map_eq
  have hg_ae : AEMeasurable g (P.map Z') := by
    rw [hZ']
    exact aemeasurable_blockDataOfWordPoints ν b
  have hB : (fun ξ => (⟨labelCount (fun i => w i ξ) b, blockPoints w x b ξ⟩ : BlockData Pos))
      = g ∘ Z' := by
    funext ξ
    rfl
  rw [hB, ← AEMeasurable.map_map_of_aemeasurable hg_ae hZ'meas.aemeasurable, hZ',
    map_blockDataOfWordPoints]
  exact sum_block_terms ν b


private lemma map_pi_sigma_reindex
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    {K : ℕ} (s : Fin K → Finset ι)
    (hdisj : ∀ b c, b ≠ c → Disjoint (s b) (s c))
    (hcover : Finset.univ.biUnion s = Finset.univ) :
    (Measure.pi (fun _ : ι => ν)).map
        (fun y : ι → α => fun p : Sigma (fun b : Fin K => Fin (s b).card) =>
          y (((s p.1).orderIsoOfFin rfl) p.2).1) =
      Measure.pi (fun _ : Sigma (fun b : Fin K => Fin (s b).card) => ν) := by
  classical
  have hex : ∀ i : ι, ∃ b : Fin K, i ∈ s b := by
    intro i
    have hi : i ∈ Finset.univ.biUnion s := by
      rw [hcover]
      exact Finset.mem_univ i
    simpa using Finset.mem_biUnion.mp hi
  let bOf : ι → Fin K := fun i => Classical.choose (hex i)
  have hiOf : ∀ i : ι, i ∈ s (bOf i) := fun i => Classical.choose_spec (hex i)
  have hiff : ∀ i b, bOf i = b ↔ i ∈ s b := by
    intro i b
    constructor
    · rintro rfl
      exact hiOf i
    · intro hib
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj (bOf i) b hne) (hiOf i) hib
  let eFib : ∀ b : Fin K, {i : ι // bOf i = b} ≃ ↥(s b) := fun b =>
    Equiv.subtypeEquivRight (fun i => hiff i b)
  let eSigma : ι ≃ Sigma (fun b : Fin K => Fin (s b).card) :=
    (Equiv.sigmaFiberEquiv bOf).symm.trans
      (Equiv.sigmaCongrRight (fun b =>
        (eFib b).trans (((s b).orderIsoOfFin rfl).toEquiv.symm)))
  have eSigma_symm_apply : ∀ (b : Fin K) (j : Fin (s b).card),
      eSigma.symm ⟨b, j⟩ = (((s b).orderIsoOfFin rfl) j).1 := by
    intro b j
    simp only [eSigma, eFib, Equiv.symm_trans, Equiv.trans_apply,
      Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply,
      Equiv.sigmaFiberEquiv_apply, Equiv.subtypeEquivRight_symm_apply,
      Equiv.symm_symm]
    rfl
  have hmap : (fun y : ι → α => fun p : Sigma (fun b : Fin K => Fin (s b).card) =>
        y (((s p.1).orderIsoOfFin rfl) p.2).1)
      = (fun y : ι → α => fun p : Sigma (fun b : Fin K => Fin (s b).card) =>
        y (eSigma.symm p)) := by
    funext y p
    rcases p with ⟨b, j⟩
    rw [eSigma_symm_apply]
  rw [hmap]
  apply (Measure.pi_eq ?_).symm
  intro A hA
  rw [Measure.map_apply]
  · have hpre : (fun y : ι → α => fun p : Sigma (fun b : Fin K => Fin (s b).card) =>
          y (eSigma.symm p)) ⁻¹' (Set.pi Set.univ A) =
        Set.pi Set.univ (fun i => A (eSigma i)) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h i
        have := h (eSigma i)
        rwa [eSigma.symm_apply_apply] at this
      · intro h p
        have := h (eSigma.symm p)
        rwa [eSigma.apply_symm_apply] at this
    rw [hpre, Measure.pi_pi]
    exact Equiv.prod_comp eSigma (fun p : Sigma (fun b : Fin K => Fin (s b).card) => ν (A p))
  · exact measurable_pi_lambda _ (fun p => measurable_pi_apply _)
  · exact MeasurableSet.pi Set.countable_univ (fun i _ => hA i)

private lemma map_pi_piCurry
    {ι : Type*} [Fintype ι]
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    {K : ℕ} (s : Fin K → Finset ι) :
    (Measure.pi (fun _ : Sigma (fun b : Fin K => Fin (s b).card) => ν)).map
        (MeasurableEquiv.piCurry (fun (b : Fin K) (_ : Fin (s b).card) => α)) =
      Measure.pi (fun b : Fin K => Measure.pi (fun _ : Fin (s b).card => ν)) := by
  classical
  let C : ∀ b : Fin K, Set (Set (Fin (s b).card → α)) := fun b =>
    Set.pi Set.univ '' Set.pi Set.univ (fun _ : Fin (s b).card => {t : Set α | MeasurableSet t})
  have hC : ∀ b, generateFrom (C b) = (inferInstance : MeasurableSpace (Fin (s b).card → α)) := by
    intro b
    simpa [C] using generateFrom_pi (α := fun _ : Fin (s b).card => α)
  have h2C : ∀ b, IsPiSystem (C b) := by
    intro b
    simpa [C] using isPiSystem_pi (α := fun _ : Fin (s b).card => α)
  have h3C : ∀ b, (Measure.pi (fun _ : Fin (s b).card => ν)).FiniteSpanningSetsIn (C b) := by
    intro b
    refine ⟨fun _ => Set.univ, ?_, ?_, ?_⟩
    · intro n
      refine (Set.mem_image _ _ _).mpr ⟨fun _ => Set.univ, ?_, ?_⟩
      · simp
      · simp
    · intro n
      simp [measure_univ]
    · rw [Set.iUnion_const]
  refine (Measure.pi_eq_generateFrom (C := C) hC h2C h3C ?_).symm
  intro t ht
  have hchoice : ∀ b, ∃ A : Fin (s b).card → Set α,
      (∀ j, MeasurableSet (A j)) ∧ t b = Set.pi Set.univ A := by
    intro b
    have hb := ht b
    simp only [C, Set.mem_image, Set.mem_pi, Set.mem_univ, forall_true_left] at hb
    rcases hb with ⟨A, hA, hAt⟩
    exact ⟨A, hA, hAt.symm⟩
  choose A hAmeas htA using hchoice
  have ht_meas : MeasurableSet (Set.pi Set.univ t) := by
    apply MeasurableSet.pi Set.countable_univ
    intro b _
    rw [htA b]
    exact MeasurableSet.univ_pi (hAmeas b)
  rw [Measure.map_apply]
  · have hpre : (MeasurableEquiv.piCurry (fun (b : Fin K) (_ : Fin (s b).card) => α)) ⁻¹'
        (Set.pi Set.univ t) =
        Set.pi Set.univ (fun p : Sigma (fun b : Fin K => Fin (s b).card) => A p.1 p.2) := by
      ext f
      simp only [MeasurableEquiv.piCurry, MeasurableEquiv.coe_mk, Set.mem_preimage,
        Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h
        rintro ⟨b, j⟩
        have hb := h b
        rw [htA b] at hb
        simp only [Set.mem_pi, Set.mem_univ, forall_true_left] at hb
        exact hb j
      · intro h b
        rw [htA b]
        simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
        intro j
        exact h ⟨b, j⟩
    rw [hpre, Measure.pi_pi]
    simp_rw [htA]
    simp_rw [Measure.pi_pi]
    exact Fintype.prod_sigma' (fun b j => ν (A b j))
  · exact (MeasurableEquiv.piCurry (fun (b : Fin K) (_ : Fin (s b).card) => α)).measurable
  · exact ht_meas

private lemma map_pi_partition
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    {K : ℕ} (s : Fin K → Finset ι)
    (hdisj : ∀ b c, b ≠ c → Disjoint (s b) (s c))
    (hcover : Finset.univ.biUnion s = Finset.univ) :
    (Measure.pi (fun _ : ι => ν)).map
        (fun y : ι → α => fun b : Fin K => fun j : Fin (s b).card =>
          y (((s b).orderIsoOfFin rfl) j).1) =
      Measure.pi (fun b : Fin K => Measure.pi (fun _ : Fin (s b).card => ν)) := by
  classical
  have h1 := map_pi_sigma_reindex ν s hdisj hcover
  have h2 := map_pi_piCurry (α := α) ν s
  let F : (ι → α) → (∀ b : Fin K, Fin (s b).card → α) :=
    fun y b j => y (((s b).orderIsoOfFin rfl) j).1
  let G : (ι → α) → (Sigma (fun b : Fin K => Fin (s b).card) → α) :=
    fun y p => y (((s p.1).orderIsoOfFin rfl) p.2).1
  let e := MeasurableEquiv.piCurry (fun (b : Fin K) (_ : Fin (s b).card) => α)
  have hFG : F = e ∘ G := by
    funext y b j
    rfl
  change (Measure.pi (fun _ : ι => ν)).map F = _
  rw [hFG, ← Measure.map_map e.measurable (by
    exact measurable_pi_lambda _ (fun p => measurable_pi_apply _)), h1, h2]

-- Joint multi-block development

/-- The joint block map on a word-point pair: for each label `b` it records the number of
positions carrying label `b` and the marks at those positions, in order. -/
def blockDataOfWordPointsAll {n K : ℕ} {Pos : Type*} [MeasurableSpace Pos]
    (p : (Fin n → Fin K) × (Fin n → Pos)) : Fin K → BlockData Pos :=
  fun b =>
    let s := Finset.univ.filter (fun i => p.1 i = b)
    ⟨s.card, fun j => p.2 ((s.orderIsoOfFin rfl) j).1⟩

private lemma fibers_disjoint {n K : ℕ} (u : Fin n → Fin K) :
    ∀ b c : Fin K, b ≠ c →
      Disjoint (Finset.univ.filter (fun i => u i = b))
        (Finset.univ.filter (fun i => u i = c)) := by
  intro b c hbc
  rw [Finset.disjoint_left]
  intro i hib hic
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hib hic
  exact hbc (hib.symm.trans hic)

private lemma fibers_cover {n K : ℕ} (u : Fin n → Fin K) :
    Finset.univ.biUnion (fun b : Fin K => Finset.univ.filter (fun i => u i = b)) =
      Finset.univ := by
  ext i
  simp [Finset.mem_biUnion]

private lemma measurable_blockMk {Pos : Type*} [MeasurableSpace Pos] (m : ℕ) :
    Measurable (fun y : Fin m → Pos => (⟨m, y⟩ : BlockData Pos)) :=
  measurable_sigma_mk m

set_option linter.style.haveILetI false in
private lemma map_blockDataOfWordPointsAll_slice
    {n K : ℕ} [NeZero K] {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (u : Fin n → Fin K) :
    ((Measure.dirac u).prod (Measure.pi (fun _ : Fin n => ν))).map
        (blockDataOfWordPointsAll (Pos := Pos)) =
      Measure.pi (fun b : Fin K =>
        (Measure.pi (fun _ : Fin (labelCount u b) => ν)).map
          (fun y => (⟨labelCount u b, y⟩ : BlockData Pos))) := by
  classical
  let s : Fin K → Finset (Fin n) := fun b => Finset.univ.filter (fun i => u i = b)
  have hs_card : ∀ b, (s b).card = labelCount u b := fun b => rfl
  have hdisj : ∀ b c, b ≠ c → Disjoint (s b) (s c) := fun b c => fibers_disjoint u b c
  have hcover : Finset.univ.biUnion s = Finset.univ := fibers_cover u
  let F : (Fin n → Pos) → (∀ b : Fin K, Fin (s b).card → Pos) :=
    fun y b j => y (((s b).orderIsoOfFin rfl) j).1
  let H : (∀ b : Fin K, Fin (s b).card → Pos) → (Fin K → BlockData Pos) :=
    fun z b => ⟨(s b).card, z b⟩
  have hF : Measurable F := measurable_pi_lambda _ (fun b =>
    measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro b
    exact (measurable_sigma_mk (s b).card).comp (measurable_pi_apply b)
  have hcomp : blockDataOfWordPointsAll (Pos := Pos) ∘ (Prod.mk u) = H ∘ F := by
    funext y b
    rfl
  have hG_ae : AEMeasurable (blockDataOfWordPointsAll (Pos := Pos))
      ((Measure.pi (fun _ : Fin n => ν)).map (Prod.mk u)) := by
    let gu : (Fin n → Fin K) × (Fin n → Pos) → (Fin K → BlockData Pos) :=
      fun p => H (F p.2)
    have hgu : Measurable gu := hH.comp (hF.comp measurable_snd)
    have heq : blockDataOfWordPointsAll (Pos := Pos) =ᵐ[
        (Measure.pi (fun _ : Fin n => ν)).map (Prod.mk u)] gu := by
      rw [Filter.EventuallyEq, ae_iff]
      apply measure_mono_null (t := {x : (Fin n → Fin K) × (Fin n → Pos) | x.1 ≠ u})
      · intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        intro hxu
        apply hx
        cases x with
        | mk a b =>
          simp only at hxu
          subst hxu
          rfl
      · rw [Measure.map_apply measurable_prodMk_left (by measurability)]
        simp
    exact hgu.aemeasurable.congr heq.symm
  have hinner : (Measure.pi (fun _ : Fin n => ν)).map F =
      Measure.pi (fun b : Fin K => Measure.pi (fun _ : Fin (s b).card => ν)) :=
    map_pi_partition ν s hdisj hcover
  have hmap_pi : (Measure.pi (fun b : Fin K => Measure.pi (fun _ : Fin (s b).card => ν))).map H =
      Measure.pi (fun b : Fin K =>
        (Measure.pi (fun _ : Fin (s b).card => ν)).map
          (fun y => (⟨(s b).card, y⟩ : BlockData Pos))) := by
    haveI : ∀ b, IsProbabilityMeasure ((Measure.pi (fun _ : Fin (s b).card => ν)).map
        (fun y => (⟨(s b).card, y⟩ : BlockData Pos))) := fun b =>
      Measure.isProbabilityMeasure_map (measurable_blockMk (Pos := Pos) (s b).card).aemeasurable
    haveI : ∀ b, SigmaFinite ((Measure.pi (fun _ : Fin (s b).card => ν)).map
        (fun y => (⟨(s b).card, y⟩ : BlockData Pos))) := fun b => inferInstance
    exact Measure.pi_map_pi (fun b => (measurable_blockMk (Pos := Pos) (s b).card).aemeasurable)
  calc
    ((Measure.dirac u).prod (Measure.pi (fun _ : Fin n => ν))).map
        (blockDataOfWordPointsAll (Pos := Pos))
      = ((Measure.pi (fun _ : Fin n => ν)).map (Prod.mk u)).map
          (blockDataOfWordPointsAll (Pos := Pos)) := by rw [Measure.dirac_prod]
    _ = (Measure.pi (fun _ : Fin n => ν)).map
          (blockDataOfWordPointsAll (Pos := Pos) ∘ (Prod.mk u)) := by
        rw [AEMeasurable.map_map_of_aemeasurable hG_ae measurable_prodMk_left.aemeasurable]
    _ = (Measure.pi (fun _ : Fin n => ν)).map (H ∘ F) := by rw [hcomp]
    _ = ((Measure.pi (fun _ : Fin n => ν)).map F).map H := by
        rw [AEMeasurable.map_map_of_aemeasurable hH.aemeasurable hF.aemeasurable]
    _ = (Measure.pi (fun b : Fin K => Measure.pi (fun _ : Fin (s b).card => ν))).map H := by
        rw [hinner]
    _ = Measure.pi (fun b : Fin K =>
          (Measure.pi (fun _ : Fin (s b).card => ν)).map
            (fun y => (⟨(s b).card, y⟩ : BlockData Pos))) := hmap_pi
    _ = Measure.pi (fun b : Fin K =>
          (Measure.pi (fun _ : Fin (labelCount u b) => ν)).map
            (fun y => (⟨labelCount u b, y⟩ : BlockData Pos))) := by
        congr 1

private lemma aemeasurable_blockDataOfWordPointsAll_slice
    {n K : ℕ} [NeZero K] {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (u : Fin n → Fin K) :
    AEMeasurable (blockDataOfWordPointsAll (Pos := Pos))
      ((Measure.pi (fun _ : Fin n => ν)).map (Prod.mk u)) := by
  classical
  let s : Fin K → Finset (Fin n) := fun b => Finset.univ.filter (fun i => u i = b)
  let F : (Fin n → Pos) → (∀ b : Fin K, Fin (s b).card → Pos) :=
    fun y b j => y (((s b).orderIsoOfFin rfl) j).1
  let H : (∀ b : Fin K, Fin (s b).card → Pos) → (Fin K → BlockData Pos) :=
    fun z b => ⟨(s b).card, z b⟩
  have hF : Measurable F := measurable_pi_lambda _ (fun b =>
    measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro b
    exact (measurable_sigma_mk (s b).card).comp (measurable_pi_apply b)
  let gu : (Fin n → Fin K) × (Fin n → Pos) → (Fin K → BlockData Pos) :=
    fun p => H (F p.2)
  have hgu : Measurable gu := hH.comp (hF.comp measurable_snd)
  have heq : blockDataOfWordPointsAll (Pos := Pos) =ᵐ[
      (Measure.pi (fun _ : Fin n => ν)).map (Prod.mk u)] gu := by
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null (t := {x : (Fin n → Fin K) × (Fin n → Pos) | x.1 ≠ u})
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      intro hxu
      apply hx
      cases x with
      | mk a b =>
        simp only at hxu
        subst hxu
        rfl
    · rw [Measure.map_apply measurable_prodMk_left (by measurability)]
      simp
  exact hgu.aemeasurable.congr heq.symm

private lemma aemeasurable_blockDataOfWordPointsAll
    {n K : ℕ} [NeZero K] {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] :
    AEMeasurable (blockDataOfWordPointsAll (Pos := Pos))
      ((Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))).prod
        (Measure.pi (fun _ : Fin n => ν))) := by
  classical
  let ρ : Measure (Fin n → Fin K) := Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))
  let σ : Measure (Fin n → Pos) := Measure.pi (fun _ : Fin n => ν)
  let G : (Fin n → Fin K) × (Fin n → Pos) → (Fin K → BlockData Pos) :=
    blockDataOfWordPointsAll (Pos := Pos)
  have hprod : ρ.prod σ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • ((Measure.dirac u).prod σ)) := by
    conv_lhs => rw [show ρ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • Measure.dirac u) from (Measure.sum_smul_dirac ρ).symm]
    rw [Measure.prod_sum_left]
    congr 1
    funext u
    rw [Measure.prod_smul_left]
  rw [hprod]
  apply AEMeasurable.sum_measure
  intro u
  rw [Measure.dirac_prod]
  by_cases hc : ρ {u} = 0
  · rw [hc, zero_smul]
    exact aemeasurable_zero_measure
  · rw [aemeasurable_smul_measure_iff hc]
    exact aemeasurable_blockDataOfWordPointsAll_slice ν u

private lemma card_words_labelCount_eq_multinomial {n K : ℕ} [NeZero K]
    (k : {k : Fin K → ℕ // ∑ b, k b = n}) :
    Nat.card {u : Fin n → Fin K // labelCount u = k.1} =
      Nat.multinomial Finset.univ k.1 := by
  rw [show Nat.card {u : Fin n → Fin K // labelCount u = k.1} =
      Nat.card {u : Fin n → Fin K // ∀ b,
        (Finset.univ.filter fun i => u i = b).card = k.1 b} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun u => by
      simp [labelCount, funext_iff]))]
  exact card_words_with_counts k.1 k.2

set_option linter.style.haveILetI false in
/-- **Joint law of all blocks (fixed `n`).**  The joint law of the block data across all
labels is the multinomial mixture of the products of the conditional mark-cloud laws.  It is
*not* the product of the independent binomial laws `blockDataLaw ν (fiberCountLaw n K)`:
the block sizes satisfy `∑ b, k b = n`, so the multinomial count vector couples the blocks.
For a count vector `k` with `∑ b, k b = n`, the block sizes are exactly `k b` and, given
`k`, the mark clouds of the different labels are independent with laws `ν^{k b}`. -/
theorem map_blockData_joint {Ω Pos : Type*} [MeasurableSpace Ω] [MeasurableSpace Pos]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure Pos} [IsProbabilityMeasure ν]
    {n K : ℕ} [NeZero K] (w : Fin n → Ω → Fin K) (x : Fin n → Ω → Pos)
    (hw : ∀ i, Measurable (w i)) (hx : ∀ i, Measurable (x i))
    (hi : iIndepFun (fun i : Fin n => fun ξ => (w i ξ, x i ξ)) P)
    (hlaw_w : ∀ i, P.map (w i) = uniformMeasure (Fin K))
    (hlaw_x : ∀ i, P.map (x i) = ν)
    (hindep_wx : ∀ i, IndepFun (w i) (x i) P) :
    P.map (fun ξ => fun b : Fin K =>
        (⟨labelCount (fun i => w i ξ) b, blockPoints w x b ξ⟩ : BlockData Pos)) =
      Measure.sum (fun k : {k : Fin K → ℕ // ∑ b, k b = n} =>
        ((Nat.multinomial Finset.univ k.1 : ℝ≥0∞) *
          ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n) •
          Measure.pi (fun b : Fin K =>
            (Measure.pi (fun _ : Fin (k.1 b) => ν)).map
              (fun y => (⟨k.1 b, y⟩ : BlockData Pos)))) := by
  classical
  let ρ : Measure (Fin n → Fin K) := Measure.pi (fun _ : Fin n => uniformMeasure (Fin K))
  let σ : Measure (Fin n → Pos) := Measure.pi (fun _ : Fin n => ν)
  let G : (Fin n → Fin K) × (Fin n → Pos) → (Fin K → BlockData Pos) :=
    blockDataOfWordPointsAll (Pos := Pos)
  let Z' : Ω → (Fin n → Fin K) × (Fin n → Pos) := fun ξ => (fun i => w i ξ, fun i => x i ξ)
  let T : (Fin K → ℕ) → Measure (Fin K → BlockData Pos) := fun k =>
    Measure.pi (fun b : Fin K =>
      (Measure.pi (fun _ : Fin (k b) => ν)).map
        (fun y => (⟨k b, y⟩ : BlockData Pos)))
  have hZ'meas : Measurable Z' := (measurable_pi_lambda _ hw).prod (measurable_pi_lambda _ hx)
  have hpairlaw : ∀ i, P.map (fun ξ => (w i ξ, x i ξ)) = (uniformMeasure (Fin K)).prod ν := by
    intro i
    rw [(hindep_wx i).map_prod_eq_prod_map_map (hw i).aemeasurable (hx i).aemeasurable,
      hlaw_w i, hlaw_x i]
  have hZ : P.map (fun ξ i => (w i ξ, x i ξ)) =
      Measure.pi (fun _ : Fin n => (uniformMeasure (Fin K)).prod ν) := by
    have h := iIndepFun.map_fun_eq_pi_map
      (f := fun i : Fin n => fun ξ => (w i ξ, x i ξ))
      (fun i => (hw i).prod (hx i) |>.aemeasurable) hi
    rwa [show (fun i => P.map (fun ξ => (w i ξ, x i ξ))) =
      (fun _ : Fin n => (uniformMeasure (Fin K)).prod ν) from funext hpairlaw] at h
  have hZ' : P.map Z' = ρ.prod σ := by
    let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin K) Pos (Fin n)
    have hmap : P.map Z' = (P.map (fun ξ i => (w i ξ, x i ξ))).map e := by
      rw [Measure.map_map (μ := P) e.measurable (by
        exact measurable_pi_lambda _ (fun i => (hw i).prod (hx i)))]
      congr 1
    rw [hmap, hZ]
    exact (measurePreserving_arrowProdEquivProdArrow (Fin K) Pos (Fin n)
      (fun _ => uniformMeasure (Fin K)) (fun _ => ν)).map_eq
  have hG_ae : AEMeasurable G (P.map Z') := by
    rw [hZ']
    exact aemeasurable_blockDataOfWordPointsAll ν
  have hB : (fun ξ => fun b : Fin K =>
      (⟨labelCount (fun i => w i ξ) b, blockPoints w x b ξ⟩ : BlockData Pos)) = G ∘ Z' := by
    funext ξ b
    rfl
  rw [hB, ← AEMeasurable.map_map_of_aemeasurable hG_ae hZ'meas.aemeasurable, hZ']
  have hG_meas : AEMeasurable G (ρ.prod σ) := aemeasurable_blockDataOfWordPointsAll ν
  have hprod : ρ.prod σ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • ((Measure.dirac u).prod σ)) := by
    conv_lhs => rw [show ρ = Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • Measure.dirac u) from (Measure.sum_smul_dirac ρ).symm]
    rw [Measure.prod_sum_left]
    congr 1
    funext u
    rw [Measure.prod_smul_left]
  have hG_meas' : AEMeasurable G (Measure.sum (fun u : Fin n → Fin K =>
      (ρ {u}) • ((Measure.dirac u).prod σ))) := by
    rwa [← hprod]
  rw [hprod, Measure.map_sum hG_meas']
  simp_rw [Measure.map_smul]
  simp only [G]
  simp only [σ]
  simp_rw [map_blockDataOfWordPointsAll_slice ν]
  have hconst : ∀ u : Fin n → Fin K,
      (ρ {u}) = ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n := by
    intro u
    rw [Measure.pi_singleton]
    simp [uniformMeasure_singleton, Finset.prod_const]
  simp_rw [hconst]
  let κ := {k : Fin K → ℕ // ∑ b, k b = n}
  let toFin : κ → (Fin K → Fin (n + 1)) := fun k b =>
    ⟨k.1 b, by
      have hle : k.1 b ≤ ∑ c, k.1 c :=
        Finset.single_le_sum (s := Finset.univ) (f := fun c => k.1 c)
          (fun c _ => Nat.zero_le _) (Finset.mem_univ b)
      rw [k.2] at hle
      exact Nat.lt_succ_of_le hle⟩
  haveI : Fintype κ := Fintype.ofInjective toFin (by
    intro k l hkl
    apply Subtype.ext
    funext b
    exact Fin.ext_iff.mp (congrFun hkl b))
  simp_rw [Measure.sum_fintype]
  rw [← Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin n → Fin K)))
    (t := (Finset.univ : Finset {k : Fin K → ℕ // ∑ b, k b = n}))
    (g := fun u : Fin n → Fin K =>
      (⟨labelCount u, sum_labelCount u⟩ : {k : Fin K → ℕ // ∑ b, k b = n}))
    (f := fun k : {k : Fin K → ℕ // ∑ b, k b = n} =>
      ((Fintype.card (Fin K) : ℝ≥0∞)⁻¹) ^ n • T k.1)
    (fun u _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  congr 1
  have hcardNat : (Finset.univ.filter (fun u : Fin n → Fin K =>
      (⟨labelCount u, sum_labelCount u⟩ : {k : Fin K → ℕ // ∑ b, k b = n}) = k)).card =
      Nat.multinomial Finset.univ k.1 := by
    rw [show (Finset.univ.filter (fun u : Fin n → Fin K =>
        (⟨labelCount u, sum_labelCount u⟩ : {k : Fin K → ℕ // ∑ b, k b = n}) = k)).card =
        Nat.card {u : Fin n → Fin K //
          (⟨labelCount u, sum_labelCount u⟩ : {k : Fin K → ℕ // ∑ b, k b = n}) = k} from by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]]
    rw [show Nat.card {u : Fin n → Fin K //
        (⟨labelCount u, sum_labelCount u⟩ : {k : Fin K → ℕ // ∑ b, k b = n}) = k} =
        Nat.card {u : Fin n → Fin K // labelCount u = k.1} from
      Nat.card_congr (Equiv.subtypeEquivRight (fun u => by
        simp [Subtype.ext_iff]))]
    exact card_words_labelCount_eq_multinomial k
  rw [show ((Finset.univ.filter (fun u : Fin n → Fin K =>
      (⟨labelCount u, sum_labelCount u⟩ : {k : Fin K → ℕ // ∑ b, k b = n}) = k)).card : ℝ≥0∞) =
      (Nat.multinomial Finset.univ k.1 : ℝ≥0∞) from by rw [hcardNat]]

private lemma measurable_uFiber
    {n K : ℕ} {Pos : Type*} [MeasurableSpace Pos] (u : Fin n → Fin K) (b : Fin K) :
    Measurable (fun y : Fin n → Pos =>
      (⟨(Finset.univ.filter (fun i => u i = b)).card,
        fun j => y (((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl) j).1⟩ :
        BlockData Pos)) := by
  let s := Finset.univ.filter (fun i => u i = b)
  have hproj : Measurable (fun y : Fin n → Pos => fun j : Fin s.card =>
      y ((s.orderIsoOfFin rfl j).1)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  exact (measurable_blockMk (Pos := Pos) s.card).comp hproj

private lemma measurable_blockDataOfPairs
    {n K : ℕ} {Pos : Type*} [MeasurableSpace Pos] (b : Fin K) :
    Measurable (blockDataOfPairs (n := n) (Pos := Pos) b) := by
  classical
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin K) Pos (Fin n)
  have hcomp : Measurable ((blockDataOfPairs (n := n) (Pos := Pos) b) ∘ e.symm) := by
    intro S hS
    have hu : ∀ u : Fin n → Fin K,
        Measurable (fun y : Fin n → Pos =>
          (⟨(Finset.univ.filter (fun i => u i = b)).card,
            fun j => y (((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl) j).1⟩ :
            BlockData Pos)) := fun u => measurable_uFiber u b
    have hUnion : ((blockDataOfPairs (n := n) (Pos := Pos) b) ∘ e.symm) ⁻¹' S =
        ⋃ u : Fin n → Fin K,
          ({u} : Set (Fin n → Fin K)) ×ˢ
            ((fun y : Fin n → Pos =>
              (⟨(Finset.univ.filter (fun i => u i = b)).card,
                fun j => y (((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl) j).1⟩ :
                BlockData Pos)) ⁻¹' S) := by
      ext p
      constructor
      · intro hp
        change (blockDataOfPairs (n := n) (Pos := Pos) b) (e.symm p) ∈ S at hp
        have hval : (blockDataOfPairs (n := n) (Pos := Pos) b) (e.symm p) =
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
        change (blockDataOfPairs (n := n) (Pos := Pos) b) (e.symm p) ∈ S
        have hval : (blockDataOfPairs (n := n) (Pos := Pos) b) (e.symm p) =
            (⟨(Finset.univ.filter (fun i => p.1 i = b)).card,
              fun j => p.2 (((Finset.univ.filter (fun i => p.1 i = b)).orderIsoOfFin rfl) j).1⟩ :
              BlockData Pos) := by
          rfl
        rw [hval, hpu_eq]
        exact huf
    rw [hUnion]
    apply MeasurableSet.iUnion
    intro u
    exact MeasurableSet.prod (measurableSet_singleton u) ((hu u) hS)
  have hEq : blockDataOfPairs (n := n) (Pos := Pos) b =
      ((blockDataOfPairs (n := n) (Pos := Pos) b) ∘ e.symm) ∘ e := by
    funext z
    simp [e]
  rw [hEq]
  exact hcomp.comp e.measurable

private lemma map_poisson_prefix
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Λ : ℝ≥0) (N : Ω → ℕ) (Y : ∀ _n, Ω → β)
    (hN : P.map N = poissonMeasure Λ)
    (hY : ∀ n, Measurable (Y n))
    (hindep : ∀ n, IndepFun N (Y n) P) :
    P.map (fun ξ => Y (N ξ) ξ) =
      Measure.sum (fun n => poissonMeasure Λ {n} • P.map (Y n)) := by
  classical
  have hNae : AEMeasurable N P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hN]
    exact IsProbabilityMeasure.ne_zero (poissonMeasure Λ)
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
      poissonMeasure Λ {n} * (P.map (Y n)) S := by
    rw [(hindep n).measure_inter_preimage_eq_mul {n} S
      (measurableSet_singleton n) hS]
    congr 1
    · rw [← Measure.map_apply_of_aemeasurable hNae (measurableSet_singleton n), hN]
    · rw [Measure.map_apply_of_aemeasurable (hY n).aemeasurable hS]
  simp_rw [hterm]
  rw [Measure.sum_apply _ hS]
  simp_rw [Measure.smul_apply, smul_eq_mul]

private lemma prefixCount_mass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n K : ℕ} [NeZero K] (w : Fin n → Ω → Fin K) (b : Fin K)
    (hw : ∀ i, AEMeasurable (w i) P)
    (hi : iIndepFun w P)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K)) (m : ℕ) :
    P ((fun ξ => (Finset.univ.filter (fun i => w i ξ = b)).card) ⁻¹' {m}) =
      fiberCountLaw n K m := by
  classical
  let W : Ω → Fin n → Fin K := fun ξ i => w i ξ
  have hWmeas : AEMeasurable W P := aemeasurable_pi_lambda _ hw
  have hWlaw : P.map W = Measure.pi (fun _ : Fin n => uniformMeasure (Fin K)) := by
    have h := iIndepFun.map_fun_eq_pi_map (f := w) hw hi
    rwa [show (fun i => P.map (w i)) =
      (fun _ : Fin n => uniformMeasure (Fin K)) from funext hlaw] at h
  have hS : MeasurableSet {u : Fin n → Fin K |
      (Finset.univ.filter (fun i => u i = b)).card = m} :=
    (measurableSet_singleton m).preimage
      (measurable_of_countable (fun u : Fin n → Fin K =>
        (Finset.univ.filter (fun i => u i = b)).card))
  have hpre : (fun ξ => (Finset.univ.filter (fun i => w i ξ = b)).card) ⁻¹' {m} =
      W ⁻¹' {u : Fin n → Fin K |
        (Finset.univ.filter (fun i => u i = b)).card = m} := by
    ext ξ
    simp [W]
  rw [hpre, ← Measure.map_apply_of_aemeasurable hWmeas hS, hWlaw]
  exact pi_uniform_fiber_count b m

private lemma aemeasurable_prefixLabelCount
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K)
    (hN : P.map N = poissonMeasure Λ)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K)) :
    AEMeasurable (fun ξ => fun b : Fin K =>
      (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card) P := by
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
  let mkCount : Ω → (Fin K → ℕ) := fun ξ b =>
    (Finset.univ.filter fun i : Fin (hNae.mk N ξ) => (hwae i).mk (w i) ξ = b).card
  have hmkCount : Measurable mkCount := by
    apply measurable_to_countable'
    intro k
    have hset : {ξ | mkCount ξ = k} =
        ⋃ n, ({ξ | hNae.mk N ξ = n} ∩
          {ξ | (fun b => (Finset.univ.filter fun i : Fin n =>
            (hwae i).mk (w i) ξ = b).card) = k}) := by
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
    · exact ((measurable_of_countable (fun ω : Fin n → Fin K => fun b =>
        (Finset.univ.filter fun i => ω i = b).card)).comp
        (measurable_pi_lambda _ (fun i => hmkw i))) (measurableSet_singleton k)
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

private lemma aemeasurable_prefixCount_single
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K) (b : Fin K)
    (hN : P.map N = poissonMeasure Λ)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K)) :
    AEMeasurable (fun ξ =>
      (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card) P :=
  (measurable_pi_apply b).aemeasurable.comp_aemeasurable
    (aemeasurable_prefixLabelCount Λ N w hN hlaw)

private lemma map_prefixCount_mass_tsum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K) (b : Fin K)
    (hN : P.map N = poissonMeasure Λ)
    (hlabel : ∀ n, iIndepFun (fun i : Fin n => w i) P)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K))
    (hindep : ∀ n, IndepFun N (fun ξ => fun i : Fin n => w i ξ) P) (m : ℕ) :
    (P.map (fun ξ => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card)) {m} =
      ∑' n, poissonMeasure Λ {n} * fiberCountLaw n K m := by
  classical
  let C : Ω → ℕ := fun ξ => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card
  have hCae : AEMeasurable C P := aemeasurable_prefixCount_single Λ N w b hN hlaw
  rw [Measure.map_apply_of_aemeasurable hCae (measurableSet_singleton m)]
  change P (C ⁻¹' {m}) = _
  let Y : ℕ → Ω → ℕ := fun n ξ =>
    (Finset.univ.filter fun i : Fin n => w i ξ = b).card
  have hwae : ∀ i : ℕ, AEMeasurable (w i) P := by
    intro i
    apply AEMeasurable.of_map_ne_zero
    rw [hlaw i]
    exact IsProbabilityMeasure.ne_zero (uniformMeasure (Fin K))
  have hYae : ∀ n, AEMeasurable (Y n) P := by
    intro n
    have hW : AEMeasurable (fun ξ => fun i : Fin n => w i ξ) P :=
      aemeasurable_pi_lambda _ (fun i => hwae i)
    have hcount : Measurable (fun u : Fin n → Fin K =>
        (Finset.univ.filter fun i => u i = b).card) :=
      measurable_of_countable _
    exact hcount.comp_aemeasurable hW
  have hindepY : ∀ n, IndepFun N (Y n) P := by
    intro n
    have hcount : Measurable (fun u : Fin n → Fin K =>
        (Finset.univ.filter fun i => u i = b).card) :=
      measurable_of_countable _
    have h := (hindep n).comp measurable_id hcount
    simpa [Function.comp_def, id_eq, Y] using h
  have hUnion : C ⁻¹' {m} = ⋃ n, (N ⁻¹' {n}) ∩ (Y n ⁻¹' {m}) := by
    ext ξ
    simp only [C, Y, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨N ξ, rfl, h⟩
    · rintro ⟨n, hn, hk⟩; subst hn; exact hk
  have hNae : AEMeasurable N P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hN]
    exact IsProbabilityMeasure.ne_zero (poissonMeasure Λ)
  have hNull (n : ℕ) : NullMeasurableSet ((N ⁻¹' {n}) ∩ (Y n ⁻¹' {m})) P := by
    apply NullMeasurableSet.inter
    · exact hNae.nullMeasurableSet_preimage (measurableSet_singleton n)
    · exact (hYae n).nullMeasurableSet_preimage (measurableSet_singleton m)
  have hdisj : Pairwise (Function.onFun (AEDisjoint P)
      (fun n => (N ⁻¹' {n}) ∩ (Y n ⁻¹' {m}))) := by
    intro p q hpq
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro ξ hξp hξq
    exact hpq (hξp.1.symm.trans hξq.1)
  rw [hUnion, measure_iUnion₀ hdisj hNull]
  have hterm (n : ℕ) : P ((N ⁻¹' {n}) ∩ (Y n ⁻¹' {m})) =
      poissonMeasure Λ {n} * fiberCountLaw n K m := by
    rw [(hindepY n).measure_inter_preimage_eq_mul {n} {m}
      (measurableSet_singleton n) (measurableSet_singleton m)]
    congr 1
    · rw [← Measure.map_apply_of_aemeasurable hNae (measurableSet_singleton n), hN]
    · simpa [Y] using prefixCount_mass (w := fun i : Fin n => w i) b
        (fun i => hwae i) (hlabel n) (fun i => hlaw i) m
  simp_rw [hterm]

private lemma map_prefixCount_single_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ} [NeZero K] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K) (b : Fin K)
    (hN : P.map N = poissonMeasure Λ)
    (hlabel : ∀ n, iIndepFun (fun i : Fin n => w i) P)
    (hlaw : ∀ i, P.map (w i) = uniformMeasure (Fin K))
    (hindep : ∀ n, IndepFun N (fun ξ => fun i : Fin n => w i ξ) P) :
    P.map (fun ξ => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card) =
      poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) := by
  classical
  let V : Ω → Fin K → ℕ := fun ξ b =>
    (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card
  have hVae : AEMeasurable V P := aemeasurable_prefixLabelCount Λ N w hN hlaw
  have hVlaw : P.map V = Measure.pi (fun _ : Fin K =>
      poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0))) :=
    map_poisson_label_counts Λ N w hN hlabel hlaw hindep
  rw [show (fun ξ => (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card) =
      Function.eval b ∘ V from rfl]
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply b).aemeasurable hVae,
    hVlaw, Measure.pi_map_eval]
  simp [measure_univ]

private lemma blockDataLaw_poisson_mix
    {K : ℕ} [NeZero K] {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (Λ : ℝ≥0)
    (hthin : ∀ m, (∑' n, poissonMeasure Λ {n} * fiberCountLaw n K m) =
      poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {m}) :
    Measure.sum (fun n => poissonMeasure Λ {n} • blockDataLaw ν (fiberCountLaw n K)) =
      blockDataLaw ν (fun m =>
        poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {m}) := by
  classical
  let G : ℕ → Measure (BlockData Pos) := fun m =>
    (Measure.pi (fun _ : Fin m => ν)).map (fun y => (⟨m, y⟩ : BlockData Pos))
  have hBD : ∀ (prob : ℕ → ℝ≥0∞) (S : Set (BlockData Pos)), MeasurableSet S →
      (blockDataLaw ν prob) S = ∑' m, prob m * G m S := by
    intro prob S hS
    rw [blockDataLaw, Measure.sum_apply _ hS]
    simp_rw [Measure.smul_apply, smul_eq_mul]
    simp only [G]
  ext S hS
  rw [Measure.sum_apply _ hS]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  have hval (n : ℕ) : (blockDataLaw ν (fiberCountLaw n K)) S =
      ∑' m, fiberCountLaw n K m * G m S := hBD (fiberCountLaw n K) S hS
  simp_rw [hval]
  rw [hBD (fun m => poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {m}) S hS]
  calc
    (∑' n, poissonMeasure Λ {n} *
        (∑' m, fiberCountLaw n K m * G m S))
        = ∑' n, ∑' m, poissonMeasure Λ {n} *
            (fiberCountLaw n K m * G m S) := by
          congr 1 with n
          rw [ENNReal.tsum_mul_left]
    _ = ∑' m, ∑' n, poissonMeasure Λ {n} *
            (fiberCountLaw n K m * G m S) :=
          ENNReal.tsum_comm
    _ = ∑' m, (∑' n, poissonMeasure Λ {n} * fiberCountLaw n K m) * G m S := by
          congr 1 with m
          rw [← ENNReal.tsum_mul_right]
          congr 1 with n
          ring
    _ = ∑' m, poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {m} * G m S := by
          congr 1 with m
          rw [hthin m]

/-- The marked block attached to label `b` among the first `N ξ` pairs. -/
def prefixBlockData {K : ℕ} {Ω Pos : Type*} [MeasurableSpace Pos]
    (N : Ω → ℕ) (w : ℕ → Ω → Fin K) (x : ℕ → Ω → Pos) (b : Fin K) (ξ : Ω) :
    BlockData Pos :=
  let s := Finset.univ.filter (fun i : Fin (N ξ) => w i ξ = b)
  ⟨s.card, fun j => x ((s.orderIsoOfFin rfl) j).1 ξ⟩

set_option linter.style.haveILetI false in
/-- **Poisson marked splitting.**  Let `N` be Poisson with rate `Λ`, independent of every
finite prefix of an iid sequence of uniform labels and iid `ν`-marks.  Then the marked block
of a single label has law `blockDataLaw ν (fun m => poissonMeasure (Λ / K) {m})`: its size
is Poisson with rate `Λ / K` and, conditionally on the size, its marks are iid `ν`. -/
theorem map_poisson_blockData
    {Ω Pos : Type*} [MeasurableSpace Ω] [MeasurableSpace Pos]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure Pos} [IsProbabilityMeasure ν]
    {K : ℕ} [NeZero K] (Λ : ℝ≥0) (N : Ω → ℕ) (w : ℕ → Ω → Fin K) (x : ℕ → Ω → Pos)
    (hN : P.map N = poissonMeasure Λ)
    (hpair : ∀ n, iIndepFun (fun i : Fin n => fun ξ => (w i ξ, x i ξ)) P)
    (hw : ∀ i, Measurable (w i)) (hx : ∀ i, Measurable (x i))
    (hlaw_w : ∀ i, P.map (w i) = uniformMeasure (Fin K))
    (hlaw_x : ∀ i, P.map (x i) = ν)
    (hindep_wx : ∀ i, IndepFun (w i) (x i) P)
    (hindep : ∀ n, IndepFun N (fun ξ => fun i : Fin n => (w i ξ, x i ξ)) P)
    (b : Fin K) :
    P.map (prefixBlockData N w x b) =
      blockDataLaw ν (fun m =>
        poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {m}) := by
  classical
  have hlabel : ∀ n, iIndepFun (fun i : Fin n => w i) P := by
    intro n
    have h := (hpair n).comp (fun i => fun p : Fin K × Pos => p.1)
      (fun i => measurable_fst)
    simpa [Function.comp_def] using h
  have hindep_label : ∀ n, IndepFun N (fun ξ => fun i : Fin n => w i ξ) P := by
    intro n
    have hproj : Measurable (fun p : Fin n → Fin K × Pos =>
        fun i : Fin n => (p i).1) :=
      measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))
    have h := (hindep n).comp measurable_id hproj
    simpa [Function.comp_def, id_eq] using h
  let Y : ∀ n, Ω → BlockData Pos := fun n ξ =>
    blockDataOfPairs (n := n) (Pos := Pos) b (fun i : Fin n => (w i ξ, x i ξ))
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    exact (measurable_blockDataOfPairs (n := n) (Pos := Pos) b).comp
      (measurable_pi_lambda _ (fun i => (hw i).prod (hx i)))
  have hindepY : ∀ n, IndepFun N (Y n) P := by
    intro n
    have h := (hindep n).comp measurable_id
      (measurable_blockDataOfPairs (n := n) (Pos := Pos) b)
    simpa [Function.comp_def, id_eq, Y] using h
  have hpoisson := map_poisson_prefix Λ N Y hN hY hindepY
  have hYlaw : ∀ n, P.map (Y n) = blockDataLaw ν (fiberCountLaw n K) := by
    intro n
    have h := map_blockData (ν := ν) (w := fun i : Fin n => w i)
      (x := fun i : Fin n => x i) (fun i => hw i) (fun i => hx i)
      (hpair n) (fun i => hlaw_w i) (fun i => hlaw_x i)
      (fun i => hindep_wx i) b
    have hfun : (fun ξ => (⟨labelCount (n := n) (fun i : Fin n => w i ξ) b,
        blockPoints (n := n) (fun i : Fin n => w i) (fun i : Fin n => x i) b ξ⟩ :
        BlockData Pos)) = Y n := by
      funext ξ
      rfl
    rw [← hfun]
    exact h
  rw [show (fun ξ => Y (N ξ) ξ) = prefixBlockData N w x b from rfl] at hpoisson
  simp_rw [hYlaw] at hpoisson
  have hthin : ∀ m, (∑' n, poissonMeasure Λ {n} * fiberCountLaw n K m) =
      poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {m} := by
    intro m
    have hlawC := map_prefixCount_single_law Λ N w b hN hlabel hlaw_w hindep_label
    have hmassC := map_prefixCount_mass_tsum Λ N w b hN hlabel hlaw_w hindep_label m
    calc (∑' n, poissonMeasure Λ {n} * fiberCountLaw n K m)
        = (P.map (fun ξ =>
            (Finset.univ.filter fun i : Fin (N ξ) => w i ξ = b).card)) {m} :=
          hmassC.symm
      _ = poissonMeasure (Λ / (Fintype.card (Fin K) : ℝ≥0)) {m} :=
          congrArg (fun μ : Measure ℕ => μ {m}) hlawC
  rw [hpoisson]
  exact blockDataLaw_poisson_mix ν Λ hthin

end OTSelector.Probability
