import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.InfiniteProductLaw
import OTSelector.Probability.PoissonLabelSplittingGeneral
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
# Tile labels and label-count discrepancy of marked Poisson clouds

A marked cloud on the unit cube carries a mark in `C × A`, where the first
coordinate `C` selects a tile and the second is the local mark.  This module
studies the tile labels `markLabel i z = (z.2 i).2.1` of the points of such a
cloud:

* the labels of the points are independent, and each label has the law of the
  first coordinate of the mark law `α`;
* when `C` is finite and the label marginal of `α` is the weighted law
  `∑ c, w c • δ c`, the vector of label counts of a cloud is a product of
  independent Poisson laws of rates `r * w c`;
* consequently two independent clouds with the same label marginal have
  expected total label-count discrepancy at most
  `sqrt (2 * r * card C)`.

The proofs follow `MarkedBlockLaw` and `PoissonLabelSplittingGeneral`: read the
labels off the iid mark sequence, lift independence from the sequence to the
Poissonized cloud, and apply the general weighted Poisson splitting law after
transporting the finite label type `C` to `Fin (card C)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

/-! ## The tile label of a point -/

/-- The label of the `i`-th point. -/
def markLabel {q : ℕ} {C A : Type*} (i : ℕ) (z : MarkedCloudSpace q (C × A)) : C :=
  (z.2 i).2.1

/-- The label of the `i`-th point is measurable. -/
theorem measurable_markLabel {q : ℕ} {C A : Type*} [MeasurableSpace C] [MeasurableSpace A]
    (i : ℕ) : Measurable fun z : MarkedCloudSpace q (C × A) => markLabel i z := by
  unfold markLabel
  fun_prop

/-- The vector of label counts of a marked cloud. -/
def markLabelCounts {q : ℕ} {C A : Type*} [DecidableEq C]
    (z : MarkedCloudSpace q (C × A)) : C → ℕ :=
  fun c => (Finset.univ.filter (fun i : Fin z.1 => markLabel (i : ℕ) z = c)).card

/-! ## Independence of the tile labels

The two lemmas below are the label analogue of `iIndepFun_markedLabelCode` in
`MarkedBlockLaw`: independence is first proved for the iid sequence law and then
lifted to the Poissonized product with an independent count. -/

/-- Random variables defined on the second factor of a product of probability
spaces inherit their independence. -/
theorem iIndepFun_snd_prod_marked {ι Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {ν₁ : Measure Ω₁} [IsProbabilityMeasure ν₁]
    {ν₂ : Measure Ω₂} [IsProbabilityMeasure ν₂] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {Y : ∀ i, Ω₂ → β i}
    (mY : ∀ i, Measurable (Y i)) (hY : iIndepFun Y ν₂) :
    iIndepFun (fun i (p : Ω₁ × Ω₂) => Y i p.2) (ν₁.prod ν₂) := by
  exact iIndepFun_snd_prod mY hY

/-- Coordinates of an infinite product of a probability measure are independent. -/
theorem iIndepFun_infinitePi_eval_comp {Pos β : Type*} [MeasurableSpace Pos]
    [MeasurableSpace β] (ν : Measure Pos) [IsProbabilityMeasure ν]
    (g : Pos → β) (hg : Measurable g) :
    iIndepFun (fun (i : ℕ) (s : ℕ → Pos) => g (s i))
      (Measure.infinitePi (fun _ : ℕ => ν)) := by
  exact iIndepFun_infinitePi_apply_comp ν g hg

/-- **Independence of the tile labels.**  The labels of the points of a marked
Poisson cloud are independent. -/
theorem iIndepFun_markLabel (q : ℕ) {C A : Type*} [MeasurableSpace C] [MeasurableSpace A]
    [MeasurableSingletonClass C]
    (α : Measure (C × A)) [IsProbabilityMeasure α] (r : ℝ≥0) :
    iIndepFun (fun (i : ℕ) (z : MarkedCloudSpace q (C × A)) => markLabel i z)
      (markedPoissonLaw (q := q) (C × A) α r) := by
  have : IsProbabilityMeasure (markedSeqLaw (q := q) (C × A) α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) (C × A) α
  have : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  have hcube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  have hmeas : Measurable (fun y : (Fin q → ℝ) × (C × A) => y.2.1) := by
    fun_prop
  have hseq : iIndepFun (fun (i : ℕ) (s : ℕ → (Fin q → ℝ) × (C × A)) =>
      (s i).2.1) (markedSeqLaw (q := q) (C × A) α) := by
    rw [markedSeqLaw]
    exact iIndepFun_infinitePi_eval_comp ((cubeMeasure (Fin q) 1).prod α)
      (fun y => y.2.1) hmeas
  rw [markedPoissonLaw]
  exact iIndepFun_snd_prod_marked
    (ν₁ := poissonMeasure r) (ν₂ := markedSeqLaw (q := q) (C × A) α)
    (Y := fun i s => (s i).2.1)
    (fun i => hmeas.comp (measurable_pi_apply i)) hseq

/-- **The label law.**  Every label of a marked Poisson cloud has the law of the
first coordinate of the mark law. -/
theorem map_markLabel (q : ℕ) {C A : Type*} [MeasurableSpace C] [MeasurableSpace A]
    [MeasurableSingletonClass C]
    (α : Measure (C × A)) [IsProbabilityMeasure α] (r : ℝ≥0) (i : ℕ) :
    (markedPoissonLaw (q := q) (C × A) α r).map (fun z => markLabel i z) =
      α.map Prod.fst := by
  have : IsProbabilityMeasure (markedSeqLaw (q := q) (C × A) α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) (C × A) α
  have : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  have hcube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  have hg : Measurable (fun s : ℕ → (Fin q → ℝ) × (C × A) => (s i).2.1) := by
    fun_prop
  have hseq : (markedSeqLaw (q := q) (C × A) α).map
      (fun s : ℕ → (Fin q → ℝ) × (C × A) => (s i).2.1) = α.map Prod.fst := by
    rw [markedSeqLaw]
    rw [show (fun s : ℕ → (Fin q → ℝ) × (C × A) => (s i).2.1) =
        (fun y : (Fin q → ℝ) × (C × A) => y.2.1) ∘ Function.eval i from rfl,
      ← Measure.map_map (by fun_prop :
        Measurable (fun y : (Fin q → ℝ) × (C × A) => y.2.1)) (measurable_pi_apply i),
      Measure.infinitePi_map_eval]
    calc ((cubeMeasure (Fin q) 1).prod α).map (fun y : (Fin q → ℝ) × (C × A) => y.2.1)
        = ((cubeMeasure (Fin q) 1).prod α).map (Prod.fst ∘ Prod.snd) := rfl
      _ = (((cubeMeasure (Fin q) 1).prod α).map Prod.snd).map Prod.fst := by
          rw [Measure.map_map measurable_fst measurable_snd]
      _ = ((cubeMeasure (Fin q) 1) Set.univ • α).map Prod.fst := by
          rw [Measure.map_snd_prod]
      _ = (cubeMeasure (Fin q) 1) Set.univ • (α.map Prod.fst) := by
          rw [Measure.map_smul]
      _ = α.map Prod.fst := by simp
  rw [markedPoissonLaw]
  rw [show (fun z : MarkedCloudSpace q (C × A) => markLabel i z) =
      (fun s : ℕ → (Fin q → ℝ) × (C × A) => (s i).2.1) ∘ Prod.snd from rfl,
    ← Measure.map_map hg measurable_snd]
  rw [Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact hseq

/-! ## Measurability of the label counts -/

/-- A single coordinate of the label-count vector is measurable. -/
theorem measurable_markLabelCount (q : ℕ) {C A : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [Countable C] [MeasurableSingletonClass C] [DecidableEq C]
    (c : C) :
    Measurable (fun z : MarkedCloudSpace q (C × A) =>
      (Finset.univ.filter (fun i : Fin z.1 => markLabel (i : ℕ) z = c)).card) := by
  classical
  apply measurable_to_countable'
  intro n
  have hset : {z : MarkedCloudSpace q (C × A) |
      (Finset.univ.filter (fun i : Fin z.1 => markLabel (i : ℕ) z = c)).card = n} =
      ⋃ m, ({z | z.1 = m} ∩
        {z | (Finset.univ.filter (fun i : Fin m => markLabel (i : ℕ) z = c)).card = n}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨z.1, rfl, h⟩
    · rintro ⟨m, hm, h⟩; subst hm; exact h
  change MeasurableSet {z : MarkedCloudSpace q (C × A) |
    (Finset.univ.filter (fun i : Fin z.1 => markLabel (i : ℕ) z = c)).card = n}
  rw [hset]
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.inter
  · exact measurable_fst (measurableSet_singleton m)
  · have hcount : Measurable (fun v : Fin m → C =>
        (Finset.univ.filter (fun i : Fin m => v i = c)).card) :=
      measurable_of_countable _
    exact hcount.comp (measurable_pi_lambda _ (fun i => measurable_markLabel (i : ℕ)))
      (measurableSet_singleton n)

/-- The vector of label counts is measurable. -/
theorem measurable_markLabelCounts (q : ℕ) {C A : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [Countable C] [MeasurableSingletonClass C] [DecidableEq C] :
    Measurable (markLabelCounts (q := q) (C := C) (A := A)) := by
  rw [measurable_pi_iff]
  intro c
  exact measurable_markLabelCount q c

/-! ## Transport along an equivalence of label types -/

/-- An equivalence of finite types pushes a weighted sum of Dirac measures to the
corresponding weighted sum over the target type. -/
theorem map_sum_smul_dirac_equiv_marked {C D : Type*} [Fintype C] [Fintype D]
    [MeasurableSpace C] [MeasurableSpace D]
    [MeasurableSingletonClass C] [MeasurableSingletonClass D]
    (e : C ≃ D) (w : C → ℝ≥0) :
    Measure.map e (Measure.sum (fun c : C => (w c : ℝ≥0∞) • Measure.dirac c)) =
      Measure.sum (fun d : D => (w (e.symm d) : ℝ≥0∞) • Measure.dirac d) := by
  classical
  refine Measure.ext_of_singleton (fun d => ?_)
  rw [Measure.map_apply (measurable_of_countable e) (measurableSet_singleton d)]
  rw [show e ⁻¹' {d} = {e.symm d} by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.eq_symm_apply]]
  rw [Measure.sum_smul_dirac_singleton, Measure.sum_smul_dirac_singleton]

/-! ## The law of the label counts -/

/-- **The label-count law.**  If the label marginal of the mark law is the
weighted law `∑ c, w c • δ c`, then the vector of tile-label counts of a marked
Poisson cloud of intensity `r` has independent Poisson coordinates of rates
`r * w c`. -/
theorem map_markLabelCounts
    (q : ℕ) {C A : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace A]
    (α : Measure (C × A)) [IsProbabilityMeasure α] (r : ℝ≥0)
    (w : C → ℝ≥0) (hwsum : ∑ c, w c = 1)
    (hlabel_law : α.map Prod.fst = Measure.sum (fun c => (w c : ℝ≥0∞) • Measure.dirac c)) :
    (markedPoissonLaw (q := q) (C × A) α r).map
      (fun z => fun c : C =>
        (Finset.univ.filter (fun i : Fin z.1 => markLabel (i : ℕ) z = c)).card) =
      Measure.pi (fun c : C => poissonMeasure (r * w c)) := by
  classical
  change (markedPoissonLaw (q := q) (C × A) α r).map
      (markLabelCounts (q := q) (C := C) (A := A)) =
      Measure.pi (fun c : C => poissonMeasure (r * w c))
  have : IsProbabilityMeasure (markedPoissonLaw (q := q) (C × A) α r) := inferInstance
  have hK : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let p : Fin (Fintype.card C) → ℝ≥0 := fun k => w (e.symm k)
  have hp : ∑ k, p k = 1 := by
    rw [← Fintype.sum_equiv e w p (fun c => by simp [p])]
    exact hwsum
  let f : ℕ → MarkedCloudSpace q (C × A) → Fin (Fintype.card C) :=
    fun i z => e (markLabel i z)
  have hN : (markedPoissonLaw (q := q) (C × A) α r).map (fun z => z.1) = poissonMeasure r := by
    rw [markedPoissonLaw]
    show Measure.map Prod.fst ((poissonMeasure r).prod
      (markedSeqLaw (q := q) (C × A) α)) = poissonMeasure r
    rw [Measure.map_fst_prod]
    simp
  have hw : ∀ n, iIndepFun (fun i : Fin n => f i)
      (markedPoissonLaw (q := q) (C × A) α r) := by
    intro n
    have hbase := iIndepFun_markLabel (q := q) (C := C) (A := A) α r
    have h1 : iIndepFun (fun i : Fin n =>
        fun z : MarkedCloudSpace q (C × A) => markLabel (i : ℕ) z)
        (markedPoissonLaw (q := q) (C × A) α r) :=
      hbase.precomp (g := fun i : Fin n => (i : ℕ)) (fun i j hij => Fin.ext hij)
    exact h1.comp (fun _ : Fin n => e) (fun _ => measurable_of_countable e)
  have hlabel_map : Measure.map e
      (Measure.sum (fun c : C => (w c : ℝ≥0∞) • Measure.dirac c)) =
      Measure.sum (fun k : Fin (Fintype.card C) => (p k : ℝ≥0∞) • Measure.dirac k) := by
    simpa only [p] using map_sum_smul_dirac_equiv_marked e w
  have hlaw : ∀ i, (markedPoissonLaw (q := q) (C × A) α r).map (f i) =
      Measure.sum (fun k : Fin (Fintype.card C) => (p k : ℝ≥0∞) • Measure.dirac k) := by
    intro i
    have hcomp : f i = e ∘ (fun z : MarkedCloudSpace q (C × A) => markLabel i z) := rfl
    rw [hcomp, ← Measure.map_map (measurable_of_countable e) (measurable_markLabel i)]
    rw [map_markLabel (q := q) (C := C) (A := A) α r i, hlabel_law, hlabel_map]
  have hindep : ∀ n, IndepFun (fun z : MarkedCloudSpace q (C × A) => z.1)
      (fun ξ => fun i : Fin n => f i ξ) (markedPoissonLaw (q := q) (C × A) α r) := by
    intro n
    have : IsProbabilityMeasure (poissonMeasure r) := inferInstance
    have : IsProbabilityMeasure (markedSeqLaw (q := q) (C × A) α) :=
      isProbabilityMeasure_markedSeqLaw (q := q) (C × A) α
    have hvec : Measurable (fun s : ℕ → (Fin q → ℝ) × (C × A) =>
        fun i : Fin n => e ((s i).2.1)) :=
      measurable_pi_lambda _ (fun i => (measurable_of_countable e).comp
        (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply (i : ℕ)))))
    have h := indepFun_prod (μ := poissonMeasure r)
      (ν := markedSeqLaw (q := q) (C × A) α) measurable_id hvec
    simpa only [Function.comp_def, id_eq, markedPoissonLaw, f, markLabel] using h
  have hsplit := map_poisson_label_counts_general (Λ := r)
    (N := fun z : MarkedCloudSpace q (C × A) => z.1) (w := f) (p := p)
    hp hN hw hlaw hindep
  let E : (Fin (Fintype.card C) → ℕ) ≃ᵐ (C → ℕ) :=
    MeasurableEquiv.piCongrLeft (fun _ : C => ℕ) e.symm
  have hE_symm_apply : ∀ (v : C → ℕ) (k : Fin (Fintype.card C)),
      E.symm v k = v (e.symm k) := by
    intro v k
    change (Equiv.piCongrLeft (fun _ : C => ℕ) e.symm).symm v k = v (e.symm k)
    rw [Equiv.piCongrLeft_symm_apply]
  have hg : Measurable (markLabelCounts (q := q) (C := C) (A := A)) :=
    measurable_markLabelCounts q
  have hg'_eq : (fun z : MarkedCloudSpace q (C × A) =>
      fun k : Fin (Fintype.card C) =>
        (Finset.univ.filter (fun i : Fin z.1 => f i z = k)).card) =
      E.symm ∘ markLabelCounts := by
    funext z k
    rw [Function.comp_apply, hE_symm_apply]
    show (Finset.univ.filter (fun i : Fin z.1 => e (markLabel (i : ℕ) z) = k)).card =
      (Finset.univ.filter (fun i : Fin z.1 => markLabel (i : ℕ) z = e.symm k)).card
    congr 1
    apply Finset.filter_congr
    intro i _
    exact (Equiv.eq_symm_apply e).symm
  have h1 : (markedPoissonLaw (q := q) (C × A) α r).map
      (fun z => fun k : Fin (Fintype.card C) =>
        (Finset.univ.filter (fun i : Fin z.1 => f i z = k)).card) =
      ((markedPoissonLaw (q := q) (C × A) α r).map
        (markLabelCounts (q := q) (C := C) (A := A))).map E.symm := by
    rw [hg'_eq, Measure.map_map E.symm.measurable hg]
  have hsplit' : (markedPoissonLaw (q := q) (C × A) α r).map
      (fun z => fun k : Fin (Fintype.card C) =>
        (Finset.univ.filter (fun i : Fin z.1 => f i z = k)).card) =
      Measure.pi (fun k : Fin (Fintype.card C) => poissonMeasure (r * p k)) := by
    simpa only [] using hsplit
  have hEE : (((markedPoissonLaw (q := q) (C × A) α r).map
        (markLabelCounts (q := q) (C := C) (A := A))).map E.symm).map E =
      (markedPoissonLaw (q := q) (C × A) α r).map
        (markLabelCounts (q := q) (C := C) (A := A)) := by
    rw [Measure.map_map E.measurable E.symm.measurable]
    have hcomp : E ∘ E.symm = id := by
      funext v
      exact E.apply_symm_apply v
    rw [hcomp, Measure.map_id]
  have hpi : (Measure.pi (fun k : Fin (Fintype.card C) => poissonMeasure (r * p k))).map E =
      Measure.pi (fun c : C => poissonMeasure (r * w c)) := by
    have h := Measure.pi_map_piCongrLeft (e := e.symm)
      (μ := fun c : C => poissonMeasure (r * w c))
    simpa only [E, p] using h
  calc (markedPoissonLaw (q := q) (C × A) α r).map
        (markLabelCounts (q := q) (C := C) (A := A))
      = (((markedPoissonLaw (q := q) (C × A) α r).map
          (markLabelCounts (q := q) (C := C) (A := A))).map E.symm).map E :=
        hEE.symm
    _ = ((markedPoissonLaw (q := q) (C × A) α r).map
          (fun z => fun k : Fin (Fintype.card C) =>
            (Finset.univ.filter (fun i : Fin z.1 => f i z = k)).card)).map E := by
          rw [← h1]
    _ = (Measure.pi (fun k : Fin (Fintype.card C) => poissonMeasure (r * p k))).map E := by
          rw [hsplit']
    _ = Measure.pi (fun c : C => poissonMeasure (r * w c)) := hpi

/-! ## The two-sample label discrepancy -/

/-- **Two-sample label discrepancy bound.**  Two independent marked Poisson
clouds of common intensity `r`, whose mark laws have the same label marginal
`∑ c, w c • δ c`, have expected total label-count discrepancy at most
`sqrt (2 * r * card C)`. -/
theorem integral_markLabelDiscrepancy_le
    (q : ℕ) {C A B : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure (C × A)) [IsProbabilityMeasure α]
    (β : Measure (C × B)) [IsProbabilityMeasure β]
    (r : ℝ≥0) (w : C → ℝ≥0) (hwsum : ∑ c, w c = 1)
    (hlabel_α : α.map Prod.fst = Measure.sum (fun c => (w c : ℝ≥0∞) • Measure.dirac c))
    (hlabel_β : β.map Prod.fst = Measure.sum (fun c => (w c : ℝ≥0∞) • Measure.dirac c)) :
    ∫ z : MarkedCloudSpace q (C × A) × MarkedCloudSpace q (C × B),
        (∑ c : C,
          |((Finset.univ.filter (fun i : Fin z.1.1 => markLabel (i : ℕ) z.1 = c)).card : ℝ) -
           ((Finset.univ.filter (fun j : Fin z.2.1 => markLabel (j : ℕ) z.2 = c)).card : ℝ)|)
        ∂((markedPoissonLaw (q := q) (C × A) α r).prod
          (markedPoissonLaw (q := q) (C × B) β r)) ≤
      Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ)) := by
  classical
  let PA : Measure (MarkedCloudSpace q (C × A)) := markedPoissonLaw (q := q) (C × A) α r
  let PB : Measure (MarkedCloudSpace q (C × B)) := markedPoissonLaw (q := q) (C × B) β r
  let π : C → Measure ℕ := fun c => poissonMeasure (r * w c)
  let cntA : MarkedCloudSpace q (C × A) → C → ℕ := fun z c =>
    (Finset.univ.filter (fun i : Fin z.1 => markLabel (i : ℕ) z = c)).card
  let cntB : MarkedCloudSpace q (C × B) → C → ℕ := fun z c =>
    (Finset.univ.filter (fun j : Fin z.1 => markLabel (j : ℕ) z = c)).card
  let F : (C → ℕ) × (C → ℕ) → ℝ :=
    fun v => ∑ c, |((v.1 c : ℕ) : ℝ) - ((v.2 c : ℕ) : ℝ)|
  change ∫ z : MarkedCloudSpace q (C × A) × MarkedCloudSpace q (C × B),
      F (cntA z.1, cntB z.2) ∂(PA.prod PB) ≤
      Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ))
  have hPA : IsProbabilityMeasure PA := by
    change IsProbabilityMeasure (markedPoissonLaw (q := q) (C × A) α r)
    infer_instance
  have hPB : IsProbabilityMeasure PB := by
    change IsProbabilityMeasure (markedPoissonLaw (q := q) (C × B) β r)
    infer_instance
  have hmeasA : Measurable cntA := by
    change Measurable (markLabelCounts (q := q) (C := C) (A := A))
    exact measurable_markLabelCounts q
  have hmeasB : Measurable cntB := by
    change Measurable (markLabelCounts (q := q) (C := C) (A := B))
    exact measurable_markLabelCounts q
  have hlawA : PA.map cntA = Measure.pi π := by
    have h := map_markLabelCounts (q := q) (C := C) (A := A) α r w hwsum hlabel_α
    simpa only [PA, π, cntA] using h
  have hlawB : PB.map cntB = Measure.pi π := by
    have h := map_markLabelCounts (q := q) (C := C) (A := B) β r w hwsum hlabel_β
    simpa only [PB, π, cntB] using h
  have hpair : (PA.prod PB).map
      (fun z : MarkedCloudSpace q (C × A) × MarkedCloudSpace q (C × B) =>
        (cntA z.1, cntB z.2)) = (Measure.pi π).prod (Measure.pi π) := by
    rw [show (fun z : MarkedCloudSpace q (C × A) × MarkedCloudSpace q (C × B) =>
          (cntA z.1, cntB z.2)) = Prod.map cntA cntB from rfl,
      ← Measure.map_prod_map PA PB hmeasA hmeasB, hlawA, hlawB]
  have hIntegral : ∫ z : MarkedCloudSpace q (C × A) × MarkedCloudSpace q (C × B),
        F (cntA z.1, cntB z.2) ∂(PA.prod PB) =
      ∫ v : (C → ℕ) × (C → ℕ), F v ∂((Measure.pi π).prod (Measure.pi π)) := by
    have hφae : AEMeasurable (fun z : MarkedCloudSpace q (C × A) ×
        MarkedCloudSpace q (C × B) => (cntA z.1, cntB z.2)) (PA.prod PB) :=
      (hmeasA.prodMap hmeasB).aemeasurable
    have hF : AEStronglyMeasurable F
        (Measure.map (fun z : MarkedCloudSpace q (C × A) ×
          MarkedCloudSpace q (C × B) => (cntA z.1, cntB z.2)) (PA.prod PB)) := by
      rw [hpair]
      exact (measurable_of_countable F).aestronglyMeasurable
    have h := integral_map hφae hF
    rw [hpair] at h
    exact h.symm
  let e' := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ C
  have hmp : MeasurePreserving e' (Measure.pi (fun c : C => (π c).prod (π c)))
      ((Measure.pi π).prod (Measure.pi π)) :=
    measurePreserving_arrowProdEquivProdArrow ℕ ℕ C π π
  have hIntegral2 : ∫ v : (C → ℕ) × (C → ℕ), F v ∂((Measure.pi π).prod (Measure.pi π)) =
      ∫ x : C → ℕ × ℕ, (∑ c, |((x c).1 : ℝ) - ((x c).2 : ℝ)|)
        ∂(Measure.pi (fun c : C => (π c).prod (π c))) := by
    rw [← hmp.integral_comp e'.measurableEmbedding F]
    congr with x
  have hCS : (∑ c : C, Real.sqrt (2 * ((r * w c : ℝ≥0) : ℝ))) ≤
      Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ)) := by
    have hwR : (∑ c : C, (w c : ℝ)) = 1 := by
      rw [← NNReal.coe_sum, hwsum, NNReal.coe_one]
    have hCSq : (∑ c : C, Real.sqrt (w c : ℝ)) ≤
        Real.sqrt (Fintype.card C : ℝ) := by
      have h := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset C))
        (f := fun c : C => (w c : ℝ)) (g := fun _ => (1 : ℝ))
        (fun c => by positivity) (fun c => by positivity)
      simpa [hwR] using h
    have hstep1 : (∑ c : C, Real.sqrt (2 * ((r * w c : ℝ≥0) : ℝ))) =
        Real.sqrt (2 * (r : ℝ)) * ∑ c : C, Real.sqrt (w c : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      have hcast : ((r * w c : ℝ≥0) : ℝ) = (r : ℝ) * (w c : ℝ) := by
        push_cast
        ring
      rw [hcast,
        show 2 * ((r : ℝ) * (w c : ℝ)) = (2 * (r : ℝ)) * (w c : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
    rw [hstep1]
    calc Real.sqrt (2 * (r : ℝ)) * ∑ c : C, Real.sqrt (w c : ℝ)
        ≤ Real.sqrt (2 * (r : ℝ)) * Real.sqrt (Fintype.card C : ℝ) :=
          mul_le_mul_of_nonneg_left hCSq (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ)) := by
          rw [← Real.sqrt_mul (by positivity)]
  calc ∫ z : MarkedCloudSpace q (C × A) × MarkedCloudSpace q (C × B),
        F (cntA z.1, cntB z.2) ∂(PA.prod PB)
      = ∫ x : C → ℕ × ℕ, (∑ c, |((x c).1 : ℝ) - ((x c).2 : ℝ)|)
          ∂(Measure.pi (fun c : C => (π c).prod (π c))) := by
        rw [hIntegral, hIntegral2]
    _ ≤ ∑ c : C, Real.sqrt (2 * ((r * w c : ℝ≥0) : ℝ)) :=
        integral_sum_abs_sub_poissonPi_le (fun c : C => r * w c)
    _ ≤ Real.sqrt (2 * (r : ℝ) * (Fintype.card C : ℝ)) := hCS

end OTSelector.Probability
