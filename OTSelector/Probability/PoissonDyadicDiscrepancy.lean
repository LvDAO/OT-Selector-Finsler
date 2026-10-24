import OTSelector.Probability.PoissonCubePressure
import OTSelector.Probability.MultinomialSplitting
import OTSelector.Probability.PoissonCountDiscrepancy
import OTSelector.Finite.DyadicCellCost
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Fin

/-!
# Poisson dyadic cell discrepancies

For two independent Poissonized clouds of intensity `r` on the unit `q`-cube, this
file bounds the expected discrepancy of their level-`k` dyadic cell-count
histograms.  The main estimate is

`∫ cloudCellDiscrepancy q k ∂(twoCloudLaw q r) ≤ sqrt (2 r 2 ^ (k * q))`,

which is the histogram-discrepancy input of the hierarchical dyadic matching
bound, together with the cruder bound `2 r`.

The proof has three layers:

* the coordinatewise dyadic cell map pushes the uniform cube measure forward to
  the uniform measure on the finite cell type `Fin q → Fin (2 ^ k)`;
* the labels of the first `N` points of a Poisson cloud therefore have the
  Poisson splitting law of `MultinomialSplitting`, namely independent Poisson
  counts with rate `r / (2 ^ k) ^ q` in each cell;
* the two clouds are independent, so the cell-count discrepancy is the sum over
  cells of the absolute difference of two independent Poisson variables, and
  `integral_sum_abs_sub_poissonPi_le` gives the square-root bound.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

-- Local typeclass instances of the form `haveI` are needed for instance search.
set_option linter.style.haveILetI false

noncomputable section
namespace OTSelector.Probability

/-! ## Cell counts and discrepancy -/

/-- The vector of level-`k` dyadic cell counts of one Poisson cloud. -/
noncomputable def cloudCellCount (q k : ℕ) (z : PoissonCloudSpace q) :
    (Fin q → Fin (2 ^ k)) → ℕ :=
  fun c => (Finset.univ.filter (fun i : Fin z.1 =>
    dyadicCell q k (z.2 i) = c)).card

/-- The total absolute discrepancy of the level-`k` dyadic cell counts of two
Poisson clouds. -/
noncomputable def cloudCellDiscrepancy (q k : ℕ) (ω : TwoCloudSpace q) : ℝ :=
  ∑ c : Fin q → Fin (2 ^ k),
    |(cloudCellCount q k ω.1 c : ℝ) - (cloudCellCount q k ω.2 c : ℝ)|

/-! ## The coordinate cell label -/

/-- The level-`k` dyadic cell label of a single real coordinate. -/
private noncomputable def cellCoord (k : ℕ) (x : ℝ) : Fin (2 ^ k) :=
  ⟨⌊(2 : ℝ) ^ k * x⌋₊ % 2 ^ k,
    Nat.mod_lt _ (Nat.pow_pos (by norm_num : 0 < 2))⟩

private theorem cellCoord_eq_dyadicCell (q k : ℕ) :
    dyadicCell q k = fun x : Fin q → ℝ => fun i => cellCoord k (x i) := rfl

private theorem measurable_cellCoord (k : ℕ) : Measurable (cellCoord k) := by
  apply measurable_to_countable'
  intro c
  have hpre : cellCoord k ⁻¹' {c} = {x : ℝ | ⌊(2 : ℝ) ^ k * x⌋₊ % 2 ^ k = (c : ℕ)} := by
    ext x
    simp [cellCoord, Fin.ext_iff]
  rw [hpre]
  exact (measurableSet_singleton (c : ℕ)).preimage
    ((measurable_of_countable (fun n : ℕ => n % 2 ^ k)).comp
      (Nat.measurable_floor.comp (measurable_const.mul measurable_id)))

/-- The cell map on a single coordinate is measurable. -/
theorem measurable_dyadicCell (q k : ℕ) : Measurable (dyadicCell q k) := by
  rw [cellCoord_eq_dyadicCell]
  exact measurable_pi_lambda _ fun i =>
    (measurable_cellCoord k).comp (measurable_pi_apply i)

/-! ## The uniform law of cell labels -/

/-- The uniform measure on the interval `(0, 1)` evaluated on a measurable set. -/
private lemma uniformInterval_one_apply {S : Set ℝ} (hS : MeasurableSet S) :
    uniformInterval 1 S = volume (S ∩ Set.Ioo (0 : ℝ) 1) := by
  unfold uniformInterval
  rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, inv_one, one_smul,
    Measure.restrict_apply hS]

/-- The preimage of a singleton cell label has volume `(2 ^ k)⁻¹`. -/
private lemma volume_cellCoord_singleton (k : ℕ) (c : Fin (2 ^ k)) :
    volume ({x : ℝ | ⌊(2 : ℝ) ^ k * x⌋₊ % 2 ^ k = c} ∩ Set.Ioo (0 : ℝ) 1) =
      ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by
    rw [Nat.cast_pow]
    norm_num
  set a : ℝ := (c : ℝ) / (2 : ℝ) ^ k with ha
  set b : ℝ := ((c : ℝ) + 1) / (2 : ℝ) ^ k with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one hp, ← hpcast]
    have hc : (c : ℝ) + 1 ≤ ((2 ^ k : ℕ) : ℝ) := by
      have hlt : (c : ℕ) + 1 ≤ 2 ^ k := Nat.succ_le_of_lt c.isLt
      exact_mod_cast hlt
    exact hc
  have hset : {x : ℝ | ⌊(2 : ℝ) ^ k * x⌋₊ % 2 ^ k = c} ∩ Set.Ioo (0 : ℝ) 1 =
      Set.Ico a b ∩ Set.Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo] at hx
      obtain ⟨hmod, hx0, hx1⟩ := hx
      have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ k * x := by positivity
      have hrp : (2 : ℝ) ^ k * x < ((2 ^ k : ℕ) : ℝ) := by
        rw [hpcast]
        simpa using mul_lt_mul_of_pos_left hx1 hp
      have hflt : ⌊(2 : ℝ) ^ k * x⌋₊ < 2 ^ k := (Nat.floor_lt hr0).mpr hrp
      have hfloor : ⌊(2 : ℝ) ^ k * x⌋₊ = (c : ℕ) := by
        rw [Nat.mod_eq_of_lt hflt] at hmod
        exact hmod
      have hbounds := (Nat.floor_eq_iff hr0).mp hfloor
      rw [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioo]
      refine ⟨⟨?_, ?_⟩, hx0, hx1⟩
      · rw [ha, div_le_iff₀ hp]
        simpa [mul_comm] using hbounds.1
      · rw [hb, lt_div_iff₀ hp]
        simpa [mul_comm] using hbounds.2
    · intro hx
      rw [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioo] at hx
      obtain ⟨⟨hax, hxb⟩, hx0, hx1⟩ := hx
      have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ k * x := by positivity
      have hc_le : (c : ℝ) ≤ (2 : ℝ) ^ k * x := by
        have h := (div_le_iff₀ hp).mp hax
        simpa [mul_comm] using h
      have hx_lt : (2 : ℝ) ^ k * x < (c : ℝ) + 1 := by
        have h := (lt_div_iff₀ hp).mp hxb
        simpa [mul_comm] using h
      have hfloor : ⌊(2 : ℝ) ^ k * x⌋₊ = (c : ℕ) :=
        (Nat.floor_eq_iff hr0).mpr ⟨hc_le, hx_lt⟩
      have hflt : ⌊(2 : ℝ) ^ k * x⌋₊ < 2 ^ k := by
        rw [hfloor]
        exact c.isLt
      rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo]
      exact ⟨by rw [Nat.mod_eq_of_lt hflt, hfloor], hx0, hx1⟩
  have hsub : Set.Ico a b ∩ Set.Ioo (0 : ℝ) 1 = Set.Ico a b \ {0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioo, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hax, hxb⟩, hx0, _⟩
      exact ⟨⟨hax, hxb⟩, ne_of_gt hx0⟩
    · rintro ⟨⟨hax, hxb⟩, hxne⟩
      exact ⟨⟨hax, hxb⟩, lt_of_le_of_ne (ha0.trans hax) (Ne.symm hxne),
        hxb.trans_le hb1⟩
  rw [hset, hsub, measure_sdiff_null (by simp : volume ({0} : Set ℝ) = 0),
    Real.volume_Ico]
  have hba : b - a = ((2 : ℝ) ^ k)⁻¹ := by
    rw [ha, hb]
    field_simp
    ring
  rw [hba, ENNReal.ofReal_inv_of_pos hp]
  congr 1
  rw [← ENNReal.ofReal_natCast (2 ^ k), Nat.cast_pow]
  norm_num

/-- The coordinate cell label of a uniform point on `(0, 1)` is uniform on
`Fin (2 ^ k)`. -/
private lemma map_cellCoord_uniformMeasure (k : ℕ) :
    Measure.map (cellCoord k) (uniformInterval 1) = uniformMeasure (Fin (2 ^ k)) := by
  refine Measure.ext_of_singleton (fun c => ?_)
  have hpre : cellCoord k ⁻¹' {c} = {x : ℝ | ⌊(2 : ℝ) ^ k * x⌋₊ % 2 ^ k = c} := by
    ext x
    simp [cellCoord, Fin.ext_iff]
  have hS : MeasurableSet {x : ℝ | ⌊(2 : ℝ) ^ k * x⌋₊ % 2 ^ k = c} :=
    (measurableSet_singleton (c : ℕ)).preimage <|
      (measurable_of_countable (fun n : ℕ => n % 2 ^ k)).comp
        (Nat.measurable_floor.comp (measurable_const.mul measurable_id))
  rw [Measure.map_apply (measurable_cellCoord k) (measurableSet_singleton c),
    hpre, uniformInterval_one_apply hS, volume_cellCoord_singleton k c,
    uniformMeasure_singleton, Fintype.card_fin]

/-- The uniform measure on a product of finite types is the product of the
uniform measures. -/
private lemma pi_uniformMeasure (q K : ℕ) [NeZero K] :
    Measure.pi (fun _ : Fin q => uniformMeasure (Fin K)) =
      uniformMeasure (Fin q → Fin K) := by
  haveI : Nonempty (Fin K) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne K)⟩⟩
  haveI : IsProbabilityMeasure (uniformMeasure (Fin K)) :=
    uniformMeasure_isProbabilityMeasure
  refine Measure.ext_of_singleton (fun f => ?_)
  rw [Measure.pi_singleton]
  simp only [uniformMeasure_singleton, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fun]
  rw [← ENNReal.inv_pow]
  congr 1
  simp [Nat.cast_pow]

/-- The dyadic cell map pushes the uniform cube measure forward to the uniform
measure on the finite cell type. -/
theorem map_dyadicCell_uniform (q k : ℕ) :
    Measure.map (dyadicCell q k) (cubeMeasure (Fin q) 1) =
      uniformMeasure (Fin q → Fin (2 ^ k)) := by
  have hsig : ∀ _ : Fin q, SigmaFinite
      ((uniformInterval 1).map (cellCoord k)) := fun _ => by
    rw [map_cellCoord_uniformMeasure k]
    infer_instance
  rw [cellCoord_eq_dyadicCell, cubeMeasure]
  rw [Measure.pi_map_pi (μ := fun _ : Fin q => uniformInterval 1)
    (f := fun _ => cellCoord k) (hμ := hsig)
    (fun _ => (measurable_cellCoord k).aemeasurable)]
  simp only [map_cellCoord_uniformMeasure k]
  exact pi_uniformMeasure q (2 ^ k)

/-! ## The count law at one dyadic level -/

/-- Pushing the uniform measure on a finite type forward along an equivalence gives
the uniform measure on the target. -/
private lemma map_uniformMeasure_equiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Fintype α] [Fintype β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformMeasure α).map e = uniformMeasure β := by
  have he : Measurable e := measurable_of_countable e
  refine Measure.ext_of_singleton (fun b => ?_)
  rw [Measure.map_apply he (measurableSet_singleton b),
    show e ⁻¹' {b} = {e.symm b} by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact (Equiv.symm_apply_apply e x).symm.trans (congrArg e.symm hx)
      · intro hx
        rw [hx, Equiv.apply_symm_apply],
    uniformMeasure_singleton, uniformMeasure_singleton, Fintype.card_congr e]

/-- The cell-count vector of a Poisson cloud is measurable. -/
theorem measurable_cloudCellCount (q k : ℕ) :
    Measurable (fun z : PoissonCloudSpace q =>
      fun c : Fin q → Fin (2 ^ k) => cloudCellCount q k z c) := by
  classical
  apply measurable_pi_iff.mpr
  intro c
  apply measurable_to_countable'
  intro m
  have hset : {z : PoissonCloudSpace q | cloudCellCount q k z c = m} =
      ⋃ n : ℕ, ({z : PoissonCloudSpace q | z.1 = n} ∩
        {z : PoissonCloudSpace q | (Finset.univ.filter (fun i : Fin n =>
          dyadicCell q k (z.2 i) = c)).card = m}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, cloudCellCount]
    constructor
    · intro hz
      exact ⟨z.1, rfl, hz⟩
    · rintro ⟨n, hn, hz⟩
      subst hn
      exact hz
  change MeasurableSet {z : PoissonCloudSpace q | cloudCellCount q k z c = m}
  rw [hset]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact measurable_fst (measurableSet_singleton n)
  · have hm : Measurable (fun z : PoissonCloudSpace q => fun i : Fin n =>
        dyadicCell q k (z.2 i)) :=
      measurable_pi_lambda _ fun i =>
        (measurable_dyadicCell q k).comp
          (show Measurable (fun z : PoissonCloudSpace q => z.2 (i : ℕ)) from
            (measurable_pi_apply (i : ℕ)).comp measurable_snd)
    have htarget : MeasurableSet {ω : Fin n → (Fin q → Fin (2 ^ k)) |
        (Finset.univ.filter (fun i : Fin n => ω i = c)).card = m} :=
      (measurable_of_countable (fun ω : Fin n → (Fin q → Fin (2 ^ k)) =>
        (Finset.univ.filter (fun i : Fin n => ω i = c)).card))
        (measurableSet_singleton m)
    exact hm htarget

/-- The cell counts sum to the cloud size. -/
private lemma sum_cloudCellCount (q k : ℕ) (z : PoissonCloudSpace q) :
    ∑ c : Fin q → Fin (2 ^ k), cloudCellCount q k z c = z.1 := by
  classical
  simpa [cloudCellCount] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin z.1)))
      (t := (Finset.univ : Finset (Fin q → Fin (2 ^ k))))
      (f := fun i : Fin z.1 => dyadicCell q k (z.2 i))
      (fun _ _ => Finset.mem_univ _)).symm

/-- The joint law of the first `n` cell labels of a Poisson cloud is the product
of the uniform laws. -/
private lemma map_cellLabel_prefix (q k n K : ℕ)
    (F : (Fin q → Fin (2 ^ k)) ≃ Fin K) (r : ℝ≥0) :
    (poissonCubeLaw q r).map
        (fun z : PoissonCloudSpace q =>
          fun i : Fin n => F (dyadicCell q k (z.2 i))) =
      Measure.pi (fun _ : Fin n => uniformMeasure (Fin K)) := by
  classical
  have hF : Measurable F := measurable_of_countable F
  have hcell (i : Fin n) : Measurable
      (fun x : ℕ → (Fin q → ℝ) => F (dyadicCell q k (x (i : ℕ)))) :=
    hF.comp ((measurable_dyadicCell q k).comp (measurable_pi_apply (i : ℕ)))
  have hg : Measurable (fun x : ℕ → (Fin q → ℝ) =>
      fun i : Fin n => F (dyadicCell q k (x i))) :=
    measurable_pi_lambda _ hcell
  have hstep1 : (poissonCubeLaw q r).map
      (fun z : PoissonCloudSpace q =>
        fun i : Fin n => F (dyadicCell q k (z.2 i))) =
      (cubeSeqLaw q).map (fun x : ℕ → (Fin q → ℝ) =>
        fun i : Fin n => F (dyadicCell q k (x i))) := by
    rw [show (fun z : PoissonCloudSpace q =>
        fun i : Fin n => F (dyadicCell q k (z.2 i))) =
        (fun x : ℕ → (Fin q → ℝ) =>
          fun i : Fin n => F (dyadicCell q k (x i))) ∘ Prod.snd from rfl]
    rw [← Measure.map_map hg measurable_snd]
    unfold poissonCubeLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  rw [hstep1]
  have hind : iIndepFun (fun i : Fin n => fun x : ℕ → (Fin q → ℝ) =>
      F (dyadicCell q k (x i))) (cubeSeqLaw q) := by
    let hprob : ∀ _ : ℕ, IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
      fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)
    have hNat : iIndepFun (fun i : ℕ => fun x : ℕ → (Fin q → ℝ) => x i)
        (cubeSeqLaw q) := by
      unfold cubeSeqLaw
      exact @iIndepFun_infinitePi ℕ (fun _ => Fin q → ℝ) (fun _ => inferInstance)
        (fun _ => Fin q → ℝ) (fun _ => inferInstance)
        (fun _ => cubeMeasure (Fin q) 1) hprob
        (fun (_ : ℕ) (x : Fin q → ℝ) => x) (by fun_prop)
    have hfin : iIndepFun (fun i : Fin n => fun x : ℕ → (Fin q → ℝ) => x i)
        (cubeSeqLaw q) :=
      hNat.precomp (g := fun i : Fin n => (i : ℕ)) (fun a b h => Fin.ext h)
    exact hfin.comp (fun _ x => F (dyadicCell q k x))
      (fun _ => hF.comp (measurable_dyadicCell q k))
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hcell i).aemeasurable) hind]
  congr 1
  funext i
  have hmpi := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => cubeMeasure (Fin q) 1)
    (hμ := fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)) (i : ℕ)
  have hmarg : (cubeSeqLaw q).map (fun x : ℕ → (Fin q → ℝ) =>
      F (dyadicCell q k (x i))) = uniformMeasure (Fin K) := by
    have h1 : (fun x : ℕ → (Fin q → ℝ) => F (dyadicCell q k (x (i : ℕ)))) =
        F ∘ ((dyadicCell q k) ∘ Function.eval (i : ℕ)) := rfl
    rw [h1, ← Measure.map_map hF ((measurable_dyadicCell q k).comp hmpi.measurable),
      ← Measure.map_map (measurable_dyadicCell q k) hmpi.measurable]
    unfold cubeSeqLaw
    rw [hmpi.map_eq, map_dyadicCell_uniform]
    exact map_uniformMeasure_equiv F
  exact hmarg

/-- **The count law at one dyadic level.**  Under the Poissonized cloud law, the
vector of level-`k` dyadic cell counts is a product of independent Poisson laws
with rate `r / (2 ^ k) ^ q` in every cell. -/
theorem map_cloudCellCount (q k : ℕ) (r : ℝ≥0) :
    (poissonCubeLaw q r).map (fun z => fun c => cloudCellCount q k z c) =
      Measure.pi (fun _ : Fin q → Fin (2 ^ k) =>
        poissonMeasure (r / (((2 ^ k) ^ q : ℕ) : ℝ≥0))) := by
  classical
  let K : ℕ := (2 ^ k) ^ q
  have hKpos : 0 < K := pow_pos (pow_pos (by norm_num : 0 < 2) k) q
  haveI : NeZero K := ⟨Nat.ne_of_gt hKpos⟩
  let F : (Fin q → Fin (2 ^ k)) ≃ Fin K := finFunctionFinEquiv
  let C : PoissonCloudSpace q → (Fin q → Fin (2 ^ k)) → ℕ :=
    fun z c => cloudCellCount q k z c
  let h : ((Fin q → Fin (2 ^ k)) → ℕ) → (Fin K → ℕ) :=
    fun g b => g (F.symm b)
  let w : ℕ → PoissonCloudSpace q → Fin K :=
    fun i z => F (dyadicCell q k (z.2 i))
  have hC_meas : Measurable C := measurable_cloudCellCount q k
  have hF : Measurable F := measurable_of_countable F
  have hw_meas (i : ℕ) : Measurable (w i) :=
    hF.comp ((measurable_dyadicCell q k).comp
      (show Measurable (fun z : PoissonCloudSpace q => z.2 i) from
        (measurable_pi_apply i).comp measurable_snd))
  have hN : (poissonCubeLaw q r).map (fun z : PoissonCloudSpace q => z.1) =
      poissonMeasure r := by
    unfold poissonCubeLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hlaw : ∀ i, (poissonCubeLaw q r).map (w i) = uniformMeasure (Fin K) := by
    intro i
    have hmpi := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => cubeMeasure (Fin q) 1)
      (hμ := fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)) i
    have hmarg : (cubeSeqLaw q).map (fun x : ℕ → (Fin q → ℝ) =>
        F (dyadicCell q k (x i))) = uniformMeasure (Fin K) := by
      have h1 : (fun x : ℕ → (Fin q → ℝ) => F (dyadicCell q k (x i))) =
          F ∘ ((dyadicCell q k) ∘ Function.eval i) := rfl
      rw [h1, ← Measure.map_map hF ((measurable_dyadicCell q k).comp hmpi.measurable),
        ← Measure.map_map (measurable_dyadicCell q k) hmpi.measurable]
      unfold cubeSeqLaw
      rw [hmpi.map_eq, map_dyadicCell_uniform]
      exact map_uniformMeasure_equiv F
    have hg : Measurable (fun x : ℕ → (Fin q → ℝ) =>
        F (dyadicCell q k (x i))) :=
      hF.comp ((measurable_dyadicCell q k).comp (measurable_pi_apply i))
    have hpull : (poissonCubeLaw q r).map (fun z => F (dyadicCell q k (z.2 i))) =
        (cubeSeqLaw q).map (fun x => F (dyadicCell q k (x i))) := by
      rw [show (fun z : PoissonCloudSpace q => F (dyadicCell q k (z.2 i))) =
          (fun x : ℕ → (Fin q → ℝ) => F (dyadicCell q k (x i))) ∘ Prod.snd from rfl,
        ← Measure.map_map hg measurable_snd]
      unfold poissonCubeLaw
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hpull.trans hmarg
  have hw : ∀ n, iIndepFun (fun i : Fin n => w i) (poissonCubeLaw q r) := by
    intro n
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (hw_meas (i : ℕ)).aemeasurable)]
    rw [show (fun z : PoissonCloudSpace q => fun i : Fin n => w i z) =
        fun z => fun i : Fin n => F (dyadicCell q k (z.2 i)) from rfl]
    rw [map_cellLabel_prefix q k n K F r]
    congr 1
    funext i
    exact (hlaw (i : ℕ)).symm
  have hindep : ∀ n, IndepFun (fun z : PoissonCloudSpace q => z.1)
      (fun z => fun i : Fin n => w i z) (poissonCubeLaw q r) := by
    intro n
    have hY : Measurable (fun x : ℕ → (Fin q → ℝ) =>
        fun i : Fin n => F (dyadicCell q k (x i))) :=
      measurable_pi_lambda _ fun i =>
        hF.comp ((measurable_dyadicCell q k).comp (measurable_pi_apply (i : ℕ)))
    have h := indepFun_prod (μ := poissonMeasure r) (ν := cubeSeqLaw q)
      (X := fun n : ℕ => n)
      (Y := fun x : ℕ → (Fin q → ℝ) => fun i : Fin n => F (dyadicCell q k (x i)))
      measurable_id hY
    unfold poissonCubeLaw
    exact h
  have hmain := map_poisson_label_counts (Λ := r)
    (N := fun z : PoissonCloudSpace q => z.1) (w := w) hN hw hlaw hindep
  have hmain' : (poissonCubeLaw q r).map
      (fun z : PoissonCloudSpace q => fun b : Fin K =>
        (Finset.univ.filter (fun i : Fin z.1 => w i z = b)).card) =
      Measure.pi (fun _ : Fin K => poissonMeasure (r / (K : ℝ≥0))) := by
    simpa [K, Fintype.card_fin] using hmain
  have hcomp : h ∘ C = fun z : PoissonCloudSpace q => fun b : Fin K =>
      (Finset.univ.filter (fun i : Fin z.1 => w i z = b)).card := by
    funext z b
    simp only [Function.comp_apply, h, C, w, cloudCellCount]
    congr 1
    apply Finset.filter_congr
    intro i _
    exact F.eq_symm_apply
  let kmape : (Fin K → ℕ) ≃ᵐ ((Fin q → Fin (2 ^ k)) → ℕ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin q → Fin (2 ^ k) => ℕ) F.symm
  have hh : h = ⇑kmape.symm := rfl
  have hk_map : (Measure.pi (fun _ : Fin K => poissonMeasure (r / (K : ℝ≥0)))).map kmape =
      Measure.pi (fun _ : Fin q → Fin (2 ^ k) =>
        poissonMeasure (r / (K : ℝ≥0))) := by
    have h := Measure.pi_map_piCongrLeft (e := F.symm)
      (μ := fun _ : Fin q → Fin (2 ^ k) => poissonMeasure (r / (K : ℝ≥0)))
    simpa using h
  have hh_meas : Measurable h := measurable_of_countable h
  have hmap_comp : (poissonCubeLaw q r).map C =
      ((poissonCubeLaw q r).map (h ∘ C)).map kmape := by
    rw [Measure.map_map (μ := poissonCubeLaw q r) kmape.measurable
      (hh_meas.comp hC_meas)]
    congr 1
    funext z c
    simp only [Function.comp_apply]
    rw [show h (C z) = kmape.symm (C z) from congrFun hh (C z), kmape.apply_symm_apply]
  calc
    (poissonCubeLaw q r).map C
        = ((poissonCubeLaw q r).map (h ∘ C)).map kmape := hmap_comp
    _ = (Measure.pi (fun _ : Fin K => poissonMeasure (r / (K : ℝ≥0)))).map kmape := by
          rw [hcomp, hmain']
    _ = Measure.pi (fun _ : Fin q → Fin (2 ^ k) =>
          poissonMeasure (r / (K : ℝ≥0))) := hk_map

/-! ## The two-cloud discrepancy integrals -/

/-- The joint law of the two cell-count vectors is a product of independent
Poisson laws on the cell type. -/
theorem map_cloudCellCount_pair (q k : ℕ) (r : ℝ≥0) :
    (twoCloudLaw q r).map (fun ω : TwoCloudSpace q =>
      fun c : Fin q → Fin (2 ^ k) =>
        (cloudCellCount q k ω.1 c, cloudCellCount q k ω.2 c)) =
      Measure.pi (fun _ : Fin q → Fin (2 ^ k) =>
        (poissonMeasure (r / (((2 ^ k) ^ q : ℕ) : ℝ≥0))).prod
          (poissonMeasure (r / (((2 ^ k) ^ q : ℕ) : ℝ≥0)))) := by
  classical
  let Cell := Fin q → Fin (2 ^ k)
  let μ : Measure ℕ := poissonMeasure (r / (((2 ^ k) ^ q : ℕ) : ℝ≥0))
  let C : PoissonCloudSpace q → Cell → ℕ := fun z c => cloudCellCount q k z c
  have hC : Measurable C := measurable_cloudCellCount q k
  have hC_fst : Measurable (fun ω : TwoCloudSpace q => C ω.1) :=
    hC.comp measurable_fst
  have hC_snd : Measurable (fun ω : TwoCloudSpace q => C ω.2) :=
    hC.comp measurable_snd
  have hpair_meas : Measurable (fun ω : TwoCloudSpace q => (C ω.1, C ω.2)) :=
    hC_fst.prodMk hC_snd
  have hpair : (twoCloudLaw q r).map
      (fun ω : TwoCloudSpace q => (C ω.1, C ω.2)) =
      (Measure.pi (fun _ : Cell => μ)).prod (Measure.pi (fun _ : Cell => μ)) := by
    have h := Measure.map_prod_map (poissonCubeLaw q r) (poissonCubeLaw q r) hC hC
    rw [map_cloudCellCount q k r] at h
    exact h.symm
  let e : (Cell → ℕ × ℕ) ≃ᵐ ((Cell → ℕ) × (Cell → ℕ)) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ Cell
  have he : MeasurePreserving e (Measure.pi (fun _ : Cell => μ.prod μ))
      ((Measure.pi (fun _ : Cell => μ)).prod (Measure.pi (fun _ : Cell => μ))) :=
    measurePreserving_arrowProdEquivProdArrow ℕ ℕ Cell (fun _ => μ) (fun _ => μ)
  have hcomp : (fun ω : TwoCloudSpace q => fun c : Cell =>
        (C ω.1 c, C ω.2 c)) =
      e.symm ∘ (fun ω : TwoCloudSpace q => (C ω.1, C ω.2)) := rfl
  calc
    (twoCloudLaw q r).map (fun ω : TwoCloudSpace q => fun c : Cell =>
        (C ω.1 c, C ω.2 c))
        = (twoCloudLaw q r).map
            (e.symm ∘ (fun ω : TwoCloudSpace q => (C ω.1, C ω.2))) := by rw [hcomp]
    _ = ((twoCloudLaw q r).map (fun ω => (C ω.1, C ω.2))).map e.symm :=
          (Measure.map_map (μ := twoCloudLaw q r) e.symm.measurable
            hpair_meas).symm
    _ = ((Measure.pi (fun _ : Cell => μ)).prod
          (Measure.pi (fun _ : Cell => μ))).map e.symm := by rw [hpair]
    _ = Measure.pi (fun _ : Cell => μ.prod μ) := he.symm.map_eq

/-- The cell counts of one cloud are nonnegative, so the discrepancy is. -/
theorem cloudCellDiscrepancy_nonneg (q k : ℕ) (ω : TwoCloudSpace q) :
    0 ≤ cloudCellDiscrepancy q k ω :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The discrepancy is bounded by the sum of the two cloud sizes. -/
theorem cloudCellDiscrepancy_le_counts (q k : ℕ) (ω : TwoCloudSpace q) :
    cloudCellDiscrepancy q k ω ≤
      ((sourceCount ω : ℕ) : ℝ) + ((targetCount ω : ℕ) : ℝ) := by
  classical
  unfold cloudCellDiscrepancy sourceCount targetCount
  calc
    ∑ c : Fin q → Fin (2 ^ k),
        |(cloudCellCount q k ω.1 c : ℝ) - (cloudCellCount q k ω.2 c : ℝ)|
        ≤ ∑ c : Fin q → Fin (2 ^ k),
            ((cloudCellCount q k ω.1 c : ℝ) + (cloudCellCount q k ω.2 c : ℝ)) := by
          apply Finset.sum_le_sum
          intro c _
          have ha : (0 : ℝ) ≤ (cloudCellCount q k ω.1 c : ℝ) := Nat.cast_nonneg _
          have hb : (0 : ℝ) ≤ (cloudCellCount q k ω.2 c : ℝ) := Nat.cast_nonneg _
          rw [abs_le]
          constructor <;> linarith
    _ = (∑ c : Fin q → Fin (2 ^ k), (cloudCellCount q k ω.1 c : ℝ)) +
          ∑ c : Fin q → Fin (2 ^ k), (cloudCellCount q k ω.2 c : ℝ) :=
          Finset.sum_add_distrib
    _ = ((ω.1.1 : ℕ) : ℝ) + ((ω.2.1 : ℕ) : ℝ) := by
          rw [← Nat.cast_sum, ← Nat.cast_sum, sum_cloudCellCount, sum_cloudCellCount]

/-- The first coordinate of a Poisson cloud has integral `r`. -/
private lemma integral_cloudCount_first (q : ℕ) (r : ℝ≥0) :
    ∫ x : PoissonCloudSpace q, ((x.1 : ℕ) : ℝ) ∂(poissonCubeLaw q r) = (r : ℝ) := by
  have h2 : (fun x : PoissonCloudSpace q => ((x.1 : ℕ) : ℝ)) =
      fun z => (fun n : ℕ => (n : ℝ)) z.1 * (fun _ => (1 : ℝ)) z.2 := by
    funext x
    simp
  rw [h2, poissonCubeLaw,
    integral_prod_mul (μ := poissonMeasure r) (ν := cubeSeqLaw q)
      (f := fun n : ℕ => (n : ℝ)) (g := fun _ => (1 : ℝ)),
    integral_id_poissonMeasure]
  simp

/-- The source count has integral `r`. -/
private lemma integral_sourceCount_twoCloudLaw (q : ℕ) (r : ℝ≥0) :
    ∫ ω : TwoCloudSpace q, ((sourceCount ω : ℕ) : ℝ) ∂(twoCloudLaw q r) = (r : ℝ) := by
  have h1 : (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ)) =
      fun z => (fun x : PoissonCloudSpace q => ((x.1 : ℕ) : ℝ)) z.1 *
        (fun _ => (1 : ℝ)) z.2 := by
    funext ω
    simp [sourceCount]
  rw [h1, twoCloudLaw,
    integral_prod_mul (μ := poissonCubeLaw q r) (ν := poissonCubeLaw q r)
      (f := fun x : PoissonCloudSpace q => ((x.1 : ℕ) : ℝ))
      (g := fun _ => (1 : ℝ)),
    integral_cloudCount_first q r]
  simp

/-- The target count has integral `r`. -/
private lemma integral_targetCount_twoCloudLaw (q : ℕ) (r : ℝ≥0) :
    ∫ ω : TwoCloudSpace q, ((targetCount ω : ℕ) : ℝ) ∂(twoCloudLaw q r) = (r : ℝ) := by
  have h1 : (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ)) =
      fun z => (fun _ => (1 : ℝ)) z.1 *
        (fun x : PoissonCloudSpace q => ((x.1 : ℕ) : ℝ)) z.2 := by
    funext ω
    simp [targetCount]
  rw [h1, twoCloudLaw,
    integral_prod_mul (μ := poissonCubeLaw q r) (ν := poissonCubeLaw q r)
      (f := fun _ : PoissonCloudSpace q => (1 : ℝ))
      (g := fun x : PoissonCloudSpace q => ((x.1 : ℕ) : ℝ)),
    integral_cloudCount_first q r]
  simp

/-- The target count is integrable. -/
private lemma integrable_targetCount_twoCloudLaw (q : ℕ) (r : ℝ≥0) :
    Integrable (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := by
  have h1 : Integrable (fun z : PoissonCloudSpace q => ((z.1 : ℕ) : ℝ))
      (poissonCubeLaw q r) := by
    unfold poissonCubeLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  unfold twoCloudLaw targetCount
  exact h1.comp_snd (poissonCubeLaw q r)

/-- The sum of square roots of the cell rates telescopes to the square root of
`2 r` times the number of cells. -/
private lemma sum_sqrt_cellRate (q k : ℕ) (r : ℝ≥0) :
    (∑ _ : Fin q → Fin (2 ^ k),
      Real.sqrt (2 * ((r / ((2 ^ k) ^ q : ℝ≥0) : ℝ≥0) : ℝ))) =
      Real.sqrt (2 * (r : ℝ) * (2 : ℝ) ^ (k * q)) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  set C : ℝ := (((2 ^ k) ^ q : ℕ) : ℝ) with hC
  have hCpos : 0 < C := by
    rw [hC]
    exact_mod_cast pow_pos (pow_pos (by norm_num : 0 < 2) k) q
  have hcoe : ((r / ((2 ^ k) ^ q : ℝ≥0) : ℝ≥0) : ℝ) = (r : ℝ) / C := by
    rw [hC]
    simp
  rw [hcoe]
  have hroot : C * Real.sqrt (2 * ((r : ℝ) / C)) =
      Real.sqrt (2 * (r : ℝ) * C) := by
    calc
      C * Real.sqrt (2 * ((r : ℝ) / C))
          = Real.sqrt (C ^ 2) * Real.sqrt (2 * ((r : ℝ) / C)) := by
              rw [Real.sqrt_sq hCpos.le]
      _ = Real.sqrt (C ^ 2 * (2 * ((r : ℝ) / C))) :=
            (Real.sqrt_mul (sq_nonneg C) (2 * ((r : ℝ) / C))).symm
      _ = Real.sqrt (2 * (r : ℝ) * C) := by
            congr 1
            field_simp
  rw [hroot]
  congr 1
  rw [hC, Nat.cast_pow, Nat.cast_pow, ← pow_mul]
  norm_num

/-- The expected dyadic cell-count discrepancy is at most the square root of
`2 r` times the number of cells. -/
theorem integral_cloudCellDiscrepancy_le (q k : ℕ) (r : ℝ≥0) :
    ∫ ω, cloudCellDiscrepancy q k ω ∂(twoCloudLaw q r)
      ≤ Real.sqrt (2 * (r : ℝ) * ((2 : ℝ) ^ (k * q))) := by
  classical
  let Cell := Fin q → Fin (2 ^ k)
  let μ : Measure ℕ := poissonMeasure (r / (((2 ^ k) ^ q : ℕ) : ℝ≥0))
  let F : (Cell → ℕ × ℕ) → ℝ :=
    fun z => ∑ c, |((z c).1 : ℝ) - ((z c).2 : ℝ)|
  have hF : Measurable F := by
    apply Finset.measurable_sum
    intro c _
    have h1 : Measurable (fun z : Cell → ℕ × ℕ => ((z c).1 : ℝ)) :=
      (measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
        (measurable_fst.comp (measurable_pi_apply c))
    have h2 : Measurable (fun z : Cell → ℕ × ℕ => ((z c).2 : ℝ)) :=
      (measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
        (measurable_snd.comp (measurable_pi_apply c))
    exact continuous_abs.measurable.comp (Measurable.sub h1 h2)
  have hpair_meas : Measurable (fun ω : TwoCloudSpace q =>
      fun c : Cell => (cloudCellCount q k ω.1 c, cloudCellCount q k ω.2 c)) := by
    apply measurable_pi_iff.mpr
    intro c
    exact (show Measurable (fun ω : TwoCloudSpace q =>
        cloudCellCount q k ω.1 c) from
        Measurable.comp (measurable_pi_apply c)
          ((measurable_cloudCellCount q k).comp measurable_fst)).prodMk
      (show Measurable (fun ω : TwoCloudSpace q =>
        cloudCellCount q k ω.2 c) from
        Measurable.comp (measurable_pi_apply c)
          ((measurable_cloudCellCount q k).comp measurable_snd))
  have hpt : (fun ω : TwoCloudSpace q => cloudCellDiscrepancy q k ω) =
      fun ω => F (fun c : Cell =>
        (cloudCellCount q k ω.1 c, cloudCellCount q k ω.2 c)) := rfl
  calc
    ∫ ω, cloudCellDiscrepancy q k ω ∂(twoCloudLaw q r)
        = ∫ z, F z ∂((twoCloudLaw q r).map
            (fun ω : TwoCloudSpace q => fun c : Cell =>
              (cloudCellCount q k ω.1 c, cloudCellCount q k ω.2 c))) := by
          rw [hpt]
          exact (integral_map hpair_meas.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ z, F z ∂(Measure.pi (fun _ : Cell => μ.prod μ)) := by
          rw [map_cloudCellCount_pair]
    _ ≤ ∑ _ : Cell, Real.sqrt (2 * ((r / ((2 ^ k) ^ q : ℝ≥0) : ℝ≥0) : ℝ)) := by
          simpa [F, μ, Nat.cast_pow] using
            integral_sum_abs_sub_poissonPi_le (fun _ : Cell =>
              r / ((2 ^ k) ^ q : ℝ≥0))
    _ = Real.sqrt (2 * (r : ℝ) * (2 : ℝ) ^ (k * q)) :=
          sum_sqrt_cellRate q k r

/-- The trivial bound: the expected dyadic cell-count discrepancy is at most the
sum of the two expected cloud sizes. -/
theorem integral_cloudCellDiscrepancy_le_trivial (q k : ℕ) (r : ℝ≥0) :
    ∫ ω, cloudCellDiscrepancy q k ω ∂(twoCloudLaw q r) ≤ 2 * (r : ℝ) := by
  have hsrc : Integrable (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := by
    simpa only using integrable_sourceCount q r
  have htgt : Integrable (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_targetCount_twoCloudLaw q r
  have hsum : Integrable (fun ω : TwoCloudSpace q =>
      ((sourceCount ω : ℕ) : ℝ) + ((targetCount ω : ℕ) : ℝ)) (twoCloudLaw q r) :=
    hsrc.add htgt
  calc
    ∫ ω, cloudCellDiscrepancy q k ω ∂(twoCloudLaw q r)
        ≤ ∫ ω, (((sourceCount ω : ℕ) : ℝ) + ((targetCount ω : ℕ) : ℝ))
            ∂(twoCloudLaw q r) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
            cloudCellDiscrepancy_nonneg q k ω) hsum
            (Filter.Eventually.of_forall fun ω => cloudCellDiscrepancy_le_counts q k ω)
    _ = (r : ℝ) + (r : ℝ) := by
          rw [integral_add hsrc htgt, integral_sourceCount_twoCloudLaw,
            integral_targetCount_twoCloudLaw]
    _ = 2 * (r : ℝ) := by ring

/-- The cell-count discrepancy is measurable in the two clouds. -/
theorem measurable_cloudCellDiscrepancy (q k : ℕ) :
    Measurable (cloudCellDiscrepancy q k) := by
  classical
  let Cell := Fin q → Fin (2 ^ k)
  let F : (Cell → ℕ × ℕ) → ℝ :=
    fun z => ∑ c, |((z c).1 : ℝ) - ((z c).2 : ℝ)|
  have hF : Measurable F := by
    apply Finset.measurable_sum
    intro c _
    have h1 : Measurable (fun z : Cell → ℕ × ℕ => ((z c).1 : ℝ)) :=
      (measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
        (measurable_fst.comp (measurable_pi_apply c))
    have h2 : Measurable (fun z : Cell → ℕ × ℕ => ((z c).2 : ℝ)) :=
      (measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
        (measurable_snd.comp (measurable_pi_apply c))
    exact continuous_abs.measurable.comp (Measurable.sub h1 h2)
  have hpair_meas : Measurable (fun ω : TwoCloudSpace q =>
      fun c : Cell => (cloudCellCount q k ω.1 c, cloudCellCount q k ω.2 c)) := by
    apply measurable_pi_iff.mpr
    intro c
    exact (show Measurable (fun ω : TwoCloudSpace q =>
        cloudCellCount q k ω.1 c) from
        Measurable.comp (measurable_pi_apply c)
          ((measurable_cloudCellCount q k).comp measurable_fst)).prodMk
      (show Measurable (fun ω : TwoCloudSpace q =>
        cloudCellCount q k ω.2 c) from
        Measurable.comp (measurable_pi_apply c)
          ((measurable_cloudCellCount q k).comp measurable_snd))
  have hpt : cloudCellDiscrepancy q k =
      fun ω => F (fun c : Cell =>
        (cloudCellCount q k ω.1 c, cloudCellCount q k ω.2 c)) := rfl
  rw [hpt]
  exact hF.comp hpair_meas

/-- The cell-count discrepancy is integrable under the two-cloud law. -/
theorem integrable_cloudCellDiscrepancy (q k : ℕ) (r : ℝ≥0) :
    Integrable (cloudCellDiscrepancy q k) (twoCloudLaw q r) := by
  have hsrc : Integrable (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := by
    simpa only using integrable_sourceCount q r
  have htgt : Integrable (fun ω : TwoCloudSpace q => ((targetCount ω : ℕ) : ℝ))
      (twoCloudLaw q r) := integrable_targetCount_twoCloudLaw q r
  refine Integrable.mono' (hsrc.add htgt)
    (measurable_cloudCellDiscrepancy q k).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (cloudCellDiscrepancy_nonneg q k ω)]
  exact cloudCellDiscrepancy_le_counts q k ω

end OTSelector.Probability
