import OTSelector.Finite.MaxCardValueMeasurable
import OTSelector.Probability.PoissonDyadicUpperBound
import OTSelector.Probability.PoissonDyadicDiscrepancy
import OTSelector.Probability.MultinomialCellDiscrepancy
import OTSelector.Probability.HierarchicalMatchingExpectation
import OTSelector.Limit.DyadicSeriesBound
import Mathlib.Algebra.BigOperators.Fin

/-!
# The fixed-size iid dyadic upper bound on the unit cube

This file proves the de-Poissonized analogue of `integral_shiftedValue_le_hier`:
for `n` iid uniform points in each of two clouds on the unit `q`-cube, the
expected maximum-cardinality matching cost with squared-distance edge cost
scaled by `n ^ (2 / q)` is bounded uniformly in `n` by a constant times `n`.

The proof follows the dyadic hierarchical scheme.  At depth `K`, every edge is
bounded by a terminal cell-diameter term plus the weighted sum of dyadic cell
mismatch indicators.  Under the iid law the level-`k` labels are independent
uniform labels in `(2 ^ k) ^ q = 2 ^ (k * q)` cells, so the expected histogram
discrepancy is bounded both by `sqrt (2 n 2 ^ (k * q))` and by `2 n`.  Inserting
the cap `min (2n) (sqrt (2 n 2 ^ (kq)))` makes the resulting geometric series
uniformly bounded in the depth, by `exists_dyadic_series_bound`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open OTSelector.Reconstruction

-- Local typeclass instances of the form `haveI` are needed for instance search.
set_option linter.style.haveILetI false

noncomputable section
namespace OTSelector.Probability

/-! ## The iid cube law -/

/-- The iid uniform law of `n` points on the unit `q`-cube. -/
noncomputable def fixedCubeLaw (q n : ℕ) : Measure (Fin n → Fin q → ℝ) :=
  Measure.pi (fun _ : Fin n => cubeMeasure (Fin q) 1)

instance fixedCubeLaw_isProbabilityMeasure (q n : ℕ) :
    IsProbabilityMeasure (fixedCubeLaw q n) := by
  unfold fixedCubeLaw
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  infer_instance

/-- The sample space of two independent iid `n`-point clouds on the unit cube. -/
abbrev FixedPairSpace (q n : ℕ) := (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ)

/-- The law of two independent iid samples of `n` points on the unit cube. -/
noncomputable def fixedPairLaw (q n : ℕ) :
    Measure (FixedPairSpace q n) :=
  (fixedCubeLaw q n).prod (fixedCubeLaw q n)

instance fixedPairLaw_isProbabilityMeasure (q n : ℕ) :
    IsProbabilityMeasure (fixedPairLaw q n) := by
  unfold fixedPairLaw
  infer_instance

/-! ## Almost-every point lies in the unit cube -/

/-- The coordinatewise truncation to the unit cube is measurable. -/
theorem measurable_cubeTruncPoint' (q : ℕ) :
    Measurable (cubeTruncPoint : (Fin q → ℝ) → (Fin q → ℝ)) := by
  apply measurable_pi_lambda
  intro l
  have hset : MeasurableSet {x : Fin q → ℝ | 0 ≤ x l ∧ x l < 1} :=
    measurableSet_Ico.preimage (measurable_pi_apply l)
  simpa only [cubeTruncPoint] using
    Measurable.ite hset (measurable_pi_apply l) measurable_const

/-- Almost every point of the uniform cube measure lies in the unit cube. -/
theorem ae_mem_unitCube_cubeMeasure' (q : ℕ) :
    ∀ᵐ x ∂(cubeMeasure (Fin q) 1), x ∈ unitCube q := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  rw [ae_iff]
  change (cubeMeasure (Fin q) 1) (unitCube q)ᶜ = 0
  rw [measure_compl (measurableSet_unitCube q)]
  · rw [cubeMeasure_unitCube, measure_univ]
    simp
  · rw [cubeMeasure_unitCube]
    exact ENNReal.one_ne_top

/-- Almost every point of the iid cube law lies in the unit cube. -/
theorem ae_points_mem_unitCube_fixedCubeLaw (q n : ℕ) :
    ∀ᵐ x ∂(fixedCubeLaw q n),
      x ∈ Set.pi Set.univ (fun _ : Fin n => unitCube q) := by
  let hprob : ∀ i : Fin n, IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  unfold fixedCubeLaw
  rw [ae_all_iff]
  intro i
  exact (@measurePreserving_eval (Fin n) (fun _ : Fin n => Fin q → ℝ) _
    (fun _ => inferInstance) (fun _ : Fin n => cubeMeasure (Fin q) 1) hprob i).quasiMeasurePreserving.ae
    (ae_mem_unitCube_cubeMeasure' q)

/-- Almost every pair of points of the two iid cube laws lies in the unit cube. -/
theorem ae_points_mem_unitCube_fixedPairLaw (q n : ℕ) :
    ∀ᵐ z ∂(fixedPairLaw q n),
      (∀ i : Fin n, z.1 i ∈ unitCube q) ∧ (∀ j : Fin n, z.2 j ∈ unitCube q) := by
  unfold fixedPairLaw
  have h1 : ∀ᵐ z ∂((fixedCubeLaw q n).prod (fixedCubeLaw q n)),
      z.1 ∈ Set.pi Set.univ (fun _ : Fin n => unitCube q) :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_points_mem_unitCube_fixedCubeLaw q n)
  have h2 : ∀ᵐ z ∂((fixedCubeLaw q n).prod (fixedCubeLaw q n)),
      z.2 ∈ Set.pi Set.univ (fun _ : Fin n => unitCube q) :=
    Measure.quasiMeasurePreserving_snd.ae
      (ae_points_mem_unitCube_fixedCubeLaw q n)
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨fun i => Set.mem_pi.mp hz1 i (Set.mem_univ i),
    fun j => Set.mem_pi.mp hz2 j (Set.mem_univ j)⟩

/-! ## Dyadic cells reindexed into `Fin ((2 ^ k) ^ q)` -/

/-- The level-`k` dyadic cell label, reindexed into `Fin ((2 ^ k) ^ q)`. -/
noncomputable def fixedCell (q k : ℕ) (x : Fin q → ℝ) : Fin ((2 ^ k) ^ q) :=
  finFunctionFinEquiv (m := 2 ^ k) (n := q) (dyadicCell q k x)

theorem measurable_fixedCell (q k : ℕ) : Measurable (fixedCell q k) :=
  (measurable_of_countable (fun w : Fin q → Fin (2 ^ k) =>
    finFunctionFinEquiv (m := 2 ^ k) (n := q) w)).comp (measurable_dyadicCell q k)

/-- Equality of finer fixed cells implies equality of coarser fixed cells. -/
theorem fixedCell_nested {q k l : ℕ} (hkl : k ≤ l) {x y : Fin q → ℝ}
    (h : fixedCell q l x = fixedCell q l y) : fixedCell q k x = fixedCell q k y := by
  have h' : dyadicCell q l x = dyadicCell q l y := by
    simpa only [fixedCell] using
      (finFunctionFinEquiv (m := 2 ^ l) (n := q)).injective h
  exact congrArg (fun w : Fin q → Fin (2 ^ k) =>
    finFunctionFinEquiv (m := 2 ^ k) (n := q) w)
    (dyadicCell_nested_global hkl h')

/-- The partition distance of reindexed cells equals that of the original dyadic cells. -/
theorem partitionDistance_fixedCell (q k : ℕ) (x y : Fin q → ℝ) :
    partitionDistance (fixedCell q k x) (fixedCell q k y) =
      partitionDistance (dyadicCell q k x) (dyadicCell q k y) := by
  classical
  simp only [partitionDistance, fixedCell]
  by_cases h : dyadicCell q k x = dyadicCell q k y
  · simp [h]
  · have h' : ¬ (finFunctionFinEquiv (m := 2 ^ k) (n := q) (dyadicCell q k x) =
        finFunctionFinEquiv (m := 2 ^ k) (n := q) (dyadicCell q k y)) :=
      fun hh => h ((finFunctionFinEquiv (m := 2 ^ k) (n := q)).injective hh)
    simp [h, h']

/-- `sqDist` is nonnegative. -/
theorem sqDist_nonneg' {q : ℕ} (x y : Fin q → ℝ) : 0 ≤ sqDist x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The squared distance of two truncated points is bounded by the number of coordinates. -/
theorem sqDist_cubeTruncPoint_le_card (q : ℕ) (x y : Fin q → ℝ) :
    sqDist (cubeTruncPoint x) (cubeTruncPoint y) ≤ (q : ℝ) := by
  have hterm : ∀ l : Fin q,
      (cubeTruncPoint x l - cubeTruncPoint y l) ^ 2 ≤ (1 : ℝ) := by
    intro l
    have hx := cubeTruncPoint_mem x l
    have hy := cubeTruncPoint_mem y l
    have habs : |cubeTruncPoint x l - cubeTruncPoint y l| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
    simpa [sq_abs] using h
  calc sqDist (cubeTruncPoint x) (cubeTruncPoint y)
      = ∑ l : Fin q, (cubeTruncPoint x l - cubeTruncPoint y l) ^ 2 := rfl
    _ ≤ ∑ _l : Fin q, (1 : ℝ) := Finset.sum_le_sum fun l _ => hterm l
    _ = (q : ℝ) := by simp

/-- The pathwise dyadic edge bound with reindexed cells. -/
theorem fixed_dyadic_edge_bound (q : ℕ) {K : ℕ} (hK : 0 < K) (x y : Fin q → ℝ) :
    sqDist (cubeTruncPoint x) (cubeTruncPoint y) ≤
      (4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K +
        ∑ k : Fin K, ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)) *
          partitionDistance (fixedCell q (k : ℕ) (cubeTruncPoint x))
            (fixedCell q (k : ℕ) (cubeTruncPoint y)) := by
  have hgeo := sq_dist_le_dyadic_partitionDistance (q := q) (K := K) hK
    (x := cubeTruncPoint x) (y := cubeTruncPoint y)
    (cubeTruncPoint_mem x) (cubeTruncPoint_mem y)
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k) *
      partitionDistance (dyadicCell q k (cubeTruncPoint x))
        (dyadicCell q k (cubeTruncPoint y))) K] at hgeo
  simpa only [sqDist, partitionDistance_fixedCell] using hgeo

/-! ## The cell-count law -/

/-- Pushing the uniform measure on a finite type forward along an equivalence
gives the uniform measure on the target. -/
private lemma map_uniformMeasure_equiv_fin {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Fintype α] [Fintype β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformMeasure α).map e = uniformMeasure β := by
  classical
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

/-- The level-`k` dyadic labels of `n` iid cube points are independent uniform
labels in `(2 ^ k) ^ q` cells. -/
theorem map_fixedCell_iid (q n k : ℕ) :
    (fixedCubeLaw q n).map (fun x : Fin n → Fin q → ℝ =>
      fun i : Fin n => fixedCell q k (x i)) =
      iidUniformMeasure n ((2 ^ k) ^ q) := by
  have hprob : ∀ i : Fin n, IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)
  have hW : Measurable (fun x : Fin n → Fin q → ℝ =>
      fun i : Fin n => dyadicCell q k (x i)) :=
    measurable_pi_lambda _ fun i =>
      (measurable_dyadicCell q k).comp (measurable_pi_apply i)
  have hE : Measurable (fun w : Fin n → (Fin q → Fin (2 ^ k)) =>
      fun i : Fin n => finFunctionFinEquiv (m := 2 ^ k) (n := q) (w i)) :=
    measurable_pi_lambda _ fun i =>
      (measurable_of_countable (fun w : Fin q → Fin (2 ^ k) =>
        finFunctionFinEquiv (m := 2 ^ k) (n := q) w)).comp (measurable_pi_apply i)
  have hsigW : ∀ i : Fin n, SigmaFinite ((cubeMeasure (Fin q) 1).map (dyadicCell q k)) :=
    fun _ => by
      rw [map_dyadicCell_uniform q k]
      infer_instance
  have hmapW : (fixedCubeLaw q n).map (fun x => fun i => dyadicCell q k (x i)) =
      Measure.pi (fun _ : Fin n => uniformMeasure (Fin q → Fin (2 ^ k))) := by
    unfold fixedCubeLaw
    rw [Measure.pi_map_pi (μ := fun _ : Fin n => cubeMeasure (Fin q) 1)
      (f := fun _ => dyadicCell q k) (hμ := hsigW)
      (fun _ => (measurable_dyadicCell q k).aemeasurable)]
    simp only [map_dyadicCell_uniform q k]
  have hsigE : ∀ i : Fin n, SigmaFinite
      ((uniformMeasure (Fin q → Fin (2 ^ k))).map
        (fun w => finFunctionFinEquiv (m := 2 ^ k) (n := q) w)) := fun _ => by
    rw [map_uniformMeasure_equiv_fin]
    infer_instance
  have hmapE : (Measure.pi (fun _ : Fin n => uniformMeasure (Fin q → Fin (2 ^ k)))).map
      (fun w => fun i => finFunctionFinEquiv (m := 2 ^ k) (n := q) (w i)) =
      Measure.pi (fun _ : Fin n => uniformMeasure (Fin ((2 ^ k) ^ q))) := by
    rw [Measure.pi_map_pi (μ := fun _ : Fin n => uniformMeasure (Fin q → Fin (2 ^ k)))
      (f := fun _ => fun w : Fin q → Fin (2 ^ k) =>
        finFunctionFinEquiv (m := 2 ^ k) (n := q) w) (hμ := hsigE)
      (fun _ => (measurable_of_countable (fun w : Fin q → Fin (2 ^ k) =>
        finFunctionFinEquiv (m := 2 ^ k) (n := q) w)).aemeasurable)]
    simp only [map_uniformMeasure_equiv_fin]
  calc (fixedCubeLaw q n).map (fun x => fun i => fixedCell q k (x i))
      = (fixedCubeLaw q n).map
          ((fun w : Fin n → (Fin q → Fin (2 ^ k)) =>
            fun i => finFunctionFinEquiv (m := 2 ^ k) (n := q) (w i)) ∘
            (fun x => fun i => dyadicCell q k (x i))) := rfl
    _ = ((fixedCubeLaw q n).map (fun x => fun i => dyadicCell q k (x i))).map
          (fun w => fun i => finFunctionFinEquiv (m := 2 ^ k) (n := q) (w i)) :=
        (Measure.map_map hE hW).symm
    _ = (Measure.pi (fun _ : Fin n => uniformMeasure (Fin q → Fin (2 ^ k)))).map
          (fun w => fun i => finFunctionFinEquiv (m := 2 ^ k) (n := q) (w i)) := by
        rw [hmapW]
    _ = Measure.pi (fun _ : Fin n => uniformMeasure (Fin ((2 ^ k) ^ q))) := hmapE
    _ = iidUniformMeasure n ((2 ^ k) ^ q) := rfl

/-- The law of the level-`k` labels of two iid cube clouds. -/
theorem map_fixedCell_pair (q n k : ℕ) :
    (fixedPairLaw q n).map
      (fun z : (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ) =>
        (fun i : Fin n => fixedCell q k (z.1 i),
          fun j : Fin n => fixedCell q k (z.2 j))) =
      (iidUniformMeasure n ((2 ^ k) ^ q)).prod
        (iidUniformMeasure n ((2 ^ k) ^ q)) := by
  have hW : Measurable (fun x : Fin n → Fin q → ℝ =>
      fun i : Fin n => fixedCell q k (x i)) :=
    measurable_pi_lambda _ fun i => (measurable_fixedCell q k).comp (measurable_pi_apply i)
  unfold fixedPairLaw
  rw [show (fun z : (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ) =>
        (fun i : Fin n => fixedCell q k (z.1 i),
          fun j : Fin n => fixedCell q k (z.2 j))) =
      Prod.map (fun x : Fin n → Fin q → ℝ => fun i : Fin n => fixedCell q k (x i))
        (fun x : Fin n → Fin q → ℝ => fun i : Fin n => fixedCell q k (x i)) from rfl]
  rw [← Measure.map_prod_map (μa := fixedCubeLaw q n) (μc := fixedCubeLaw q n) hW hW,
    map_fixedCell_iid]

/-! ## The truncated-label law -/

/-- The level-`k` labels of truncated iid cube points are still iid uniform. -/
theorem map_truncFixedCell_iid (q n k : ℕ) :
    (fixedCubeLaw q n).map (fun x : Fin n → Fin q → ℝ =>
      fun i : Fin n => fixedCell q k (cubeTruncPoint (x i))) =
      iidUniformMeasure n ((2 ^ k) ^ q) := by
  have hae : (fun x : Fin n → Fin q → ℝ =>
        fun i : Fin n => fixedCell q k (cubeTruncPoint (x i)))
      =ᵐ[fixedCubeLaw q n] (fun x : Fin n → Fin q → ℝ =>
        fun i : Fin n => fixedCell q k (x i)) := by
    filter_upwards [ae_points_mem_unitCube_fixedCubeLaw q n] with x hx
    funext i
    rw [cubeTruncPoint_eq_of_mem (Set.mem_pi.mp hx i (Set.mem_univ i))]
  rw [Measure.map_congr hae]
  exact map_fixedCell_iid q n k

/-- The law of the level-`k` truncated labels of two iid cube clouds. -/
theorem map_truncFixedCell_pair (q n k : ℕ) :
    (fixedPairLaw q n).map
      (fun z : (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ) =>
        (fun i : Fin n => fixedCell q k (cubeTruncPoint (z.1 i)),
          fun j : Fin n => fixedCell q k (cubeTruncPoint (z.2 j)))) =
      (iidUniformMeasure n ((2 ^ k) ^ q)).prod
        (iidUniformMeasure n ((2 ^ k) ^ q)) := by
  have hW : Measurable (fun x : Fin n → Fin q → ℝ =>
      fun i : Fin n => fixedCell q k (cubeTruncPoint (x i))) :=
    measurable_pi_lambda _ fun i =>
      (measurable_fixedCell q k).comp
        ((measurable_cubeTruncPoint' q).comp (measurable_pi_apply i))
  unfold fixedPairLaw
  rw [show (fun z : (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ) =>
        (fun i : Fin n => fixedCell q k (cubeTruncPoint (z.1 i)),
          fun j : Fin n => fixedCell q k (cubeTruncPoint (z.2 j)))) =
      Prod.map (fun x : Fin n → Fin q → ℝ =>
          fun i : Fin n => fixedCell q k (cubeTruncPoint (x i)))
        (fun x : Fin n → Fin q → ℝ =>
          fun i : Fin n => fixedCell q k (cubeTruncPoint (x i))) from rfl]
  rw [← Measure.map_prod_map (μa := fixedCubeLaw q n) (μc := fixedCubeLaw q n) hW hW,
    map_truncFixedCell_iid]

/-! ## Partition counts versus `labelCount` -/

/-- The partition count of a word equals its label count, cast to `ℝ`. -/
theorem partitionCount_eq_labelCount_cast {n K : ℕ} (w : Fin n → Fin K) (c : Fin K) :
    partitionCount w c = (labelCount w c : ℝ) := by
  classical
  rw [partitionCount, labelCount,
    Finset.natCast_card_filter (fun i => w i = c) Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  unfold partitionIndicator
  by_cases h : w i = c <;> simp [h]

theorem partitionCount_nonneg' {n K : ℕ} (w : Fin n → Fin K) (c : Fin K) :
    0 ≤ partitionCount w c := by
  classical
  unfold partitionCount
  apply Finset.sum_nonneg
  intro i _
  unfold partitionIndicator
  split_ifs <;> norm_num

/-- The partition counts of a word sum to its length. -/
theorem sum_partitionCount_eq {n K : ℕ} (w : Fin n → Fin K) :
    ∑ c : Fin K, partitionCount w c = (n : ℝ) := by
  classical
  simp only [partitionCount_eq_labelCount_cast]
  rw [← Nat.cast_sum, sum_labelCount]

/-- The pointwise `ℓ¹` partition-count discrepancy of two words of the same
length is at most twice that length. -/
theorem sum_abs_partitionCount_sub_le {n K : ℕ} (w₁ w₂ : Fin n → Fin K) :
    ∑ c : Fin K, |partitionCount w₁ c - partitionCount w₂ c| ≤ 2 * (n : ℝ) := by
  classical
  calc ∑ c : Fin K, |partitionCount w₁ c - partitionCount w₂ c|
      ≤ ∑ c : Fin K, (partitionCount w₁ c + partitionCount w₂ c) := by
        apply Finset.sum_le_sum
        intro c _
        rw [abs_sub_le_iff]
        constructor <;>
          linarith [partitionCount_nonneg' w₁ c, partitionCount_nonneg' w₂ c]
    _ = (∑ c : Fin K, partitionCount w₁ c) + ∑ c : Fin K, partitionCount w₂ c :=
        Finset.sum_add_distrib
    _ = (n : ℝ) + (n : ℝ) := by rw [sum_partitionCount_eq, sum_partitionCount_eq]
    _ = 2 * (n : ℝ) := by ring

/-! ## The cell-count discrepancy of two iid clouds -/

/-- The level-`k` dyadic cell-count discrepancy of two truncated iid cube clouds. -/
noncomputable def fixedDiscrepancy (q n k : ℕ)
    (z : (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ)) : ℝ :=
  ∑ c : Fin ((2 ^ k) ^ q),
    |partitionCount (fun i : Fin n => fixedCell q k (cubeTruncPoint (z.1 i))) c -
      partitionCount (fun j : Fin n => fixedCell q k (cubeTruncPoint (z.2 j))) c|

theorem measurable_fixedDiscrepancy (q n k : ℕ) :
    Measurable (fixedDiscrepancy q n k) := by
  classical
  unfold fixedDiscrepancy
  apply Finset.measurable_sum
  intro c _
  apply continuous_abs.measurable.comp
  apply Measurable.sub
  · unfold partitionCount
    apply Finset.measurable_sum
    intro i _
    unfold partitionIndicator
    apply Measurable.ite
    · exact (measurableSet_singleton c).preimage
        ((measurable_fixedCell q k).comp
          ((measurable_cubeTruncPoint' q).comp (by fun_prop)))
    · exact measurable_const
    · exact measurable_const
  · unfold partitionCount
    apply Finset.measurable_sum
    intro j _
    unfold partitionIndicator
    apply Measurable.ite
    · exact (measurableSet_singleton c).preimage
        ((measurable_fixedCell q k).comp
          ((measurable_cubeTruncPoint' q).comp (by fun_prop)))
    · exact measurable_const
    · exact measurable_const

theorem fixedDiscrepancy_nonneg (q n k : ℕ)
    (z : (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ)) :
    0 ≤ fixedDiscrepancy q n k z := by
  classical
  unfold fixedDiscrepancy
  exact Finset.sum_nonneg fun c _ => abs_nonneg _

theorem fixedDiscrepancy_le_two_mul (q n k : ℕ)
    (z : (Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ)) :
    fixedDiscrepancy q n k z ≤ 2 * (n : ℝ) := by
  classical
  unfold fixedDiscrepancy
  exact sum_abs_partitionCount_sub_le _ _

theorem integrable_fixedDiscrepancy (q n k : ℕ) :
    Integrable (fixedDiscrepancy q n k) (fixedPairLaw q n) := by
  refine Integrable.of_bound (measurable_fixedDiscrepancy q n k).aestronglyMeasurable
    (2 * (n : ℝ)) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (fixedDiscrepancy_nonneg q n k z)]
  exact fixedDiscrepancy_le_two_mul q n k z

/-- The expected level-`k` cell-count discrepancy is at most the square-root bound. -/
theorem integral_fixedDiscrepancy_le_sqrt (q n k : ℕ) :
    ∫ z, fixedDiscrepancy q n k z ∂(fixedPairLaw q n)
      ≤ Real.sqrt (2 * (n : ℝ) * (((2 ^ k) ^ q : ℕ) : ℝ)) := by
  classical
  haveI hK : NeZero ((2 ^ k) ^ q) :=
    ⟨Nat.ne_of_gt (pow_pos (pow_pos (by norm_num : 0 < 2) k) q)⟩
  let Φ : ((Fin n → Fin q → ℝ) × (Fin n → Fin q → ℝ)) →
      ((Fin n → Fin ((2 ^ k) ^ q)) × (Fin n → Fin ((2 ^ k) ^ q))) :=
    fun z => (fun i : Fin n => fixedCell q k (cubeTruncPoint (z.1 i)),
      fun j : Fin n => fixedCell q k (cubeTruncPoint (z.2 j)))
  let F : ((Fin n → Fin ((2 ^ k) ^ q)) × (Fin n → Fin ((2 ^ k) ^ q))) → ℝ :=
    fun w => ∑ c : Fin ((2 ^ k) ^ q),
      |(labelCount w.1 c : ℝ) - (labelCount w.2 c : ℝ)|
  have hΦ : Measurable Φ := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i =>
        (measurable_fixedCell q k).comp
          ((measurable_cubeTruncPoint' q).comp (by fun_prop))
    · exact measurable_pi_lambda _ fun j =>
        (measurable_fixedCell q k).comp
          ((measurable_cubeTruncPoint' q).comp (by fun_prop))
  have hF : Measurable F := measurable_of_countable F
  have hpt : ∀ z, fixedDiscrepancy q n k z = F (Φ z) := by
    intro z
    simp only [fixedDiscrepancy, F, Φ, partitionCount_eq_labelCount_cast]
  have hmap : (fixedPairLaw q n).map Φ =
      (iidUniformMeasure n ((2 ^ k) ^ q)).prod
        (iidUniformMeasure n ((2 ^ k) ^ q)) := by
    simpa only [Φ] using map_truncFixedCell_pair q n k
  calc ∫ z, fixedDiscrepancy q n k z ∂(fixedPairLaw q n)
      = ∫ w, F w ∂((fixedPairLaw q n).map Φ) := by
        rw [show (fun z => fixedDiscrepancy q n k z) = F ∘ Φ from funext hpt]
        exact (integral_map hΦ.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ w, F w ∂((iidUniformMeasure n ((2 ^ k) ^ q)).prod
          (iidUniformMeasure n ((2 ^ k) ^ q))) := by
        rw [hmap]
    _ ≤ Real.sqrt (2 * (n : ℝ) * (((2 ^ k) ^ q : ℕ) : ℝ)) := by
        simpa only [F] using integral_sum_abs_labelCount_sub_le n ((2 ^ k) ^ q)

/-- The expected level-`k` cell-count discrepancy is at most `2 n`. -/
theorem integral_fixedDiscrepancy_le_trivial (q n k : ℕ) :
    ∫ z, fixedDiscrepancy q n k z ∂(fixedPairLaw q n) ≤ 2 * (n : ℝ) := by
  calc ∫ z, fixedDiscrepancy q n k z ∂(fixedPairLaw q n)
      ≤ ∫ _z, 2 * (n : ℝ) ∂(fixedPairLaw q n) :=
        integral_mono (integrable_fixedDiscrepancy q n k) (integrable_const _)
          (fun z => fixedDiscrepancy_le_two_mul q n k z)
    _ = 2 * (n : ℝ) := by simp

/-! ## The integrated dyadic bound at a fixed depth -/

/-- With nonnegative edge costs the maximum-cardinality value is nonnegative. -/
theorem maxCardValue_nonneg_of_nonneg {m n : ℕ} {c : Fin m → Fin n → ℝ}
    (hc : ∀ i j, 0 ≤ c i j) : 0 ≤ PartialMatching.maxCardValue c := by
  exact PartialMatching.maxCardValue_nonneg hc

set_option maxHeartbeats 800000 in
/-- The integrated dyadic upper bound at a fixed depth `K`: the terminal
cell-diameter term contributes `n ^ (2/q) * 4q * (1/4)^K * n`, and each level
contributes the capped discrepancy. -/
theorem integral_fixedCardValue_le_depth (q n K : ℕ) (hq : 4 < q) (hK : 0 < K) :
    ∫ z, PartialMatching.maxCardValue (fun i : Fin n => fun j : Fin n =>
        (n : ℝ) ^ (2 / (q : ℝ)) * sqDist (z.1 i) (z.2 j)) ∂(fixedPairLaw q n)
    ≤ (n : ℝ) ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) * (n : ℝ) +
      (1 / 2 : ℝ) * ∑ k : Fin K,
        ((n : ℝ) ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
          min (2 * (n : ℝ))
            (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ ((k : ℕ) * q))) := by
  classical
  let P : Measure (FixedPairSpace q n) := fixedPairLaw q n
  haveI hP : IsProbabilityMeasure P := by unfold P; infer_instance
  let cell : (k : Fin K) → (Fin q → ℝ) → Fin ((2 ^ (k : ℕ)) ^ q) :=
    fun k => fixedCell q (k : ℕ)
  have hnested : ∀ (k l : Fin K), k ≤ l → ∀ x y : Fin q → ℝ,
      cell l x = cell l y → cell k x = cell k y := by
    intro k l hkl x y h
    exact fixedCell_nested (by exact_mod_cast hkl) h
  let base : ℝ := (n : ℝ) ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K)
  let weight : Fin K → ℝ := fun k =>
    (n : ℝ) ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (2 / (q : ℝ)) := Real.rpow_nonneg hnnonneg _
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hbase0 : 0 ≤ base := by
    dsimp only [base]
    exact mul_nonneg hrpow (mul_nonneg (by positivity) (by positivity))
  have hweight0 : ∀ k, 0 ≤ weight k := by
    intro k
    dsimp only [weight]
    exact mul_nonneg hrpow (mul_nonneg (by positivity) (by positivity))
  let x : FixedPairSpace q n → Fin n → (Fin q → ℝ) := fun z i => cubeTruncPoint (z.1 i)
  let y : FixedPairSpace q n → Fin n → (Fin q → ℝ) := fun z j => cubeTruncPoint (z.2 j)
  let cost : FixedPairSpace q n → Fin n → Fin n → ℝ := fun z i j =>
    (n : ℝ) ^ (2 / (q : ℝ)) * sqDist (x z i) (y z j)
  let costActual : FixedPairSpace q n → Fin n → Fin n → ℝ := fun z i j =>
    (n : ℝ) ^ (2 / (q : ℝ)) * sqDist (z.1 i) (z.2 j)
  have hcost : ∀ z i j, cost z i j ≤
      base + ∑ k : Fin K, weight k *
        partitionDistance (cell k (x z i)) (cell k (y z j)) := by
    intro z i j
    have hgeo := fixed_dyadic_edge_bound (q := q) (K := K) hK (z.1 i) (z.2 j)
    have hscaled := mul_le_mul_of_nonneg_left hgeo hrpow
    rw [mul_add, Finset.mul_sum] at hscaled
    calc cost z i j
        = (n : ℝ) ^ (2 / (q : ℝ)) *
            sqDist (cubeTruncPoint (z.1 i)) (cubeTruncPoint (z.2 j)) := rfl
      _ ≤ (n : ℝ) ^ (2 / (q : ℝ)) *
              ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
            ∑ k : Fin K, (n : ℝ) ^ (2 / (q : ℝ)) *
              (((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)) *
                partitionDistance (fixedCell q (k : ℕ) (cubeTruncPoint (z.1 i)))
                  (fixedCell q (k : ℕ) (cubeTruncPoint (z.2 j)))) := hscaled
      _ = base + ∑ k : Fin K, weight k *
            partitionDistance (cell k (x z i)) (cell k (y z j)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [weight, cell, x, y]
        ring
  have hnonneg : ∀ z i j, 0 ≤ cost z i j := by
    intro z i j
    exact mul_nonneg hrpow (sqDist_nonneg' _ _)
  have hmeasCost : ∀ i j, Measurable fun z : FixedPairSpace q n => cost z i j := by
    intro i j
    have h1 : Measurable (fun z : FixedPairSpace q n =>
        (cubeTruncPoint (z.1 i) : Fin q → ℝ)) :=
      (measurable_cubeTruncPoint' q).comp (by fun_prop)
    have h2 : Measurable (fun z : FixedPairSpace q n =>
        (cubeTruncPoint (z.2 j) : Fin q → ℝ)) :=
      (measurable_cubeTruncPoint' q).comp (by fun_prop)
    dsimp only [cost, x, y, sqDist]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro l _
    apply Measurable.pow
    · apply Measurable.sub
      · exact (measurable_pi_apply l).comp h1
      · exact (measurable_pi_apply l).comp h2
    · exact measurable_const
  have hV : Integrable (fun z => PartialMatching.maxCardValue (cost z)) P := by
    have hmeas : Measurable (fun z : FixedPairSpace q n =>
        PartialMatching.maxCardValue (cost z)) :=
      PartialMatching.measurable_maxCardValue cost hmeasCost
    have hbound : ∀ z : FixedPairSpace q n,
        PartialMatching.maxCardValue (cost z) ≤
          (n : ℝ) * ((n : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ)) := by
      intro z
      have hcard : (PartialMatching.diagonal n n).card = min n n :=
        PartialMatching.card_diagonal n n
      have hle := PartialMatching.maxCardValue_le_of_card (cost z) hcard
      have hcostle : (PartialMatching.diagonal n n).cost (cost z) ≤
          (n : ℝ) * ((n : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ)) := by
        unfold PartialMatching.cost
        calc ∑ p ∈ (PartialMatching.diagonal n n).edges, cost z p.1 p.2
            ≤ ∑ _p ∈ (PartialMatching.diagonal n n).edges,
                ((n : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ)) := by
              apply Finset.sum_le_sum
              intro p _
              dsimp only [cost]
              exact mul_le_mul_of_nonneg_left
                (sqDist_cubeTruncPoint_le_card q (z.1 p.1) (z.2 p.2)) hrpow
          _ = ((min n n : ℕ) : ℝ) * ((n : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              congr 1
              exact_mod_cast hcard
          _ = (n : ℝ) * ((n : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ)) := by simp
      exact hle.trans hcostle
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      ((n : ℝ) * ((n : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ))) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs,
      abs_of_nonneg (maxCardValue_nonneg_of_nonneg (fun i j => hnonneg z i j))]
    exact hbound z
  have hmax : Integrable (fun _ : FixedPairSpace q n => ((max n n : ℕ) : ℝ)) P := by
    simp
  have hDiff : Integrable (fun _ : FixedPairSpace q n =>
      |((n : ℝ) - (n : ℝ))|) P := by
    simp
  have hfunD : ∀ k : Fin K, (fun z : FixedPairSpace q n =>
        ∑ c : Fin ((2 ^ (k : ℕ)) ^ q),
          |partitionCount (cell k ∘ x z) c - partitionCount (cell k ∘ y z) c|)
      = fixedDiscrepancy q n (k : ℕ) := by
    intro k
    funext z
    rfl
  have hD : ∀ k : Fin K, Integrable (fun z : FixedPairSpace q n =>
      ∑ c : Fin ((2 ^ (k : ℕ)) ^ q),
        |partitionCount (cell k ∘ x z) c - partitionCount (cell k ∘ y z) c|) P := by
    intro k
    rw [hfunD k]
    exact integrable_fixedDiscrepancy q n (k : ℕ)
  have hcast : ∀ k : Fin K,
      (((2 ^ (k : ℕ)) ^ q : ℕ) : ℝ) = (2 : ℝ) ^ ((k : ℕ) * q) := by
    intro k
    rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul]
    norm_num
  have hDk : ∀ k : Fin K,
      ∫ z, (∑ c : Fin ((2 ^ (k : ℕ)) ^ q),
        |partitionCount (cell k ∘ x z) c - partitionCount (cell k ∘ y z) c|) ∂P ≤
        min (2 * (n : ℝ))
          (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ ((k : ℕ) * q))) := by
    intro k
    rw [hfunD k]
    apply le_min
    · exact integral_fixedDiscrepancy_le_trivial q n (k : ℕ)
    · have h := integral_fixedDiscrepancy_le_sqrt q n (k : ℕ)
      rw [hcast k] at h
      exact h
  have hbmax : ∫ _z : FixedPairSpace q n, ((max n n : ℕ) : ℝ) ∂P ≤ (n : ℝ) := by
    simp
  have hbdiff : ∫ _z : FixedPairSpace q n, |((n : ℝ) - (n : ℝ))| ∂P ≤ (0 : ℝ) := by
    simp
  have hmain := integral_maxCardValue_le_of_counts (P := P) (K := K)
    (C := fun k : Fin K => Fin ((2 ^ (k : ℕ)) ^ q))
    cell hnested base hbase0 weight hweight0
    (N := fun _ : FixedPairSpace q n => n) (M := fun _ : FixedPairSpace q n => n)
    (x := x) (y := y) (cost := cost)
    hcost hnonneg hV hmax hD hDiff
    (n : ℝ) hbmax
    (fun k : Fin K => min (2 * (n : ℝ))
      (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ ((k : ℕ) * q))))
    hDk (0 : ℝ) hbdiff
  have hae_cost : cost =ᵐ[P] costActual := by
    change ∀ᵐ z ∂(fixedPairLaw q n), cost z = costActual z
    filter_upwards [ae_points_mem_unitCube_fixedPairLaw q n] with z hz
    funext i j
    dsimp only [cost, costActual, x, y]
    rw [cubeTruncPoint_eq_of_mem (hz.1 i), cubeTruncPoint_eq_of_mem (hz.2 j)]
  have hae_val : (fun z : FixedPairSpace q n =>
        PartialMatching.maxCardValue (cost z)) =ᵐ[P]
      (fun z : FixedPairSpace q n => PartialMatching.maxCardValue (costActual z)) := by
    filter_upwards [hae_cost] with z hz
    rw [hz]
  have hIntEq : ∫ z, PartialMatching.maxCardValue (cost z) ∂P =
      ∫ z, PartialMatching.maxCardValue (costActual z) ∂P :=
    integral_congr_ae hae_val
  rw [hIntEq] at hmain
  simpa only [P, costActual, base, weight, add_zero] using hmain

/-! ## The uniform-in-size bound -/

/-- **The fixed-size iid dyadic upper bound.**  For `q > 4` there is a constant
`C ≥ 0` such that for every number of points `n` and every positive depth `K`,
the expected maximum-cardinality matching cost of two independent iid uniform
samples on the unit `q`-cube, with squared-distance edge cost scaled by
`n ^ (2 / q)`, is at most `C * n`.

The depth `K` is auxiliary: the integral does not depend on it.  The proof uses
the depth `Nat.ceil n`, the terminal cell-diameter bound `(1/4)^(ceil n) ≤
n^(-2/q)`, and `exists_dyadic_series_bound` for the capped level sum. -/
theorem exists_fixedCloud_dyadic_bound (q : ℕ) (hq : 4 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n K : ℕ), 0 < K →
      ∫ z, PartialMatching.maxCardValue (fun i : Fin n => fun j : Fin n =>
          (n : ℝ) ^ (2 / (q : ℝ)) * sqDist (z.1 i) (z.2 j))
        ∂(fixedPairLaw q n)
      ≤ C * (n : ℝ) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_dyadic_series_bound q hq
  refine ⟨4 * (q : ℝ) + C₀, ?_, ?_⟩
  · have hqpos : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  · intro n K hK
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · -- The empty sample: the value is zero.
      subst hn0
      have hd := integral_fixedCardValue_le_depth q 0 K hq hK
      have hexp : (2 : ℝ) / (q : ℝ) ≠ 0 := by positivity
      have hzero : (0 : ℝ) ^ (2 / (q : ℝ)) = 0 := Real.zero_rpow hexp
      simpa [hzero] using hd
    · -- Positive sample size: use the depth `ceil n`.
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
      let D : ℕ := Nat.ceil (n : ℝ)
      have hDge : (n : ℝ) ≤ (D : ℝ) := by
        simpa only [D] using Nat.le_ceil (n : ℝ)
      have hnleD : n ≤ D := by exact_mod_cast hDge
      have hDpos : 0 < D := by
        dsimp only [D]
        exact Nat.ceil_pos.mpr hnpos
      have hdepth := integral_fixedCardValue_le_depth q n D hq hDpos
      -- The terminal cell-diameter factor is at most `n^(-2/q)`.
      have hnle2D : (n : ℝ) ≤ (2 : ℝ) ^ D := by
        have h1 : (n : ℝ) < ((2 : ℕ) ^ n : ℝ) := by
          exact_mod_cast Nat.lt_two_pow_self
        have h2 : ((2 : ℕ) ^ n : ℝ) ≤ ((2 : ℕ) ^ D : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hnleD
        have h3 : ((2 : ℕ) ^ D : ℝ) = (2 : ℝ) ^ D := by norm_num
        linarith
      have hquarter : (1 / 4 : ℝ) ^ D ≤ (n : ℝ) ^ (-(2 / (q : ℝ))) := by
        have h1 : (1 / 4 : ℝ) ^ D = ((2 : ℝ) ^ D) ^ (-2 : ℝ) := by
          have hbase : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
            norm_num [Real.rpow_neg, Real.rpow_natCast]
          calc (1 / 4 : ℝ) ^ D = ((2 : ℝ) ^ (-2 : ℝ)) ^ D := by rw [hbase]
            _ = ((2 : ℝ) ^ (-2 : ℝ)) ^ (D : ℝ) := by rw [Real.rpow_natCast]
            _ = (2 : ℝ) ^ ((-2 : ℝ) * (D : ℝ)) :=
                (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-2) (D : ℝ)).symm
            _ = (2 : ℝ) ^ ((D : ℝ) * (-2 : ℝ)) := by ring_nf
            _ = ((2 : ℝ) ^ (D : ℝ)) ^ (-2 : ℝ) :=
                Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (D : ℝ) (-2)
            _ = ((2 : ℝ) ^ D) ^ (-2 : ℝ) := by rw [Real.rpow_natCast]
        rw [h1]
        have h2 : ((2 : ℝ) ^ D) ^ (-2 : ℝ) ≤ (n : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hnpos hnle2D (by norm_num)
        have hexp_le : (-2 : ℝ) ≤ -(2 / (q : ℝ)) := by
          have hq4 : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
          have h2q : (2 : ℝ) / (q : ℝ) ≤ 2 := by
            rw [div_le_iff₀ hqpos]
            linarith
          linarith
        have h3 : (n : ℝ) ^ (-2 : ℝ) ≤ (n : ℝ) ^ (-(2 / (q : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hexp_le
        linarith
      have hfac : (n : ℝ) ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ D ≤ 1 := by
        have h1 : (n : ℝ) ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ D
            ≤ (n : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (-(2 / (q : ℝ))) :=
          mul_le_mul_of_nonneg_left hquarter (Real.rpow_nonneg hnpos.le _)
        have h2 : (n : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (-(2 / (q : ℝ))) = 1 := by
          rw [← Real.rpow_add hnpos]
          have : (2 / (q : ℝ)) + -(2 / (q : ℝ)) = 0 := by ring
          rw [this, Real.rpow_zero]
        linarith
      have hbase_le : (n : ℝ) ^ (2 / (q : ℝ)) *
            ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ D) * (n : ℝ)
          ≤ 4 * (q : ℝ) * (n : ℝ) := by
        have h1 : (n : ℝ) ^ (2 / (q : ℝ)) *
              ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ D) * (n : ℝ) =
            (4 * (q : ℝ) * (n : ℝ)) *
              ((n : ℝ) ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ D) := by ring
        rw [h1]
        calc (4 * (q : ℝ) * (n : ℝ)) *
              ((n : ℝ) ^ (2 / (q : ℝ)) * (1 / 4 : ℝ) ^ D)
            ≤ (4 * (q : ℝ) * (n : ℝ)) * 1 := by
              apply mul_le_mul_of_nonneg_left hfac
              positivity
          _ = 4 * (q : ℝ) * (n : ℝ) := by ring
      -- Factor the scaled weight out of the depth sum.
      have hsum_fin : (∑ k : Fin D,
            ((n : ℝ) ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
              min (2 * (n : ℝ))
                (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ ((k : ℕ) * q))))
          = (n : ℝ) ^ (2 / (q : ℝ)) * ∑ k ∈ Finset.range D,
              (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                min (2 * (n : ℝ))
                  (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q))) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun k : ℕ => ((n : ℝ) ^ (2 / (q : ℝ)) *
            ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k)) *
              min (2 * (n : ℝ))
                (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q)))) D]
        trans ∑ k ∈ Finset.range D,
            (n : ℝ) ^ (2 / (q : ℝ)) *
              (((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k) *
                min (2 * (n : ℝ))
                  (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q))))
        · apply Finset.sum_congr rfl
          intro k _
          ring
        · rw [Finset.mul_sum]
      -- Apply the uniform geometric-series bound.
      have hseries : (1 / 2 : ℝ) * ∑ k ∈ Finset.range D,
            (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
              min (2 * (n : ℝ))
                (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q)))
          ≤ C₀ * (max 1 (n : ℝ)) ^ (1 - 2 / (q : ℝ)) := by
        have hsubset : Finset.range D ⊆ Finset.range (D + 1) := by
          apply Finset.range_subset_range.mpr
          omega
        have hterm_nonneg : ∀ k : ℕ,
            0 ≤ (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
              min (2 * (n : ℝ))
                (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q))) := by
          intro k
          have hmin : 0 ≤ min (2 * (n : ℝ))
              (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q))) :=
            le_min (by positivity) (Real.sqrt_nonneg _)
          positivity
        have hle : ∑ k ∈ Finset.range D,
              (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                min (2 * (n : ℝ))
                  (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q)))
            ≤ ∑ k ∈ Finset.range (D + 1),
              (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                min (2 * (n : ℝ))
                  (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun i _ _ => hterm_nonneg i)
        calc (1 / 2 : ℝ) * ∑ k ∈ Finset.range D,
              (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                min (2 * (n : ℝ))
                  (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q)))
            ≤ (1 / 2 : ℝ) * ∑ k ∈ Finset.range (D + 1),
              (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                min (2 * (n : ℝ))
                  (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q))) := by
              exact mul_le_mul_of_nonneg_left hle (by norm_num)
          _ ≤ C₀ * (max 1 (n : ℝ)) ^ (1 - 2 / (q : ℝ)) := hC₀ n D
      have hmax_eq : max 1 (n : ℝ) = (n : ℝ) :=
        max_eq_right (by exact_mod_cast hn)
      have hpow : (n : ℝ) ^ (2 / (q : ℝ)) *
          (n : ℝ) ^ (1 - 2 / (q : ℝ)) = (n : ℝ) := by
        rw [← Real.rpow_add hnpos]
        have : (2 / (q : ℝ)) + (1 - 2 / (q : ℝ)) = 1 := by ring
        rw [this, Real.rpow_one]
      calc ∫ z, PartialMatching.maxCardValue (fun i : Fin n => fun j : Fin n =>
              (n : ℝ) ^ (2 / (q : ℝ)) * sqDist (z.1 i) (z.2 j))
            ∂(fixedPairLaw q n)
          ≤ (n : ℝ) ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ D) *
                (n : ℝ) +
              (1 / 2 : ℝ) * ∑ k : Fin D,
                ((n : ℝ) ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
                  min (2 * (n : ℝ))
                    (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ ((k : ℕ) * q))) := hdepth
        _ = (n : ℝ) ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ D) *
                (n : ℝ) +
              (n : ℝ) ^ (2 / (q : ℝ)) * ((1 / 2 : ℝ) * ∑ k ∈ Finset.range D,
                (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                  min (2 * (n : ℝ))
                    (Real.sqrt (2 * (n : ℝ) * (2 : ℝ) ^ (k * q)))) := by
            rw [hsum_fin]
            ring
        _ ≤ 4 * (q : ℝ) * (n : ℝ) +
              (n : ℝ) ^ (2 / (q : ℝ)) *
                (C₀ * (max 1 (n : ℝ)) ^ (1 - 2 / (q : ℝ))) := by
            apply add_le_add hbase_le
            exact mul_le_mul_of_nonneg_left hseries (Real.rpow_nonneg hnpos.le _)
        _ = 4 * (q : ℝ) * (n : ℝ) +
              (n : ℝ) ^ (2 / (q : ℝ)) *
                (C₀ * (n : ℝ) ^ (1 - 2 / (q : ℝ))) := by
            rw [hmax_eq]
        _ = (4 * (q : ℝ) + C₀) * (n : ℝ) := by
            have h2 : (n : ℝ) ^ (2 / (q : ℝ)) *
                (C₀ * (n : ℝ) ^ (1 - 2 / (q : ℝ))) = C₀ * (n : ℝ) := by
              rw [← mul_assoc, mul_comm ((n : ℝ) ^ (2 / (q : ℝ))) C₀, mul_assoc, hpow]
            rw [h2]
            ring

end OTSelector.Probability
