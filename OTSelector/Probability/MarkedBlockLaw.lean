import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.MarkedSplitting
import OTSelector.MeasureTheory.CubeBlockDecomposition
import OTSelector.Probability.CubeMeasureScaling
import OTSelector.Probability.InfiniteProductLaw

/-!
# The block-decomposition law of marked Poisson clouds

A marked cloud on the unit cube `(0,1)^q` is tiled by the `m^q` blocks of side `m⁻¹`.
This file proves the two block-decomposition laws used by the dyadic pressure
comparison:

* the vector of block counts of a marked Poisson cloud of intensity `r` has
  independent Poisson coordinates of rate `r / m^q`; for two colours the count
  vector in each block is a product of two independent Poisson laws;
* the points of a marked cloud that fall in one block, rescaled by `m` to the unit
  cube, again form a marked Poisson cloud of intensity `r / m^q`.  The marked
  block is encoded as a `BlockData`, i.e. as a `Sigma` type carrying its own
  number of points; this is the canonical encoding of a Poisson point cloud
  whose count is part of the data.

The proof pushes the one-point law through the coordinatewise block map of
`CubeBlockDecomposition`, observes that the block label is uniform on `m^q`
labels and independent of the mark, and then applies the multinomial and marked
splitting theorems of `MultinomialSplitting` and `MarkedSplitting`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {A : Type*} [MeasurableSpace A]

/-! The unit-cube measure of a nonnegative dimension is a probability measure;
this instance avoids repeating the proof at every use. -/
instance instIsProbabilityMeasureCubeMeasureOne (q : ℕ) :
    IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
  isProbabilityMeasure_cubeMeasure (by norm_num)

instance instIsProbabilityMeasureCubeMeasureOneProd (q : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] :
    IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := inferInstance

/-! ## The block label and the local coordinate of a point -/

/-- The index of the block of side `m⁻¹` containing `x`, as a natural number. -/
noncomputable def blockLabel (q m : ℕ) (x : Fin q → ℝ) : Fin q → ℕ :=
  fun l => blockIndex ((m : ℝ)⁻¹) (x l)

/-- The local coordinate of `x` in its block, coordinatewise. -/
noncomputable def blockLocalPoint (q m : ℕ) (x : Fin q → ℝ) : Fin q → ℝ :=
  fun l => localCoord ((m : ℝ)⁻¹) (x l)

theorem measurable_blockLabel (q m : ℕ) : Measurable (blockLabel q m) :=
  measurable_pi_lambda _ fun l =>
    (measurable_blockIndex _).comp (measurable_pi_apply l)

theorem measurable_blockLocalPoint (q m : ℕ) : Measurable (blockLocalPoint q m) :=
  measurable_pi_lambda _ fun l =>
    (measurable_localCoord _).comp (measurable_pi_apply l)

/-- The coordinatewise block map of `CubeBlockDecomposition`, written in terms of
`blockLabel` and `blockLocalPoint`. -/
theorem blockMap_eq (q m : ℕ) (x : Fin q → ℝ) :
    blockMap (Fin q) ((m : ℝ)⁻¹) x = (blockLabel q m x, blockLocalPoint q m x) := rfl

theorem measurable_blockMap (ι : Type*) [Fintype ι] (L : ℝ) :
    Measurable (blockMap ι L) := by
  unfold blockMap
  exact (measurable_pi_lambda _ fun i =>
      (measurable_blockIndex L).comp (measurable_pi_apply i)).prod
    (measurable_pi_lambda _ fun i =>
      (measurable_localCoord L).comp (measurable_pi_apply i))

/-! ## The block index as an element of `Fin m` -/

/-- The inclusion `{0, …, m-1} → Fin m`, with junk value `0` outside the range. -/
def natToFin (m : ℕ) [NeZero m] (n : ℕ) : Fin m :=
  if h : n < m then ⟨n, h⟩ else 0

theorem natToFin_of_lt {m n : ℕ} [NeZero m] (h : n < m) :
    natToFin m n = ⟨n, h⟩ := by
  simp [natToFin, h]

theorem measurable_natToFin (m : ℕ) [NeZero m] : Measurable (natToFin m) :=
  measurable_of_countable _

/-- `⌊m x⌋` lies in `{0, …, m-1}` when `0 ≤ x < 1`. -/
theorem blockIndex_inv_lt {m : ℕ} [NeZero m] {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    blockIndex ((m : ℝ)⁻¹) x < m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hdiv : 0 ≤ x / (m : ℝ)⁻¹ := div_nonneg hx0 (inv_pos.mpr hmpos).le
  unfold blockIndex
  rw [Nat.floor_lt hdiv, div_inv_eq_mul]
  calc x * (m : ℝ) < 1 * (m : ℝ) := mul_lt_mul_of_pos_right hx1 hmpos
    _ = (m : ℝ) := one_mul _

/-- The block index of `x` as an element of `Fin m`. -/
def blockIndexFin (m : ℕ) [NeZero m] (x : ℝ) : Fin m :=
  natToFin m (blockIndex ((m : ℝ)⁻¹) x)

theorem blockIndexFin_apply {m : ℕ} [NeZero m] {x : ℝ}
    (h : blockIndex ((m : ℝ)⁻¹) x < m) :
    blockIndexFin m x = ⟨blockIndex ((m : ℝ)⁻¹) x, h⟩ :=
  natToFin_of_lt h

theorem measurable_blockIndexFin (m : ℕ) [NeZero m] : Measurable (blockIndexFin m) :=
  (measurable_natToFin m).comp (measurable_blockIndex _)

/-- The coordinatewise block label of a point, as a map into `Fin q → Fin m`. -/
def blockLabelFin (q m : ℕ) [NeZero m] (x : Fin q → ℝ) : Fin q → Fin m :=
  fun l => blockIndexFin m (x l)

theorem measurable_blockLabelFin (q m : ℕ) [NeZero m] :
    Measurable (blockLabelFin q m) :=
  measurable_pi_lambda _ fun l =>
    (measurable_blockIndexFin m).comp (measurable_pi_apply l)

/-- The block label encoded as an element of `Fin (m ^ q)` through
`finFunctionFinEquiv`. -/
def blockLabelCode (q m : ℕ) [NeZero m] (x : Fin q → ℝ) : Fin (m ^ q) :=
  finFunctionFinEquiv (blockLabelFin q m x)

theorem measurable_blockLabelCode (q m : ℕ) [NeZero m] :
    Measurable (blockLabelCode q m) :=
  (measurable_of_countable (finFunctionFinEquiv (m := m) (n := q))).comp
    (measurable_blockLabelFin q m)

/-- The encoding of a grid label `Fin q → ℕ` into `Fin (m ^ q)`, with junk outside
the grid `{0, …, m-1}^q`. -/
def gridEncode (q m : ℕ) [NeZero m] (u : Fin q → ℕ) : Fin (m ^ q) :=
  finFunctionFinEquiv (fun l => natToFin m (u l))

theorem blockLabelCode_eq_gridEncode (q m : ℕ) [NeZero m] (x : Fin q → ℝ) :
    blockLabelCode q m x = gridEncode q m (blockLabel q m x) := rfl

theorem measurable_gridEncode (q m : ℕ) [NeZero m] : Measurable (gridEncode q m) :=
  (measurable_of_countable (finFunctionFinEquiv (m := m) (n := q))).comp
    (measurable_pi_lambda (fun (u : Fin q → ℕ) (l : Fin q) => natToFin m (u l))
      (fun l => (measurable_natToFin m).comp (measurable_pi_apply l)))

/-! ## The uniform label law -/

/-- The mass of a singleton under `uniformGrid`. -/
theorem uniformGrid_singleton (m n : ℕ) :
    uniformGrid m {n} = (m : ℝ≥0∞)⁻¹ * (if n < m then 1 else 0) := by
  classical
  rw [uniformGrid, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ (measurableSet_singleton n)]
  congr 1
  rw [tsum_eq_single n]
  · by_cases h : n < m <;> simp [h]
  · intro k hk
    by_cases hk' : k < m
    · simp [hk', hk]
    · simp [hk']

/-- The uniform measure on `Fin m`, pushed forward by the inclusion into `ℕ`, is
the uniform grid measure. -/
theorem map_coe_uniformMeasure_eq_uniformGrid (m : ℕ) :
    (uniformMeasure (Fin m)).map (fun b : Fin m => (b : ℕ)) = uniformGrid m := by
  classical
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton n),
    uniformGrid_singleton]
  by_cases h : n < m
  · have hpre : (fun b : Fin m => (b : ℕ)) ⁻¹' {n} = {⟨n, h⟩} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
    rw [hpre, uniformMeasure_singleton, if_pos h, mul_one, Fintype.card_fin]
  · have hpre : (fun b : Fin m => (b : ℕ)) ⁻¹' {n} = ∅ := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hb
      exact h (hb ▸ b.isLt)
    rw [hpre, measure_empty, if_neg h, mul_zero]

/-- The inclusion `ℕ → Fin m` pushes `uniformGrid m` forward to `uniformMeasure (Fin m)`. -/
theorem map_natToFin_uniformGrid (m : ℕ) [NeZero m] (hm : 0 < m) :
    (uniformGrid m).map (natToFin m) = uniformMeasure (Fin m) := by
  rw [← map_coe_uniformMeasure_eq_uniformGrid m,
    Measure.map_map (measurable_natToFin m) (measurable_of_countable _)]
  have hcomp : natToFin m ∘ (fun b : Fin m => (b : ℕ)) = id := by
    funext b
    rw [Function.comp_apply, natToFin_of_lt b.isLt]
    exact Fin.ext rfl
  rw [hcomp, Measure.map_id]

/-- The block index pushes the uniform measure on the interval to the uniform grid. -/
theorem map_blockIndex_uniformInterval_eq_uniformGrid (m : ℕ) (hm : 0 < m) :
    (uniformInterval 1).map (blockIndex ((m : ℝ)⁻¹)) = uniformGrid m := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmul : (m : ℝ) * (m : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hmpos.ne'
  have hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  haveI : IsProbabilityMeasure (uniformInterval ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_uniformInterval hL
  have hblock := map_block_local_uniformInterval m hm hL
  rw [hmul] at hblock
  have hmap : ((uniformInterval 1).map
        (fun x : ℝ => (blockIndex ((m : ℝ)⁻¹) x, localCoord ((m : ℝ)⁻¹) x))).map Prod.fst =
      (uniformInterval 1).map (blockIndex ((m : ℝ)⁻¹)) := by
    rw [Measure.map_map measurable_fst (measurable_block_local _)]
    rfl
  rw [hblock, Measure.map_fst_prod, measure_univ, one_smul] at hmap
  exact hmap.symm

/-- The `Fin m`-valued block index pushes the uniform interval law to the uniform
measure on `Fin m`. -/
theorem map_blockIndexFin_uniformInterval (m : ℕ) [NeZero m] (hm : 0 < m) :
    (uniformInterval 1).map (blockIndexFin m) = uniformMeasure (Fin m) := by
  have hcomp : blockIndexFin m = natToFin m ∘ blockIndex ((m : ℝ)⁻¹) := rfl
  rw [hcomp, ← Measure.map_map (measurable_natToFin m) (measurable_blockIndex _)]
  rw [map_blockIndex_uniformInterval_eq_uniformGrid m hm,
    map_natToFin_uniformGrid m hm]

/-- The product of uniform measures on a finite type is the uniform measure on the
function space. -/
theorem pi_uniformMeasure_eq (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α : Type*) [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [Nonempty α] :
    Measure.pi (fun _ : ι => uniformMeasure α) = uniformMeasure (ι → α) := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton, uniformMeasure_singleton]
  simp only [uniformMeasure_singleton, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- A bijection pushes the uniform measure to the uniform measure. -/
theorem map_uniformMeasure_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Fintype α] [Fintype β]
    (e : α ≃ β) : (uniformMeasure α).map e = uniformMeasure β := by
  classical
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable e) (measurableSet_singleton b)]
  have hpre : e ⁻¹' {b} = {e.symm b} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro ha
      rw [← ha, Equiv.symm_apply_apply]
    · intro ha
      rw [ha, Equiv.apply_symm_apply]
  rw [hpre, uniformMeasure_singleton, uniformMeasure_singleton, Fintype.card_congr e]

/-- The encoding of a uniform grid label is uniform on `Fin (m ^ q)`. -/
theorem map_gridEncode_gridMeasure (q m : ℕ) [NeZero m] (hm : 0 < m) :
    (gridMeasure (Fin q) m).map (gridEncode q m) = uniformMeasure (Fin (m ^ q)) := by
  haveI hGrid : IsProbabilityMeasure (uniformGrid m) := isProbabilityMeasure_uniformGrid hm
  haveI : IsProbabilityMeasure (gridMeasure (Fin q) m) := by
    unfold gridMeasure
    infer_instance
  haveI : IsProbabilityMeasure ((uniformGrid m).map (fun n : ℕ => natToFin m n)) :=
    Measure.isProbabilityMeasure_map (measurable_natToFin m).aemeasurable
  haveI : ∀ _ : Fin q, SigmaFinite ((uniformGrid m).map (fun n : ℕ => natToFin m n)) :=
    fun _ => inferInstance
  have h1 : Measure.map (fun x i => natToFin m (x i))
      (Measure.pi (fun _ : Fin q => uniformGrid m)) =
      Measure.pi (fun _ : Fin q =>
        Measure.map (fun n => natToFin m n) (uniformGrid m)) :=
    Measure.pi_map_pi (μ := fun _ : Fin q => uniformGrid m)
      (f := fun _ (n : ℕ) => natToFin m n)
      (fun _ => (measurable_natToFin m).aemeasurable)
  have hnatMap : Measurable (fun u : Fin q → ℕ => fun l => natToFin m (u l)) :=
    measurable_pi_lambda (fun (u : Fin q → ℕ) (l : Fin q) => natToFin m (u l))
      (fun l => (measurable_natToFin m).comp (measurable_pi_apply l))
  have h2 : gridEncode q m =
      (finFunctionFinEquiv (m := m) (n := q)).toFun ∘
        (fun u : Fin q → ℕ => fun l => natToFin m (u l)) := rfl
  rw [h2, ← Measure.map_map (measurable_of_countable _) hnatMap]
  change (Measure.map (fun x i => natToFin m (x i))
      (Measure.pi (fun _ : Fin q => uniformGrid m))).map
        (finFunctionFinEquiv (m := m) (n := q)).toFun =
    uniformMeasure (Fin (m ^ q))
  rw [h1]
  rw [show (fun _ : Fin q => Measure.map (fun n => natToFin m n) (uniformGrid m)) =
      (fun _ : Fin q => uniformMeasure (Fin m)) from
    funext (fun _ => map_natToFin_uniformGrid m hm)]
  rw [pi_uniformMeasure_eq (Fin q) (Fin m)]
  exact map_uniformMeasure_equiv (finFunctionFinEquiv (m := m) (n := q))

/-- The coordinatewise block label of a uniform point on the cube is uniform on
`Fin (m ^ q)`. -/
theorem map_blockLabelCode_cubeMeasure (q m : ℕ) [NeZero m] (hm : 0 < m) :
    (cubeMeasure (Fin q) 1).map (blockLabelCode q m) = uniformMeasure (Fin (m ^ q)) := by
  haveI hInt : IsProbabilityMeasure (uniformInterval (1 : ℝ)) :=
    isProbabilityMeasure_uniformInterval (by norm_num)
  haveI hGrid : IsProbabilityMeasure (uniformGrid m) := isProbabilityMeasure_uniformGrid hm
  haveI hLab : IsProbabilityMeasure
      ((uniformInterval (1 : ℝ)).map (blockIndex ((m : ℝ)⁻¹))) :=
    Measure.isProbabilityMeasure_map (measurable_blockIndex _).aemeasurable
  haveI hNat : IsProbabilityMeasure
      ((uniformGrid m).map (fun n : ℕ => natToFin m n)) :=
    Measure.isProbabilityMeasure_map (measurable_natToFin m).aemeasurable
  haveI : ∀ _ : Fin q, SigmaFinite
      ((uniformInterval (1 : ℝ)).map (blockIndex ((m : ℝ)⁻¹))) :=
    fun _ => inferInstance
  haveI : ∀ _ : Fin q, SigmaFinite ((uniformGrid m).map (fun n : ℕ => natToFin m n)) :=
    fun _ => inferInstance
  have hlabel : (cubeMeasure (Fin q) 1).map (blockLabel q m) = gridMeasure (Fin q) m := by
    have h := Measure.pi_map_pi (μ := fun _ : Fin q => uniformInterval (1 : ℝ))
      (f := fun _ (x : ℝ) => blockIndex ((m : ℝ)⁻¹) x)
      (fun _ => (measurable_blockIndex _).aemeasurable)
    change Measure.map (fun x i => blockIndex ((m : ℝ)⁻¹) (x i))
        (Measure.pi (fun _ : Fin q => uniformInterval (1 : ℝ))) =
      Measure.pi (fun _ : Fin q => uniformGrid m)
    rw [show Measure.map (fun x i => blockIndex ((m : ℝ)⁻¹) (x i))
          (Measure.pi (fun _ : Fin q => uniformInterval (1 : ℝ))) =
        Measure.pi (fun _ : Fin q =>
          Measure.map (fun x => blockIndex ((m : ℝ)⁻¹) x) (uniformInterval 1)) from h]
    simp only [map_blockIndex_uniformInterval_eq_uniformGrid m hm]
  have hnat := map_gridEncode_gridMeasure q m hm
  calc
    (cubeMeasure (Fin q) 1).map (blockLabelCode q m)
        = (cubeMeasure (Fin q) 1).map ((gridEncode q m) ∘ (blockLabel q m)) := by
          rw [show blockLabelCode q m = (gridEncode q m) ∘ (blockLabel q m) from rfl]
    _ = ((cubeMeasure (Fin q) 1).map (blockLabel q m)).map (gridEncode q m) := by
          rw [Measure.map_map (measurable_gridEncode q m) (measurable_blockLabel q m)]
    _ = (gridMeasure (Fin q) m).map (gridEncode q m) := by rw [hlabel]
    _ = uniformMeasure (Fin (m ^ q)) := hnat

/-! ## The joint law of the block label and the local point -/

/-- The joint law of the block label and the local position of a uniform cube
point. -/
theorem map_blockLabel_local_cubeMeasure (q m : ℕ) (hm : 0 < m) :
    (cubeMeasure (Fin q) 1).map
        (fun x : Fin q → ℝ => (blockLabel q m x, blockLocalPoint q m x)) =
      (gridMeasure (Fin q) m).prod (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmul : (m : ℝ) * (m : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hmpos.ne'
  have hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  have hblock := map_blockMap_cubeMeasure (ι := Fin q) m hm hL
  rw [hmul] at hblock
  change (cubeMeasure (Fin q) 1).map
      (fun x : Fin q → ℝ => (blockLabel q m x, blockLocalPoint q m x)) =
    (gridMeasure (Fin q) m).prod (cubeMeasure (Fin q) ((m : ℝ)⁻¹))
  exact hblock

/-- The joint law of the encoded block label and the local position of a uniform
cube point. -/
theorem map_blockLabelCode_local_cubeMeasure (q m : ℕ) [NeZero m] (hm : 0 < m) :
    (cubeMeasure (Fin q) 1).map
        (fun x : Fin q → ℝ => (blockLabelCode q m x, blockLocalPoint q m x)) =
      (uniformMeasure (Fin (m ^ q))).prod (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure hL
  haveI hg : IsProbabilityMeasure (uniformGrid m) := isProbabilityMeasure_uniformGrid hm
  haveI : IsProbabilityMeasure (gridMeasure (Fin q) m) := by
    unfold gridMeasure
    infer_instance
  have hlabel := map_blockLabel_local_cubeMeasure q m hm
  have hcomp : (fun x : Fin q → ℝ => (blockLabelCode q m x, blockLocalPoint q m x)) =
      (Prod.map (gridEncode q m) id) ∘
        (fun x : Fin q → ℝ => (blockLabel q m x, blockLocalPoint q m x)) := by
    funext x
    rfl
  rw [hcomp, ← Measure.map_map (measurable_gridEncode q m |>.prodMap measurable_id)
    ((measurable_blockLabel q m).prod (measurable_blockLocalPoint q m))]
  rw [hlabel, ← Measure.map_prod_map (gridMeasure (Fin q) m)
    (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) (measurable_gridEncode q m) measurable_id]
  rw [map_gridEncode_gridMeasure q m hm, Measure.map_id]

/-! ## The one-point block law -/

/-- The coordinatewise block decomposition of a marked point: the encoded block
label together with the local position and the mark. -/
def markedBlockOnePoint (q m : ℕ) [NeZero m] (y : (Fin q → ℝ) × A) :
    Fin (m ^ q) × ((Fin q → ℝ) × A) :=
  (blockLabelCode q m y.1, (blockLocalPoint q m y.1, y.2))

theorem measurable_markedBlockOnePoint (q m : ℕ) [NeZero m] :
    Measurable (markedBlockOnePoint (A := A) q m) :=
  ((measurable_blockLabelCode q m).comp measurable_fst).prodMk
    (((measurable_blockLocalPoint q m).comp measurable_fst).prodMk measurable_snd)

/-- The one-point law of the block decomposition: the label is uniform on
`m ^ q` possibilities, independent of the local position and the mark. -/
theorem map_markedBlockOnePoint (q m : ℕ) [NeZero m] (hm : 0 < m)
    (α : Measure A) [IsProbabilityMeasure α] :
    ((cubeMeasure (Fin q) 1).prod α).map (markedBlockOnePoint (A := A) q m) =
      (uniformMeasure (Fin (m ^ q))).prod ((cubeMeasure (Fin q) ((m : ℝ)⁻¹)).prod α) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure hL
  have hlabel := map_blockLabelCode_local_cubeMeasure q m hm
  have hcomp : (markedBlockOnePoint (A := A) q m) =
      (MeasurableEquiv.prodAssoc) ∘
        (Prod.map (fun x : Fin q → ℝ =>
          (blockLabelCode q m x, blockLocalPoint q m x)) id) := by
    funext p
    rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable
    (((measurable_blockLabelCode q m).prod (measurable_blockLocalPoint q m)).prodMap
      measurable_id)]
  rw [← Measure.map_prod_map (cubeMeasure (Fin q) 1) α
    ((measurable_blockLabelCode q m).prod (measurable_blockLocalPoint q m)) measurable_id]
  rw [hlabel, Measure.map_id]
  exact Measure.prodAssoc_prod

/-! ## Almost everywhere membership in the unit cube -/

/-- The open unit cube `(0,1)^q`, viewed as the support of `cubeMeasure`. -/
def unitCubeSet (q : ℕ) : Set (Fin q → ℝ) :=
  Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) 1)

theorem ae_mem_uniformInterval_Ioo {L : ℝ} :
    ∀ᵐ x ∂(uniformInterval L), x ∈ Set.Ioo (0 : ℝ) L := by
  rw [uniformInterval]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _

theorem ae_mem_unitCubeSet_cubeMeasure (q : ℕ) :
    ∀ᵐ x ∂(cubeMeasure (Fin q) 1), x ∈ unitCubeSet q := by
  haveI hInt : IsProbabilityMeasure (uniformInterval (1 : ℝ)) :=
    isProbabilityMeasure_uniformInterval (by norm_num)
  haveI : ∀ _ : Fin q, IsProbabilityMeasure (uniformInterval (1 : ℝ)) := fun _ => hInt
  have h : ∀ᵐ x ∂(Measure.pi (fun _ : Fin q => uniformInterval (1 : ℝ))),
      ∀ l, x l ∈ Set.Ioo (0 : ℝ) 1 := by
    apply ae_all_iff.mpr
    intro l
    exact (measurePreserving_eval (μ := fun _ : Fin q => uniformInterval (1 : ℝ)) l)
      |>.quasiMeasurePreserving.ae (ae_mem_uniformInterval_Ioo (L := 1))
  simpa only [cubeMeasure, unitCubeSet, Set.mem_pi, Set.mem_univ, forall_true_left] using h

theorem ae_mem_unitCubeSet_markedSeqLaw (q : ℕ) (α : Measure A) [IsProbabilityMeasure α] :
    ∀ᵐ s ∂(markedSeqLaw (q := q) A α), ∀ i, (s i).1 ∈ unitCubeSet q := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  have hν : ∀ᵐ p ∂((cubeMeasure (Fin q) 1).prod α), p.1 ∈ unitCubeSet q :=
    measurePreserving_fst.quasiMeasurePreserving.ae (ae_mem_unitCubeSet_cubeMeasure q)
  rw [markedSeqLaw]
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval_infinitePi
    (μ := fun _ : ℕ => (cubeMeasure (Fin q) 1).prod α) i).quasiMeasurePreserving.ae hν

theorem ae_mem_unitCubeSet_markedPoissonLaw (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (r : ℝ≥0) :
    ∀ᵐ z ∂(markedPoissonLaw (q := q) A α r), ∀ i, (z.2 i).1 ∈ unitCubeSet q := by
  haveI : IsProbabilityMeasure (markedSeqLaw (q := q) A α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) A α
  haveI : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  rw [markedPoissonLaw]
  exact measurePreserving_snd.quasiMeasurePreserving.ae
    (ae_mem_unitCubeSet_markedSeqLaw (q := q) α)

/-- On the unit cube, the encoded label of a point agrees with the raw block
label exactly when the raw label is the given block. -/
theorem blockLabelCode_eq_finFunctionFinEquiv_iff {q m : ℕ} [NeZero m] {x : Fin q → ℝ}
    (hx : x ∈ unitCubeSet q) (b : Fin q → Fin m) :
    blockLabelCode q m x = finFunctionFinEquiv b ↔
      ∀ l, blockIndex ((m : ℝ)⁻¹) (x l) = (b l).val := by
  have hx' : ∀ l, x l ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [unitCubeSet, Set.mem_pi, Set.mem_univ, forall_true_left] using hx
  constructor
  · intro h l
    have hu : blockLabelFin q m x = b := finFunctionFinEquiv.injective h
    have hl : blockIndexFin m (x l) = b l := congrFun hu l
    rw [blockIndexFin_apply (blockIndex_inv_lt (m := m) (hx' l).1.le (hx' l).2)] at hl
    exact congrArg Fin.val hl
  · intro h
    have hfun : blockLabelFin q m x = b := by
      funext l
      show blockIndexFin m (x l) = b l
      rw [blockIndexFin_apply (blockIndex_inv_lt (m := m) (hx' l).1.le (hx' l).2)]
      exact Fin.ext (h l)
    rw [blockLabelCode, hfun]

/-! ## The block counts of a cloud -/

/-- The encoded block label of the `i`-th point of a cloud. -/
def markedLabelCode (q m : ℕ) [NeZero m] (z : MarkedCloudSpace q A) (i : ℕ) : Fin (m ^ q) :=
  blockLabelCode q m (z.2 i).1

/-- The vector of encoded block counts of a cloud. -/
def markedBlockCountCode (q m : ℕ) [NeZero m] (z : MarkedCloudSpace q A) :
    Fin (m ^ q) → ℕ :=
  fun b => (Finset.univ.filter (fun i : Fin z.1 => markedLabelCode q m z i = b)).card

/-- The number of points of the cloud that lie in the block `b`. -/
def markedBlockCount (q m : ℕ) (z : MarkedCloudSpace q A) (b : Fin q → Fin m) : ℕ :=
  (Finset.univ.filter (fun i : Fin z.1 =>
    ∀ l, blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l) = (b l).val)).card

theorem measurable_markedLabelCode (q m : ℕ) [NeZero m] (i : ℕ) :
    Measurable (fun z : MarkedCloudSpace q A => markedLabelCode q m z i) :=
  (measurable_blockLabelCode q m).comp
    (((measurable_pi_apply i).comp measurable_snd).fst)

/-- A general measurability statement for counts over the prefix of length `N`. -/
theorem measurable_prefixCount_eq {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] [DecidableEq β]
    (N : Ω → ℕ) (hN : Measurable N) (x : ℕ → Ω → β) (hx : ∀ i, Measurable (x i))
    (y : β) :
    Measurable (fun ξ => (Finset.univ.filter (fun i : Fin (N ξ) => x i ξ = y)).card) := by
  classical
  apply measurable_to_countable'
  intro n
  have hset : {ξ : Ω | (Finset.univ.filter (fun i : Fin (N ξ) => x i ξ = y)).card = n} =
      ⋃ m, ({ξ | N ξ = m} ∩
        {ξ | (Finset.univ.filter (fun i : Fin m => x i ξ = y)).card = n}) := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨N ξ, rfl, h⟩
    · rintro ⟨m, hm, h⟩; subst hm; exact h
  change MeasurableSet {ξ : Ω |
    (Finset.univ.filter (fun i : Fin (N ξ) => x i ξ = y)).card = n}
  rw [hset]
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.inter
  · exact hN (measurableSet_singleton m)
  · have hcount : Measurable (fun v : Fin m → β =>
        (Finset.univ.filter (fun i : Fin m => v i = y)).card) :=
      measurable_of_countable _
    exact hcount.comp (measurable_pi_lambda _ (fun i => hx i)) (measurableSet_singleton n)

theorem measurable_markedBlockCountCode (q m : ℕ) [NeZero m] :
    Measurable (markedBlockCountCode (A := A) q m) := by
  classical
  rw [measurable_pi_iff]
  intro b
  exact measurable_prefixCount_eq (fun z : MarkedCloudSpace q A => z.1) measurable_fst
    (fun i z => markedLabelCode q m z i) (fun i => measurable_markedLabelCode q m i) b

theorem measurable_markedBlockCount (q m : ℕ) (b : Fin q → Fin m) :
    Measurable (fun z : MarkedCloudSpace q A => markedBlockCount q m z b) := by
  classical
  have h : (fun z : MarkedCloudSpace q A => markedBlockCount q m z b) =
      fun z : MarkedCloudSpace q A => (Finset.univ.filter
        (fun i : Fin z.1 => (fun l => blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l))
          = (fun l => (b l).val))).card := by
    funext z
    unfold markedBlockCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      funext l
      exact h l
    · intro h l
      exact congrFun h l
  rw [h]
  exact measurable_prefixCount_eq (fun z : MarkedCloudSpace q A => z.1) measurable_fst
    (fun i z => fun l => blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l))
    (fun i => measurable_pi_lambda _ (fun l =>
      (measurable_blockIndex _).comp ((measurable_pi_apply l).comp
        (((measurable_pi_apply i).comp measurable_snd).fst))))
    (fun l => (b l).val)

/-! ## The law of the encoded block counts -/

theorem iIndepFun_markedLabelCode (q m : ℕ) [NeZero m] {α : Measure A}
    [IsProbabilityMeasure α] (r : ℝ≥0) :
    iIndepFun (fun (i : ℕ) (z : MarkedCloudSpace q A) => markedLabelCode q m z i)
      (markedPoissonLaw (q := q) A α r) := by
  haveI : IsProbabilityMeasure (markedSeqLaw (q := q) A α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) A α
  haveI : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI hpair : IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := inferInstance
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => hpair
  have hseq : iIndepFun (fun (i : ℕ) (s : ℕ → (Fin q → ℝ) × A) =>
      blockLabelCode q m (s i).1) (markedSeqLaw (q := q) A α) := by
    rw [markedSeqLaw]
    exact iIndepFun_infinitePi_apply_comp ((cubeMeasure (Fin q) 1).prod α)
      (fun y => blockLabelCode q m y.1) ((measurable_blockLabelCode q m).comp measurable_fst)
  rw [markedPoissonLaw]
  exact iIndepFun_snd_prod
    (ν₁ := poissonMeasure r) (ν₂ := markedSeqLaw (q := q) A α)
    (Y := fun i s => blockLabelCode q m (s i).1)
    (fun i => (measurable_blockLabelCode q m).comp (measurable_pi_apply i |>.fst)) hseq

theorem iIndepFun_markedLabelCode_fin (q m : ℕ) [NeZero m] {α : Measure A}
    [IsProbabilityMeasure α] (r : ℝ≥0) (n : ℕ) :
    iIndepFun (fun (i : Fin n) (z : MarkedCloudSpace q A) => markedLabelCode q m z (i : ℕ))
      (markedPoissonLaw (q := q) A α r) :=
  (iIndepFun_markedLabelCode (q := q) (m := m) (α := α) r).precomp
    (g := fun i : Fin n => (i : ℕ)) (fun i j hij => Fin.ext hij)

theorem map_markedLabelCode_law (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (i : ℕ) :
    (markedPoissonLaw (q := q) A α r).map (fun z => markedLabelCode q m z i) =
      uniformMeasure (Fin (m ^ q)) := by
  haveI : IsProbabilityMeasure (markedSeqLaw (q := q) A α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) A α
  haveI : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI hpair : IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := inferInstance
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => hpair
  have hg : Measurable (fun y : (Fin q → ℝ) × A => blockLabelCode q m y.1) :=
    (measurable_blockLabelCode q m).comp measurable_fst
  have hgi : Measurable (Function.eval i : (ℕ → (Fin q → ℝ) × A) → (Fin q → ℝ) × A) :=
    measurable_pi_apply i
  have hseq : (markedSeqLaw (q := q) A α).map
      (fun s : ℕ → (Fin q → ℝ) × A => blockLabelCode q m (s i).1) =
      uniformMeasure (Fin (m ^ q)) := by
    rw [markedSeqLaw]
    rw [show (fun s : ℕ → (Fin q → ℝ) × A => blockLabelCode q m (s i).1) =
        (fun y : (Fin q → ℝ) × A => blockLabelCode q m y.1) ∘ Function.eval i from rfl,
      ← Measure.map_map hg hgi,
      Measure.infinitePi_map_eval]
    change Measure.map ((blockLabelCode q m) ∘ Prod.fst)
        ((cubeMeasure (Fin q) 1).prod α) = uniformMeasure (Fin (m ^ q))
    rw [← Measure.map_map (measurable_blockLabelCode q m) measurable_fst,
      Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    exact map_blockLabelCode_cubeMeasure q m hm
  have hgi' : Measurable (fun s : ℕ → (Fin q → ℝ) × A => blockLabelCode q m (s i).1) :=
    (measurable_blockLabelCode q m).comp ((measurable_pi_apply i).fst)
  rw [markedPoissonLaw]
  rw [show (fun z : MarkedCloudSpace q A => markedLabelCode q m z i) =
      (fun s : ℕ → (Fin q → ℝ) × A => blockLabelCode q m (s i).1) ∘ Prod.snd from rfl,
    ← Measure.map_map hgi' measurable_snd,
    Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact hseq

/-- The law of the vector of encoded block counts: independent Poisson coordinates
of rate `r / m^q`. -/
theorem markedBlockCountCode_law (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] :
    (markedPoissonLaw (q := q) A α r).map (markedBlockCountCode (A := A) q m) =
      Measure.pi (fun _ : Fin (m ^ q) => poissonMeasure (r / (m ^ q : ℝ≥0))) := by
  haveI : NeZero (m ^ q) := ⟨pow_ne_zero q (NeZero.ne m)⟩
  haveI : IsProbabilityMeasure (markedPoissonLaw (q := q) A α r) := inferInstance
  have hN : (markedPoissonLaw (q := q) A α r).map (fun z => z.1) = poissonMeasure r := by
    rw [markedPoissonLaw]
    show Measure.map Prod.fst ((poissonMeasure r).prod (markedSeqLaw (q := q) A α)) =
      poissonMeasure r
    rw [Measure.map_fst_prod]
    simp
  have hw : ∀ n, iIndepFun
      (fun i : Fin n => fun z : MarkedCloudSpace q A => markedLabelCode q m z (i : ℕ))
      (markedPoissonLaw (q := q) A α r) :=
    fun n => iIndepFun_markedLabelCode_fin (q := q) (m := m) (α := α) r n
  have hlaw : ∀ i, (markedPoissonLaw (q := q) A α r).map
      (fun z => markedLabelCode q m z i) = uniformMeasure (Fin (m ^ q)) :=
    fun i => map_markedLabelCode_law q m hm r α i
  have hindep : ∀ n, IndepFun (fun z : MarkedCloudSpace q A => z.1)
      (fun z => fun i : Fin n => markedLabelCode q m z (i : ℕ))
      (markedPoissonLaw (q := q) A α r) := by
    intro n
    have hvec : Measurable (fun s : ℕ → (Fin q → ℝ) × A => fun i : Fin n =>
        blockLabelCode q m (s i).1) :=
      measurable_pi_lambda (fun (s : ℕ → (Fin q → ℝ) × A) (i : Fin n) =>
        blockLabelCode q m (s i).1)
        (fun i => (measurable_blockLabelCode q m).comp
          ((measurable_pi_apply (i : ℕ)).fst))
    have h := indepFun_prod (μ := poissonMeasure r) (ν := markedSeqLaw (q := q) A α)
      measurable_id hvec
    have hP : (poissonMeasure r).prod (markedSeqLaw (q := q) A α) =
        markedPoissonLaw (q := q) A α r := rfl
    rw [hP] at h
    simpa only [Function.comp_def, id_eq, markedLabelCode] using h
  have h := map_poisson_label_counts (Λ := r) (N := fun z : MarkedCloudSpace q A => z.1)
    (w := fun i z => markedLabelCode q m z i) (K := m ^ q) hN hw hlaw hindep
  rw [show markedBlockCountCode (A := A) q m = fun z : MarkedCloudSpace q A =>
      fun b : Fin (m ^ q) =>
        (Finset.univ.filter (fun i : Fin z.1 => markedLabelCode q m z i = b)).card from rfl]
  rw [h]
  simp

theorem markedBlockCount_ae_eq_code (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] :
    ∀ᵐ z ∂(markedPoissonLaw (q := q) A α r), ∀ b : Fin q → Fin m,
      markedBlockCount q m z b = markedBlockCountCode q m z (finFunctionFinEquiv b) := by
  filter_upwards [ae_mem_unitCubeSet_markedPoissonLaw (q := q) α r] with z hz b
  unfold markedBlockCount markedBlockCountCode markedLabelCode
  congr 1
  apply Finset.filter_congr
  intro i _
  exact (blockLabelCode_eq_finFunctionFinEquiv_iff (m := m) (hz i) b).symm

/-- **The block count law.**  The vector of block counts of a marked Poisson cloud
of intensity `r` on the unit cube has independent Poisson coordinates of rate
`r / m^q`. -/
theorem markedBlockCount_law (q m : ℕ) (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] :
    (markedPoissonLaw (q := q) A α r).map (fun z => fun b : Fin q → Fin m =>
      markedBlockCount q m z b) =
      Measure.pi (fun _ : Fin q → Fin m => poissonMeasure (r / (m ^ q : ℝ≥0))) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (m ^ q) := ⟨pow_ne_zero q (NeZero.ne m)⟩
  have hmeas : Measurable (fun c : Fin (m ^ q) → ℕ =>
      fun b : Fin q → Fin m => c (finFunctionFinEquiv b)) :=
    measurable_of_countable _
  calc
    (markedPoissonLaw (q := q) A α r).map (fun z => fun b : Fin q → Fin m =>
        markedBlockCount q m z b)
        = (markedPoissonLaw (q := q) A α r).map
            (fun z => fun b : Fin q → Fin m => markedBlockCountCode q m z
              (finFunctionFinEquiv b)) := by
          apply Measure.map_congr
          filter_upwards [markedBlockCount_ae_eq_code q m hm r α] with z hz
          funext b
          exact hz b
    _ = ((markedPoissonLaw (q := q) A α r).map
          (markedBlockCountCode (A := A) q m)).map
            (fun c : Fin (m ^ q) → ℕ => fun b : Fin q → Fin m =>
              c (finFunctionFinEquiv b)) := by
          rw [Measure.map_map hmeas (measurable_markedBlockCountCode (A := A) q m)]
          rfl
    _ = (Measure.pi (fun _ : Fin (m ^ q) => poissonMeasure (r / (m ^ q : ℝ≥0)))).map
          (fun c : Fin (m ^ q) → ℕ => fun b : Fin q → Fin m =>
            c (finFunctionFinEquiv b)) := by
          rw [markedBlockCountCode_law q m hm r α]
    _ = Measure.pi (fun _ : Fin q → Fin m => poissonMeasure (r / (m ^ q : ℝ≥0))) := by
          have h := Measure.pi_map_piCongrLeft
            (e := (finFunctionFinEquiv (m := m) (n := q)).symm)
            (μ := fun _ : Fin q → Fin m => poissonMeasure (r / (m ^ q : ℝ≥0)))
          rw [show ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin q → Fin m => ℕ)
                (finFunctionFinEquiv (m := m) (n := q)).symm) =
              (fun c : Fin (m ^ q) → ℕ => fun b : Fin q → Fin m =>
                c (finFunctionFinEquiv b)) from ?_] at h
          · exact h
          · funext c b
            simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
              Equiv.symm_symm]
            simp

/-! ## The rescaled cloud of one block -/

/-- The local position of a point, dilated by `m` so that a block of side `m⁻¹`
becomes the unit cube. -/
def blockScaledLocalPoint (q m : ℕ) (x : Fin q → ℝ) : Fin q → ℝ :=
  fun l => (m : ℝ) * localCoord ((m : ℝ)⁻¹) (x l)

theorem measurable_blockScaledLocalPoint (q m : ℕ) :
    Measurable (blockScaledLocalPoint q m) :=
  measurable_pi_lambda _ fun l =>
    (measurable_const_mul (m : ℝ)).comp
      ((measurable_localCoord _).comp (measurable_pi_apply l))

/-- A marked point with its position replaced by the dilated local position. -/
def blockLocalMark (q m : ℕ) (y : (Fin q → ℝ) × A) : (Fin q → ℝ) × A :=
  (blockScaledLocalPoint q m y.1, y.2)

theorem measurable_blockLocalMark (q m : ℕ) :
    Measurable (blockLocalMark (A := A) q m) :=
  (measurable_blockScaledLocalPoint q m).comp measurable_fst |>.prodMk measurable_snd

/-- On the local cube, the local coordinate is the point itself, so the dilated
local point is the point rescaled by `m`. -/
theorem blockScaledLocalPoint_eq_mul {q m : ℕ} (hm : 0 < m) {x : Fin q → ℝ}
    (hx : ∀ l, x l ∈ Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹)) :
    blockScaledLocalPoint q m x = fun l => (m : ℝ) * x l := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  funext l
  have hx1 : x l < (m : ℝ)⁻¹ := (hx l).2
  have hdiv : x l / (m : ℝ)⁻¹ < 1 := by
    rw [div_inv_eq_mul]
    calc x l * (m : ℝ) < (m : ℝ)⁻¹ * (m : ℝ) := mul_lt_mul_of_pos_right hx1 hmpos
      _ = 1 := inv_mul_cancel₀ hmpos.ne'
  have hfloor : blockIndex ((m : ℝ)⁻¹) (x l) = 0 := by
    unfold blockIndex
    rw [Nat.floor_eq_zero]
    exact hdiv
  simp [blockScaledLocalPoint, localCoord, hfloor]

/-- Almost everywhere on the cube of side `L`, all coordinates lie in `(0, L)`. -/
theorem ae_mem_cubeMeasure_Ioo (q : ℕ) {L : ℝ} (hL : 0 < L) :
    ∀ᵐ x ∂(cubeMeasure (Fin q) L), ∀ l, x l ∈ Set.Ioo (0 : ℝ) L := by
  haveI hInt : IsProbabilityMeasure (uniformInterval L) :=
    isProbabilityMeasure_uniformInterval hL
  haveI : ∀ _ : Fin q, IsProbabilityMeasure (uniformInterval L) := fun _ => hInt
  have h : ∀ᵐ x ∂(Measure.pi (fun _ : Fin q => uniformInterval L)),
      ∀ l, x l ∈ Set.Ioo (0 : ℝ) L := by
    apply ae_all_iff.mpr
    intro l
    exact (measurePreserving_eval (μ := fun _ : Fin q => uniformInterval L) l)
      |>.quasiMeasurePreserving.ae (ae_mem_uniformInterval_Ioo (L := L))
  simpa only [cubeMeasure] using h

/-- Dilating the local position of a marked point by `m` turns the local cube law
into the unit-cube law. -/
theorem map_blockLocalMark_prod (q m : ℕ) (hm : 0 < m) (α : Measure A)
    [IsProbabilityMeasure α] :
    ((cubeMeasure (Fin q) ((m : ℝ)⁻¹)).prod α).map (blockLocalMark (A := A) q m) =
      (cubeMeasure (Fin q) 1).prod α := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure hL
  have hscaleMeas : Measurable (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l) :=
    measurable_pi_lambda _ (fun l => (measurable_const_mul (m : ℝ)).comp
      (measurable_pi_apply l))
  have hae : blockLocalMark (A := A) q m =ᵐ[
      ((cubeMeasure (Fin q) ((m : ℝ)⁻¹)).prod α)]
      Prod.map (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l) id := by
    have hcube := ae_mem_cubeMeasure_Ioo q hL
    have hfst : ∀ᵐ y ∂((cubeMeasure (Fin q) ((m : ℝ)⁻¹)).prod α),
        ∀ l, y.1 l ∈ Set.Ioo (0 : ℝ) ((m : ℝ)⁻¹) :=
      measurePreserving_fst.quasiMeasurePreserving.ae hcube
    filter_upwards [hfst] with y hy
    have hyl : blockScaledLocalPoint q m y.1 = fun l => (m : ℝ) * y.1 l :=
      blockScaledLocalPoint_eq_mul hm hy
    show blockLocalMark q m y =
      ((fun x : Fin q → ℝ => fun l => (m : ℝ) * x l) y.1, y.2)
    rw [show blockLocalMark q m y = (blockScaledLocalPoint q m y.1, y.2) from rfl, hyl]
  rw [Measure.map_congr hae, ← Measure.map_prod_map (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) α
    hscaleMeas measurable_id]
  rw [map_mul_cubeMeasure q m hm, Measure.map_id]

/-- The encoded block label is independent of the dilated local position of a
uniform cube point, and the dilated local position is uniform on the unit cube. -/
theorem map_blockLabelCode_scaledLocal_cubeMeasure (q m : ℕ) [NeZero m] (hm : 0 < m) :
    (cubeMeasure (Fin q) 1).map
        (fun x : Fin q → ℝ => (blockLabelCode q m x, blockScaledLocalPoint q m x)) =
      (uniformMeasure (Fin (m ^ q))).prod (cubeMeasure (Fin q) 1) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure hL
  have hjoint := map_blockLabelCode_local_cubeMeasure q m hm
  have hscale : (fun x : Fin q → ℝ =>
        (blockLabelCode q m x, blockScaledLocalPoint q m x)) =
      (Prod.map id (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l)) ∘
        (fun x : Fin q → ℝ => (blockLabelCode q m x, blockLocalPoint q m x)) := rfl
  have hscaleMeas : Measurable (fun x : Fin q → ℝ => fun l => (m : ℝ) * x l) :=
    measurable_pi_lambda _ (fun l => (measurable_const_mul (m : ℝ)).comp
      (measurable_pi_apply l))
  rw [hscale, ← Measure.map_map (measurable_id.prodMap hscaleMeas)
    ((measurable_blockLabelCode q m).prod (measurable_blockLocalPoint q m)),
    hjoint,
    ← Measure.map_prod_map (uniformMeasure (Fin (m ^ q)))
      (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) measurable_id hscaleMeas,
    Measure.map_id, map_mul_cubeMeasure q m hm]

/-- The dilated local position of a uniform point on the unit cube is again
uniform on the unit cube (it is the local coordinate inside a random block). -/
theorem map_blockScaledLocalPoint_cubeMeasure (q m : ℕ) [NeZero m] (hm : 0 < m) :
    (cubeMeasure (Fin q) 1).map (blockScaledLocalPoint q m) = cubeMeasure (Fin q) 1 := by
  haveI : NeZero (m ^ q) := ⟨pow_ne_zero q (NeZero.ne m)⟩
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := map_blockLabelCode_scaledLocal_cubeMeasure q m hm
  have hmap : ((cubeMeasure (Fin q) 1).map (fun x : Fin q → ℝ =>
      (blockLabelCode q m x, blockScaledLocalPoint q m x))).map Prod.snd =
      (cubeMeasure (Fin q) 1).map (blockScaledLocalPoint q m) := by
    rw [Measure.map_map measurable_snd
      ((measurable_blockLabelCode q m).prod (measurable_blockScaledLocalPoint q m))]
    rfl
  rw [h] at hmap
  rw [Measure.map_snd_prod] at hmap
  simp only [measure_univ, one_smul] at hmap
  exact hmap.symm

/-- The scaled local marked point of a uniform cube point is again uniform. -/
theorem map_blockLocalMark_unit (q m : ℕ) [NeZero m] (hm : 0 < m)
    (α : Measure A) [IsProbabilityMeasure α] :
    ((cubeMeasure (Fin q) 1).prod α).map (blockLocalMark (A := A) q m) =
      (cubeMeasure (Fin q) 1).prod α := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have hscaled := map_blockScaledLocalPoint_cubeMeasure q m hm
  have h : blockLocalMark (A := A) q m = Prod.map (blockScaledLocalPoint q m) id := rfl
  rw [h, ← Measure.map_prod_map (cubeMeasure (Fin q) 1) α
    (measurable_blockScaledLocalPoint q m) measurable_id, hscaled, Measure.map_id]

/-- The one-point block law with the dilated local position. -/
def markedBlockOnePointScaled (q m : ℕ) [NeZero m] (y : (Fin q → ℝ) × A) :
    Fin (m ^ q) × ((Fin q → ℝ) × A) :=
  (blockLabelCode q m y.1, blockLocalMark q m y)

theorem measurable_markedBlockOnePointScaled (q m : ℕ) [NeZero m] :
    Measurable (markedBlockOnePointScaled (A := A) q m) :=
  ((measurable_blockLabelCode q m).comp measurable_fst).prodMk
    (measurable_blockLocalMark q m)

theorem map_markedBlockOnePointScaled (q m : ℕ) [NeZero m] (hm : 0 < m)
    (α : Measure A) [IsProbabilityMeasure α] :
    ((cubeMeasure (Fin q) 1).prod α).map (markedBlockOnePointScaled (A := A) q m) =
      (uniformMeasure (Fin (m ^ q))).prod ((cubeMeasure (Fin q) 1).prod α) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure hL
  have hlabel := map_blockLabelCode_scaledLocal_cubeMeasure q m hm
  have hcomp : (markedBlockOnePointScaled (A := A) q m) =
      (MeasurableEquiv.prodAssoc) ∘
        (Prod.map (fun x : Fin q → ℝ =>
          (blockLabelCode q m x, blockScaledLocalPoint q m x)) id) := by
    funext p
    rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable
    (((measurable_blockLabelCode q m).prod (measurable_blockScaledLocalPoint q m)).prodMap
      measurable_id)]
  rw [← Measure.map_prod_map (cubeMeasure (Fin q) 1) α
    ((measurable_blockLabelCode q m).prod (measurable_blockScaledLocalPoint q m))
    measurable_id]
  rw [hlabel, Measure.map_id]
  exact Measure.prodAssoc_prod

/-- The cloud of the points of `z` lying in the block `b`, with the block dilated
to the unit cube; it is encoded as block data with its own number of points.

Concretely, this is the sub-cloud of the points whose encoded block label is the
label of `b`, enumerated in the order of their positions, with the local
coordinates dilated by `m`.  It is almost everywhere equal to the cloud obtained
by filtering the points with the raw block-index predicate
`∀ l, ⌊m x l⌋ = (b l).val`, since the two labels agree on the unit cube. -/
noncomputable def blockLocalCloudEncoded (q m : ℕ) [NeZero m] (b : Fin q → Fin m)
    (z : MarkedCloudSpace q A) : BlockData ((Fin q → ℝ) × A) :=
  prefixBlockData (fun z : MarkedCloudSpace q A => z.1)
    (fun i z => markedLabelCode q m z i)
    (fun i z => blockLocalMark (A := A) q m (z.2 i))
    (finFunctionFinEquiv b) z

/-- The same block cloud written with the raw block-index predicate.  It agrees
with `blockLocalCloudEncoded` almost everywhere but requires no label encoding. -/
noncomputable def blockLocalCloud (q m : ℕ) (b : Fin q → Fin m)
    (z : MarkedCloudSpace q A) : BlockData ((Fin q → ℝ) × A) :=
  let s := Finset.univ.filter (fun i : Fin z.1 =>
    ∀ l, blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l) = (b l).val)
  ⟨s.card, fun j =>
    let i := (s.orderIsoOfFin rfl j).1
    (fun l => (m : ℝ) * localCoord ((m : ℝ)⁻¹) ((z.2 i).1 l), (z.2 i).2)⟩

/-! ## The Poisson cloud of one block -/

/-- The original independently counted iid prefix has its exact finite
block-data law for any original count distribution. -/
theorem blockDataLaw_eq_map_count_cloud {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (κ : Measure ℕ) [IsProbabilityMeasure κ] :
    blockDataLaw ν (fun n => κ {n}) =
      (κ.prod (Measure.infinitePi (fun _ : ℕ => ν))).map
        (fun z : ℕ × (ℕ → Pos) =>
          (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData Pos)) := by
  classical
  let F : ℕ × (ℕ → Pos) → BlockData Pos :=
    fun z => ⟨z.1, fun j : Fin z.1 => z.2 j⟩
  have hF : Measurable F := by
    intro S hS
    have hpre : F ⁻¹' S = ⋃ n : ℕ, (Prod.fst ⁻¹' {n}) ∩
        (Prod.snd ⁻¹' ((fun y : ℕ → Pos =>
          (⟨n, fun j : Fin n => y j⟩ : BlockData Pos)) ⁻¹' S)) := by
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
    have hcompMeas : ∀ n, Measurable (fun y : ℕ → Pos =>
        (⟨n, fun j : Fin n => y j⟩ : BlockData Pos)) := by
      intro n
      exact (measurable_sigma_mk n).comp
        (measurable_pi_lambda (fun (y : ℕ → Pos) (j : Fin n) => y j)
          (fun j => measurable_pi_apply (j : ℕ)))
    rw [hpre]
    exact MeasurableSet.iUnion fun n => MeasurableSet.inter
      (measurable_fst (measurableSet_singleton n))
      (measurable_snd ((hcompMeas n) hS))
  have hsum : κ.prod (Measure.infinitePi (fun _ : ℕ => ν)) =
      Measure.sum (fun n => κ {n} •
        ((Measure.dirac n).prod (Measure.infinitePi (fun _ : ℕ => ν)))) := by
    conv_lhs => rw [show κ =
      Measure.sum (fun n => κ {n} • Measure.dirac n) from
        (Measure.sum_smul_dirac _).symm]
    rw [Measure.prod_sum_left]
    congr 1
    funext n
    rw [Measure.prod_smul_left]
  rw [hsum, Measure.map_sum hF.aemeasurable, blockDataLaw]
  apply Measure.sum_congr
  intro n
  rw [Measure.map_smul]
  congr 1
  have hterm : ((Measure.dirac n).prod (Measure.infinitePi (fun _ : ℕ => ν))).map F =
      (Measure.pi (fun _ : Fin n => ν)).map
        (fun y : Fin n → Pos => (⟨n, y⟩ : BlockData Pos)) := by
    rw [Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
    have hcomp : F ∘ Prod.mk n =
        (fun y : Fin n → Pos => (⟨n, y⟩ : BlockData Pos)) ∘
          (fun y : ℕ → Pos => fun j : Fin n => y j) := rfl
    have hsig : Measurable (fun y : Fin n → Pos => (⟨n, y⟩ : BlockData Pos)) :=
      measurable_sigma_mk n
    have hres : Measurable (fun y : ℕ → Pos => fun j : Fin n => y j) :=
      measurable_pi_lambda (fun (y : ℕ → Pos) (j : Fin n) => y j)
        (fun j => measurable_pi_apply (j : ℕ))
    rw [hcomp, ← Measure.map_map hsig hres, infinitePi_map_fin ν n]
  exact hterm.symm

/-- The Poisson specialization of the original counted iid prefix law. -/
theorem blockDataLaw_eq_map_cloud {Pos : Type*} [MeasurableSpace Pos]
    (ν : Measure Pos) [IsProbabilityMeasure ν] (c : ℝ≥0) :
    blockDataLaw ν (fun n => poissonMeasure c {n}) =
      ((poissonMeasure c).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
        (fun z : ℕ × (ℕ → Pos) =>
          (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData Pos)) := by
  exact blockDataLaw_eq_map_count_cloud ν (poissonMeasure c)

/-! ## Independence of the scaled one-point map -/

theorem iIndepFun_markedBlockOnePointScaled (q m : ℕ) [NeZero m] {α : Measure A}
    [IsProbabilityMeasure α] (r : ℝ≥0) :
    iIndepFun (fun (i : ℕ) (z : MarkedCloudSpace q A) =>
      markedBlockOnePointScaled (A := A) q m (z.2 i)) (markedPoissonLaw (q := q) A α r) := by
  haveI : IsProbabilityMeasure (markedSeqLaw (q := q) A α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) A α
  haveI : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI hpair : IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := inferInstance
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := fun _ => hpair
  have hseq : iIndepFun (fun (i : ℕ) (s : ℕ → (Fin q → ℝ) × A) =>
      markedBlockOnePointScaled q m (s i)) (markedSeqLaw (q := q) A α) := by
    rw [markedSeqLaw]
    exact iIndepFun_infinitePi_apply_comp ((cubeMeasure (Fin q) 1).prod α)
      (markedBlockOnePointScaled q m) (measurable_markedBlockOnePointScaled q m)
  rw [markedPoissonLaw]
  exact iIndepFun_snd_prod (ν₁ := poissonMeasure r) (ν₂ := markedSeqLaw (q := q) A α)
    (Y := fun i s => markedBlockOnePointScaled q m (s i))
    (fun i => (measurable_markedBlockOnePointScaled q m).comp (measurable_pi_apply i)) hseq

theorem iIndepFun_markedBlockOnePointScaled_fin (q m : ℕ) [NeZero m] {α : Measure A}
    [IsProbabilityMeasure α] (r : ℝ≥0) (n : ℕ) :
    iIndepFun (fun (i : Fin n) (z : MarkedCloudSpace q A) =>
      markedBlockOnePointScaled (A := A) q m (z.2 i)) (markedPoissonLaw (q := q) A α r) :=
  (iIndepFun_markedBlockOnePointScaled (q := q) (m := m) (α := α) r).precomp
    (g := fun i : Fin n => (i : ℕ)) (fun i j hij => Fin.ext hij)

theorem map_markedBlockOnePointScaled_law (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (i : ℕ) :
    (markedPoissonLaw (q := q) A α r).map
        (fun z => markedBlockOnePointScaled (A := A) q m (z.2 i)) =
      (uniformMeasure (Fin (m ^ q))).prod ((cubeMeasure (Fin q) 1).prod α) := by
  haveI : IsProbabilityMeasure (markedSeqLaw (q := q) A α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) A α
  haveI : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI hpair : IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := inferInstance
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := fun _ => hpair
  have hg : Measurable (fun s : ℕ → (Fin q → ℝ) × A =>
      markedBlockOnePointScaled (A := A) q m (s i)) :=
    (measurable_markedBlockOnePointScaled q m).comp (measurable_pi_apply i)
  have hseq : (markedSeqLaw (q := q) A α).map
      (fun s : ℕ → (Fin q → ℝ) × A => markedBlockOnePointScaled q m (s i)) =
      (uniformMeasure (Fin (m ^ q))).prod ((cubeMeasure (Fin q) 1).prod α) := by
    rw [markedSeqLaw]
    rw [show (fun s : ℕ → (Fin q → ℝ) × A => markedBlockOnePointScaled q m (s i)) =
        markedBlockOnePointScaled q m ∘ Function.eval i from rfl,
      ← Measure.map_map (measurable_markedBlockOnePointScaled q m) (measurable_pi_apply i),
      Measure.infinitePi_map_eval]
    exact map_markedBlockOnePointScaled q m hm α
  rw [markedPoissonLaw]
  rw [show (fun z : MarkedCloudSpace q A => markedBlockOnePointScaled q m (z.2 i)) =
      (fun s : ℕ → (Fin q → ℝ) × A => markedBlockOnePointScaled q m (s i)) ∘ Prod.snd
      from rfl,
    ← Measure.map_map hg measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact hseq

theorem map_blockLocalMark_law (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (i : ℕ) :
    (markedPoissonLaw (q := q) A α r).map
        (fun z => blockLocalMark (A := A) q m (z.2 i)) =
      (cubeMeasure (Fin q) 1).prod α := by
  haveI : IsProbabilityMeasure (markedSeqLaw (q := q) A α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) A α
  haveI : IsProbabilityMeasure (poissonMeasure r) := inferInstance
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI hpair : IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := inferInstance
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) := fun _ => hpair
  have hg : Measurable (fun s : ℕ → (Fin q → ℝ) × A =>
      blockLocalMark (A := A) q m (s i)) :=
    (measurable_blockLocalMark q m).comp (measurable_pi_apply i)
  have hseq : (markedSeqLaw (q := q) A α).map
      (fun s : ℕ → (Fin q → ℝ) × A => blockLocalMark q m (s i)) =
      (cubeMeasure (Fin q) 1).prod α := by
    rw [markedSeqLaw]
    rw [show (fun s : ℕ → (Fin q → ℝ) × A => blockLocalMark q m (s i)) =
        blockLocalMark q m ∘ Function.eval i from rfl,
      ← Measure.map_map (measurable_blockLocalMark q m) (measurable_pi_apply i),
      Measure.infinitePi_map_eval]
    exact map_blockLocalMark_unit q m hm α
  rw [markedPoissonLaw]
  rw [show (fun z : MarkedCloudSpace q A => blockLocalMark q m (z.2 i)) =
      (fun s : ℕ → (Fin q → ℝ) × A => blockLocalMark q m (s i)) ∘ Prod.snd from rfl,
    ← Measure.map_map hg measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact hseq

/-- **The per-block rescaled cloud law.**  For a marked Poisson cloud of intensity
`r` on the unit cube, the points of one block, dilated back to the unit cube, form
a marked Poisson cloud of intensity `r / m^q`, encoded as block data. -/
theorem blockLocalCloudEncoded_law (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (b : Fin q → Fin m) :
    (markedPoissonLaw (q := q) A α r).map (blockLocalCloudEncoded (A := A) q m b) =
      blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
        (fun n => poissonMeasure (r / (m ^ q : ℝ≥0)) {n}) := by
  haveI : NeZero (m ^ q) := ⟨pow_ne_zero q (NeZero.ne m)⟩
  haveI : IsProbabilityMeasure (markedPoissonLaw (q := q) A α r) := inferInstance
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI hL : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hm)
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) ((m : ℝ)⁻¹)) :=
    isProbabilityMeasure_cubeMeasure hL
  have hN : (markedPoissonLaw (q := q) A α r).map (fun z => z.1) = poissonMeasure r := by
    rw [markedPoissonLaw]
    show Measure.map Prod.fst ((poissonMeasure r).prod (markedSeqLaw (q := q) A α)) =
      poissonMeasure r
    rw [Measure.map_fst_prod]
    simp
  have hpair : ∀ n, iIndepFun (fun i : Fin n => fun z : MarkedCloudSpace q A =>
      (markedLabelCode q m z i, blockLocalMark (A := A) q m (z.2 i)))
      (markedPoissonLaw (q := q) A α r) := by
    intro n
    have h := iIndepFun_markedBlockOnePointScaled_fin (q := q) (m := m) (α := α) r n
    simpa only [markedBlockOnePointScaled, markedLabelCode] using h
  have hw : ∀ i, Measurable (fun z : MarkedCloudSpace q A => markedLabelCode q m z i) :=
    fun i => measurable_markedLabelCode q m i
  have hx : ∀ i, Measurable (fun z : MarkedCloudSpace q A =>
      blockLocalMark (A := A) q m (z.2 i)) :=
    fun i => (measurable_blockLocalMark q m).comp ((measurable_pi_apply i).comp measurable_snd)
  have hlaw_w : ∀ i, (markedPoissonLaw (q := q) A α r).map
      (fun z => markedLabelCode q m z i) = uniformMeasure (Fin (m ^ q)) :=
    fun i => map_markedLabelCode_law q m hm r α i
  have hlaw_x : ∀ i, (markedPoissonLaw (q := q) A α r).map
      (fun z => blockLocalMark (A := A) q m (z.2 i)) =
      (cubeMeasure (Fin q) 1).prod α :=
    fun i => map_blockLocalMark_law q m hm r α i
  have hindep_wx : ∀ i, IndepFun (fun z : MarkedCloudSpace q A => markedLabelCode q m z i)
      (fun z => blockLocalMark (A := A) q m (z.2 i))
      (markedPoissonLaw (q := q) A α r) := by
    intro i
    have hxmeas : Measurable (fun z : MarkedCloudSpace q A =>
        blockLocalMark (A := A) q m (z.2 i)) :=
      (measurable_blockLocalMark q m).comp ((measurable_pi_apply i).comp measurable_snd)
    refine (indepFun_iff_map_prod_eq_prod_map_map
      (f := fun z : MarkedCloudSpace q A => markedLabelCode q m z i)
      (g := fun z => blockLocalMark (A := A) q m (z.2 i))
      (measurable_markedLabelCode q m i).aemeasurable hxmeas.aemeasurable).mpr ?_
    rw [hlaw_w i, hlaw_x i]
    have h := map_markedBlockOnePointScaled_law (q := q) (m := m) (A := A) hm r α i
    have hfun : (fun z : MarkedCloudSpace q A =>
        (markedLabelCode q m z i, blockLocalMark q m (z.2 i))) =
        fun z => markedBlockOnePointScaled q m (z.2 i) := rfl
    rw [hfun]
    exact h
  have hindep : ∀ n, IndepFun (fun z : MarkedCloudSpace q A => z.1)
      (fun z => fun i : Fin n =>
        (markedLabelCode q m z i, blockLocalMark (A := A) q m (z.2 i)))
      (markedPoissonLaw (q := q) A α r) := by
    intro n
    have hvec : Measurable (fun s : ℕ → (Fin q → ℝ) × A => fun i : Fin n =>
        markedBlockOnePointScaled q m (s i)) :=
      measurable_pi_lambda (fun (s : ℕ → (Fin q → ℝ) × A) (i : Fin n) =>
        markedBlockOnePointScaled q m (s i))
        (fun i => (measurable_markedBlockOnePointScaled q m).comp
          (measurable_pi_apply (i : ℕ)))
    have h := indepFun_prod (μ := poissonMeasure r) (ν := markedSeqLaw (q := q) A α)
      measurable_id hvec
    have hP : (poissonMeasure r).prod (markedSeqLaw (q := q) A α) =
        markedPoissonLaw (q := q) A α r := rfl
    rw [hP] at h
    simpa only [Function.comp_def, id_eq, markedBlockOnePointScaled, markedLabelCode] using h
  have h := map_poisson_blockData (Λ := r) (N := fun z : MarkedCloudSpace q A => z.1)
    (w := fun i z => markedLabelCode q m z i)
    (x := fun i z => blockLocalMark (A := A) q m (z.2 i))
    (ν := (cubeMeasure (Fin q) 1).prod α)
    hN hpair hw hx hlaw_w hlaw_x hindep_wx hindep (finFunctionFinEquiv b)
  rw [show (Fintype.card (Fin (m ^ q)) : ℝ≥0) = (m ^ q : ℝ≥0) from by simp] at h
  unfold blockLocalCloudEncoded
  exact h

/-- The per-block rescaled cloud law, in the marked-cloud form: the law of the
block cloud is the pushforward of the intensity-`r/m^q` cloud under the encoding
of a cloud as block data. -/
theorem blockLocalCloudEncoded_law' (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (b : Fin q → Fin m) :
    (markedPoissonLaw (q := q) A α r).map (blockLocalCloudEncoded (A := A) q m b) =
      (markedPoissonLaw (q := q) A α (r / (m ^ q : ℝ≥0))).map
        (fun z : MarkedCloudSpace q A =>
          (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData ((Fin q → ℝ) × A))) := by
  rw [blockLocalCloudEncoded_law q m hm r α b]
  exact blockDataLaw_eq_map_cloud ((cubeMeasure (Fin q) 1).prod α)
    (r / (m ^ q : ℝ≥0))

/-! ## The two-colour block counts -/

/-- **The two-colour block count law.**  The vector of the pairs of block counts
of two independent marked Poisson clouds has, in every block, independent Poisson
coordinates of rate `r / m^q` for each colour. -/
theorem twoMarkedBlockCount_law (q m : ℕ) (hm : 0 < m) (r : ℝ≥0)
    {B : Type*} [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] :
    (twoMarkedCloudLaw (q := q) A B α β r).map (fun ω => fun b : Fin q → Fin m =>
      (markedBlockCount q m ω.1 b, markedBlockCount q m ω.2 b)) =
      Measure.pi (fun _ : Fin q → Fin m =>
        (poissonMeasure (r / (m ^ q : ℝ≥0))).prod
          (poissonMeasure (r / (m ^ q : ℝ≥0)))) := by
  haveI : IsProbabilityMeasure (markedPoissonLaw (q := q) A α r) := inferInstance
  haveI : IsProbabilityMeasure (markedPoissonLaw (q := q) B β r) := inferInstance
  have h1 := markedBlockCount_law (q := q) (m := m) (A := A) hm r α
  have h2 := markedBlockCount_law (q := q) (m := m) (A := B) hm r β
  have hmeas1 : Measurable (fun z : MarkedCloudSpace q A => fun b : Fin q → Fin m =>
      markedBlockCount q m z b) := by
    rw [measurable_pi_iff]
    intro b
    exact measurable_markedBlockCount q m b
  have hmeas2 : Measurable (fun z : MarkedCloudSpace q B => fun b : Fin q → Fin m =>
      markedBlockCount q m z b) := by
    rw [measurable_pi_iff]
    intro b
    exact measurable_markedBlockCount q m b
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ (Fin q → Fin m)
  have hmap : (fun ω : TwoMarkedCloudSpace q A B => fun b : Fin q → Fin m =>
      (markedBlockCount q m ω.1 b, markedBlockCount q m ω.2 b)) =
      e.symm ∘ Prod.map
        (fun z : MarkedCloudSpace q A => fun b => markedBlockCount q m z b)
        (fun z : MarkedCloudSpace q B => fun b => markedBlockCount q m z b) := by
    funext ω b
    rfl
  rw [hmap, ← Measure.map_map e.symm.measurable (hmeas1.prodMap hmeas2)]
  rw [twoMarkedCloudLaw]
  rw [← Measure.map_prod_map (markedPoissonLaw (q := q) A α r)
    (markedPoissonLaw (q := q) B β r) hmeas1 hmeas2]
  rw [h1, h2]
  let c : ℝ≥0 := r / (m ^ q : ℝ≥0)
  have hpres := measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin q → Fin m)
    (fun _ : Fin q → Fin m => poissonMeasure c)
    (fun _ : Fin q → Fin m => poissonMeasure c)
  rw [← hpres.map_eq, Measure.map_map e.symm.measurable e.measurable]
  have hid : e.symm ∘ e = id := by
    funext x
    exact e.symm_apply_apply x
  rw [hid, Measure.map_id]


/-- Two sigma-encoded enumerations of equal finsets coincide. -/
lemma sigma_orderIsoOfFin_congr {α β : Type*} [LinearOrder α]
    {s t : Finset α} (h : s = t) (f : α → β) :
    (⟨s.card, fun j : Fin s.card => f ((s.orderIsoOfFin rfl j).1)⟩ : Σ n, Fin n → β) =
      (⟨t.card, fun j : Fin t.card => f ((t.orderIsoOfFin rfl j).1)⟩ : Σ n, Fin n → β) := by
  subst h
  rfl

/-- The raw block cloud and the encoded block cloud agree almost everywhere: on
the unit cube the raw block-index predicate is equivalent to the encoded label. -/
theorem blockLocalCloud_ae_eq_encoded (q m : ℕ) [NeZero m] (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (b : Fin q → Fin m) :
    ∀ᵐ z ∂(markedPoissonLaw (q := q) A α r),
      blockLocalCloud (A := A) q m b z = blockLocalCloudEncoded (A := A) q m b z := by
  filter_upwards [ae_mem_unitCubeSet_markedPoissonLaw (q := q) α r] with z hz
  classical
  have hfil : (Finset.univ.filter (fun i : Fin z.1 =>
      ∀ l, blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l) = (b l).val)) =
      Finset.univ.filter (fun i : Fin z.1 =>
        markedLabelCode q m z i = finFunctionFinEquiv b) := by
    apply Finset.filter_congr
    intro i _
    exact (blockLabelCode_eq_finFunctionFinEquiv_iff (m := m) (hz i) b).symm
  unfold blockLocalCloud blockLocalCloudEncoded prefixBlockData
  exact sigma_orderIsoOfFin_congr hfil
    (fun i => (fun l => (m : ℝ) * localCoord ((m : ℝ)⁻¹) ((z.2 i).1 l), (z.2 i).2))

/-- **The per-block rescaled cloud law, raw form.**  The cloud obtained by
filtering the points of the block `b` with the raw block-index predicate and
dilating the block to the unit cube has the law of an intensity-`r / m^q` marked
Poisson cloud. -/
theorem blockLocalCloud_law (q m : ℕ) (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (b : Fin q → Fin m) :
    (markedPoissonLaw (q := q) A α r).map (blockLocalCloud (A := A) q m b) =
      blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
        (fun n => poissonMeasure (r / (m ^ q : ℝ≥0)) {n}) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [← blockLocalCloudEncoded_law q m hm r α b]
  exact Measure.map_congr (blockLocalCloud_ae_eq_encoded q m hm r α b)

/-- **The per-block rescaled cloud law, raw marked-cloud form.**  The raw block
cloud of an intensity-`r` marked Poisson cloud is distributed as the pushforward
of the intensity-`r / m^q` marked Poisson cloud under the encoding of a cloud as
block data. -/
theorem blockLocalCloud_law' (q m : ℕ) (hm : 0 < m) (r : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α] (b : Fin q → Fin m) :
    (markedPoissonLaw (q := q) A α r).map (blockLocalCloud (A := A) q m b) =
      (markedPoissonLaw (q := q) A α (r / (m ^ q : ℝ≥0))).map
        (fun z : MarkedCloudSpace q A =>
          (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData ((Fin q → ℝ) × A))) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [← blockLocalCloudEncoded_law' q m hm r α b]
  exact Measure.map_congr (blockLocalCloud_ae_eq_encoded q m hm r α b)

end OTSelector.Probability
