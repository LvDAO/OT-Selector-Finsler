import OTSelector.Finite.MaxCardValueStability
import OTSelector.Probability.MarkedBlockLaw
import OTSelector.Probability.MarkedGridBlockComparison
import OTSelector.Finite.MatchingTranspose
import OTSelector.Probability.CloudValueMeasurable

/-!
# Expected leaf-block value of the marked Poisson cloud

The marked Poisson cloud of intensity `R` on the unit cube is tiled by the
`m ^ q` equal blocks of the uniform grid hierarchy.  This file proves that the
expected sum of the optimal leaf-block matching values equals `m ^ q` times the
marked pressure at the per-block intensity `R / m ^ q`.

The proof has four steps:

* padded leaf labels with a coordinate at least `m` carry an empty block and
  therefore have value zero, so the sum over the padded label type
  `Fin q → Fin (2 ^ J + 1)` is the sum over the real blocks `Fin q → Fin m`;
* on each real block, the ambient block matrix is a reindexing of the local
  matrix of the rescaled block cloud, and the kinetic edge coefficients agree
  because the displacement scales by `m` and the kernel is quadratically
  homogeneous;
* the rescaled block cloud has law the marked Poisson cloud of intensity
  `R / m ^ q`, so each block contributes the marked pressure at that intensity;
* the `m ^ q` blocks are exchangeable, so the expected sum is `m ^ q` times the
  single-block pressure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## Leaf labels of the padded grid -/

/-- The leaf label of a real block `b : Fin q → Fin m`, padded to the label
type `Fin q → Fin (2 ^ J + 1)` of the level-`J` grid. -/
def blockLeafLabel (q m J : ℕ) (hJ : m ≤ 2 ^ J) (b : Fin q → Fin m) :
    Fin q → Fin (2 ^ J + 1) :=
  fun l => ⟨(b l).val, Nat.lt_succ_of_lt (lt_of_lt_of_le (b l).isLt hJ)⟩

@[simp] theorem blockLeafLabel_val (q m J : ℕ) (hJ : m ≤ 2 ^ J)
    (b : Fin q → Fin m) (l : Fin q) :
    (blockLeafLabel q m J hJ b l).val = (b l).val := rfl

theorem blockLeafLabel_lt (q m J : ℕ) (hJ : m ≤ 2 ^ J)
    (b : Fin q → Fin m) (l : Fin q) :
    (blockLeafLabel q m J hJ b l).val < m := (b l).isLt

theorem blockLeafLabel_injective (q m J : ℕ) (hJ : m ≤ 2 ^ J) :
    Function.Injective (blockLeafLabel q m J hJ) := by
  intro b c h
  funext l
  apply Fin.ext
  have := congrArg (fun f : Fin q → Fin (2 ^ J + 1) => (f l).val) h
  simpa only [blockLeafLabel_val] using this

/-- On the unit cube, the level-`J` grid label of a point is its leaf block
index.  The level-`J` divisor is `2 ^ (J - J) = 1`. -/
theorem gridCellLabel_leaf_apply {m J : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    {x : Fin q → ℝ} (hx : x ∈ unitCubeSet q) (l : Fin q) :
    (gridCellLabel q m J J hm hJ x l).val = blockIndex ((m : ℝ)⁻¹) (x l) := by
  have hxl : 0 ≤ x l ∧ x l < 1 := by
    have hxl' : x l ∈ Set.Ioo (0 : ℝ) 1 := by
      have := hx
      simp only [unitCubeSet, Set.mem_pi, Set.mem_univ, true_implies] at this
      exact this l
    exact ⟨le_of_lt hxl'.1, hxl'.2⟩
  have hval := gridLeaf_val_of_mem hm hxl.1 hxl.2
  simp only [gridCellLabel, Nat.sub_self, pow_zero, Nat.div_one, hval]
  unfold blockIndex
  rw [div_inv_eq_mul, mul_comm]

/-- The level-`J` grid label of a unit-cube point equals a padded block label
exactly when the point lies in that block. -/
theorem gridCellLabel_leaf_eq_iff {m J : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    {x : Fin q → ℝ} (hx : x ∈ unitCubeSet q) (b : Fin q → Fin m) :
    gridCellLabel q m J J hm hJ x = blockLeafLabel q m J hJ b ↔
      ∀ l, blockIndex ((m : ℝ)⁻¹) (x l) = (b l).val := by
  constructor
  · intro h l
    have hv := congrArg (fun f : Fin q → Fin (2 ^ J + 1) => (f l).val) h
    rw [gridCellLabel_leaf_apply hm hJ hx l, blockLeafLabel_val] at hv
    exact hv
  · intro h
    funext l
    apply Fin.ext
    rw [gridCellLabel_leaf_apply hm hJ hx l, blockLeafLabel_val]
    exact h l

/-- The same characterization with the truncated point used by the block cost. -/
theorem gridCellLabel_trunc_eq_iff {m J : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    {x : Fin q → ℝ} (hx : x ∈ unitCubeSet q) (b : Fin q → Fin m) :
    gridCellLabel q m J J hm hJ (cubeTruncPoint x) = blockLeafLabel q m J hJ b ↔
      ∀ l, blockIndex ((m : ℝ)⁻¹) (x l) = (b l).val := by
  rw [cubeTruncPoint_eq_of_mem hx]
  exact gridCellLabel_leaf_eq_iff hm hJ hx b

/-- A padded label that is not a real block label carries no point of the leaf
grid: at level `J` every leaf index is below `m`. -/
theorem gridCellLabel_leaf_val_lt {m J : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (x : Fin q → ℝ) (l : Fin q) :
    (gridCellLabel q m J J hm hJ x l).val < m := by
  simp only [gridCellLabel, Nat.sub_self, pow_zero, Nat.div_one]
  exact (gridLeaf m hm (x l)).isLt

/-! ## The ambient leaf-block value -/

/-- The optimal value of the leaf block with padded label `c`. -/
noncomputable def markedBlockValue (q m J : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (r t : ℝ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) (c : Fin q → Fin (2 ^ J + 1)) : ℝ :=
  PartialMatching.maxCardValue
    (blockCost
      (fun i : Fin (mSourceCount ω) =>
        gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
      (fun j : Fin (mTargetCount ω) =>
        gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
      (fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) c)

/-- A padded label with a coordinate at least `m` selects no source point, so its
block matrix has no rows and its optimal value is zero. -/
theorem markedBlockValue_eq_zero_of_not_forall_lt {q m J : ℕ} (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (r t : ℝ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (ω : TwoMarkedCloudSpace q A B) (c : Fin q → Fin (2 ^ J + 1))
    (hc : ¬ ∀ l, (c l).val < m) :
    markedBlockValue q m J hm hJ r t kin g ω c = 0 := by
  classical
  have hex : ∃ l, m ≤ (c l).val := by
    by_contra h
    push_neg at h
    exact hc h
  obtain ⟨l0, hl0⟩ := hex
  have hempty : blockSizeS
      (fun i : Fin (mSourceCount ω) =>
        gridCellLabel q m J J hm hJ (markedTruncSource q ω i)) c = 0 := by
    unfold blockSizeS blockFinset
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    have hv := congrArg (fun f : Fin q → Fin (2 ^ J + 1) => (f l0).val) hi
    have hlt := gridCellLabel_leaf_val_lt (q := q) (m := m) (J := J) hm hJ
      (markedTruncSource q ω i) l0
    rw [hv] at hlt
    exact (not_lt_of_ge hl0) hlt
  unfold markedBlockValue
  rw [← PartialMatching.maxCardValue_reindex
    (c := blockCost
      (fun i : Fin (mSourceCount ω) =>
        gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
      (fun j : Fin (mTargetCount ω) =>
        gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
      (fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) c)
    (e := finCongr hempty) (f := Equiv.refl _)]
  exact PartialMatching.maxCardValue_of_empty_rows _

/-- The sum over all padded labels equals the sum over the real blocks: labels
outside `{0, …, m-1}^q` carry the value zero. -/
theorem markedBlockValue_sum_eq_realBlocks {q m J : ℕ} (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (r t : ℝ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (ω : TwoMarkedCloudSpace q A B) :
    (∑ c : Fin q → Fin (2 ^ J + 1),
        markedBlockValue q m J hm hJ r t kin g ω c) =
      ∑ b : Fin q → Fin m,
        markedBlockValue q m J hm hJ r t kin g ω (blockLeafLabel q m J hJ b) := by
  classical
  let f : (Fin q → Fin (2 ^ J + 1)) → ℝ :=
    fun c => markedBlockValue q m J hm hJ r t kin g ω c
  let S : Finset (Fin q → Fin (2 ^ J + 1)) :=
    Finset.univ.filter (fun c => ∀ l, (c l).val < m)
  have hsub : S ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ c ∈ (Finset.univ : Finset (Fin q → Fin (2 ^ J + 1))),
      c ∉ S → f c = 0 := by
    intro c _ hc
    exact markedBlockValue_eq_zero_of_not_forall_lt hm hJ r t
      (kin := kin) (g := g) ω c
      (fun h => hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩))
  rw [← Finset.sum_subset hsub hzero]
  let ρ : (c : Fin q → Fin (2 ^ J + 1)) → c ∈ S → (Fin q → Fin m) :=
    fun c hc l => ⟨(c l).val, (Finset.mem_filter.mp hc).2 l⟩
  have hbij : (∑ c ∈ S, f c) =
      ∑ b : Fin q → Fin m, f (blockLeafLabel q m J hJ b) := by
    refine Finset.sum_bij (i := ρ) (fun c hc => Finset.mem_univ _) ?_ ?_ ?_
    · intro c₁ hc₁ c₂ hc₂ heq
      funext l
      apply Fin.ext
      have := congrArg (fun b : Fin q → Fin m => (b l).val) heq
      exact this
    · intro b _
      refine ⟨blockLeafLabel q m J hJ b, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun l => blockLeafLabel_lt q m J hJ b l⟩
      · funext l
        apply Fin.ext
        rfl
    · intro c hc
      apply congrArg f
      funext l
      apply Fin.ext
      rfl
  rw [hbij]

/-! ## The block-rescaling identity for the kinetic cost -/

/-- The block index of `x` is the floor of `m * x`. -/
theorem blockIndex_inv_eq_floor (m : ℕ) (x : ℝ) :
    blockIndex ((m : ℝ)⁻¹) x = ⌊(m : ℝ) * x⌋₊ := by
  unfold blockIndex
  rw [div_inv_eq_mul, mul_comm]

/-- The scaled local coordinate inside a block, written as the fractional part
`m * x - ⌊m * x⌋`. -/
theorem blockScaledLocalPoint_eq_sub (m : ℕ) (hm : 0 < m) (x : Fin q → ℝ) (l : Fin q) :
    blockScaledLocalPoint q m x l =
      (m : ℝ) * x l - ((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) := by
  have hmul : (m : ℝ) * (m : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast hm.ne')
  unfold blockScaledLocalPoint localCoord
  have hterm : (m : ℝ) * (((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) * (m : ℝ)⁻¹) =
      ((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) := by
    calc (m : ℝ) * (((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) * (m : ℝ)⁻¹)
        = ((m : ℝ) * ((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ)) * (m : ℝ)⁻¹ := by
          rw [mul_assoc]
      _ = (((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) * (m : ℝ)) * (m : ℝ)⁻¹ := by
          rw [mul_comm (m : ℝ)]
      _ = ((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) * ((m : ℝ) * (m : ℝ)⁻¹) := by
          rw [mul_assoc]
      _ = ((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) := by rw [hmul, mul_one]
  rw [mul_sub, hterm]

/-- The scaled local coordinate of a point with nonnegative coordinates is
nonnegative. -/
theorem blockScaledLocalPoint_nonneg {m : ℕ} (hm : 0 < m) (x : Fin q → ℝ) {l : Fin q}
    (hx : 0 ≤ x l) : 0 ≤ blockScaledLocalPoint q m x l := by
  rw [blockScaledLocalPoint_eq_sub m hm, blockIndex_inv_eq_floor]
  have h : (((⌊(m : ℝ) * x l⌋₊ : ℕ)) : ℝ) ≤ (m : ℝ) * x l :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) hx)
  linarith

/-- The scaled local coordinate of a point lies below one. -/
theorem blockScaledLocalPoint_lt_one (m : ℕ) (hm : 0 < m) (x : Fin q → ℝ) (l : Fin q) :
    blockScaledLocalPoint q m x l < 1 := by
  rw [blockScaledLocalPoint_eq_sub m hm, blockIndex_inv_eq_floor]
  have h := Nat.lt_floor_add_one ((m : ℝ) * x l)
  linarith

/-- The truncation of a scaled local coordinate is the coordinate itself. -/
theorem cubeTruncPoint_blockScaledLocalPoint (m : ℕ) (hm : 0 < m) {x : Fin q → ℝ}
    (hx : ∀ l, 0 ≤ x l) :
    cubeTruncPoint (blockScaledLocalPoint q m x) = blockScaledLocalPoint q m x := by
  funext l
  unfold cubeTruncPoint
  rw [if_pos]
  exact ⟨blockScaledLocalPoint_nonneg hm x (hx l), blockScaledLocalPoint_lt_one m hm x l⟩

/-- On the unit cube, the truncated displacement is the plain difference. -/
theorem mDisplacement_eq_sub_of_mem {x y : Fin q → ℝ} (hx : x ∈ unitCubeSet q)
    (hy : y ∈ unitCubeSet q) :
    mDisplacement x y = fun l => y l - x l := by
  funext l
  have hx' : x l ∈ Set.Ioo (0 : ℝ) 1 := by
    have := hx
    simp only [unitCubeSet, Set.mem_pi, Set.mem_univ, true_implies] at this
    exact this l
  have hy' : y l ∈ Set.Ioo (0 : ℝ) 1 := by
    have := hy
    simp only [unitCubeSet, Set.mem_pi, Set.mem_univ, true_implies] at this
    exact this l
  unfold mDisplacement cubeTruncPoint
  rw [if_pos ⟨le_of_lt hy'.1, hy'.2⟩, if_pos ⟨le_of_lt hx'.1, hx'.2⟩]

/-- The local displacement of two points in the same block is `m` times the
ambient displacement. -/
theorem mDisplacement_blockScaledLocalPoint
    {m : ℕ} (hm : 0 < m) {x y : Fin q → ℝ}
    (hx : x ∈ unitCubeSet q) (hy : y ∈ unitCubeSet q)
    (hxy : ∀ l, blockIndex ((m : ℝ)⁻¹) (x l) = blockIndex ((m : ℝ)⁻¹) (y l)) :
    mDisplacement (blockScaledLocalPoint q m x) (blockScaledLocalPoint q m y)
      = fun l => (m : ℝ) * (y l - x l) := by
  have hx0 : ∀ l, 0 ≤ x l := by
    intro l
    have := hx
    simp only [unitCubeSet, Set.mem_pi, Set.mem_univ, true_implies] at this
    exact le_of_lt (this l).1
  have hy0 : ∀ l, 0 ≤ y l := by
    intro l
    have := hy
    simp only [unitCubeSet, Set.mem_pi, Set.mem_univ, true_implies] at this
    exact le_of_lt (this l).1
  funext l
  unfold mDisplacement
  rw [cubeTruncPoint_blockScaledLocalPoint m hm hx0,
    cubeTruncPoint_blockScaledLocalPoint m hm hy0]
  rw [blockScaledLocalPoint_eq_sub m hm, blockScaledLocalPoint_eq_sub m hm, hxy l]
  ring

/-- The intensity scale of a block: `(r / m ^ q) ^ (2 / q)` is `r ^ (2 / q)`
times the inverse square of the block width. -/
theorem rpow_div_natPow (q : ℕ) (hq : 0 < q) {r : ℝ} (hr : 0 ≤ r)
    {m : ℕ} (hm : 0 < m) :
    (r / ((m : ℝ) ^ q)) ^ (2 / (q : ℝ)) =
      r ^ (2 / (q : ℝ)) * ((m : ℝ)⁻¹) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmq : (0 : ℝ) < (m : ℝ) ^ q := pow_pos hmR q
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow : ((m : ℝ) ^ q) ^ (2 / (q : ℝ)) = (m : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (m : ℝ) q, ← Real.rpow_mul hmR.le]
    have hq' : (q : ℝ) * (2 / (q : ℝ)) = 2 := by
      calc (q : ℝ) * (2 / (q : ℝ)) = 2 / (q : ℝ) * (q : ℝ) := by ring
        _ = 2 := div_mul_cancel₀ 2 hqR
    rw [hq', Real.rpow_two]
  rw [Real.div_rpow hr hmq.le, hpow]
  rw [inv_pow]
  ring

/-! ## The block-local matrix -/

/-- The source points of a marked cloud lying in the real block `b`. -/
def blockLocalFilter (q m : ℕ) (b : Fin q → Fin m) (z : MarkedCloudSpace q A) :
    Finset (Fin z.1) :=
  Finset.univ.filter (fun i : Fin z.1 =>
    ∀ l, blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l) = (b l).val)

theorem blockLocalCloud_fst (q m : ℕ) (b : Fin q → Fin m) (z : MarkedCloudSpace q A) :
    (blockLocalCloud q m b z).1 = (blockLocalFilter q m b z).card := rfl

theorem mem_blockLocalFilter {q m : ℕ} {b : Fin q → Fin m}
    {z : MarkedCloudSpace q A} {i : Fin z.1} :
    i ∈ blockLocalFilter q m b z ↔
      ∀ l, blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l) = (b l).val := by
  simp [blockLocalFilter]

/-- The matrix entries of the rescaled block cloud. -/
noncomputable def blockTiltedValue (q : ℕ) (r : ℝ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) : ℝ :=
  PartialMatching.maxCardValue (fun p : Fin dS.1 => fun q' : Fin dT.1 =>
    r ^ (2 / (q : ℝ)) * kin (dS.2 p).2 (dT.2 q').2
        (mDisplacement (dS.2 p).1 (dT.2 q').1) +
      t * g (dS.2 p).2 (dT.2 q').2)

/-- The block cloud of the raw (unencoded) filter has the local points written
with the scaled local coordinate. -/
theorem blockLocalCloud_apply (q m : ℕ) (b : Fin q → Fin m) (z : MarkedCloudSpace q A)
    (j : Fin (blockLocalCloud q m b z).1) :
    (blockLocalCloud q m b z).2 j =
      (blockScaledLocalPoint q m
        ((z.2 ((blockLocalFilter q m b z).orderIsoOfFin rfl j).1).1),
       (z.2 ((blockLocalFilter q m b z).orderIsoOfFin rfl j).1).2) := rfl

/-! ## Evaluation of block data -/

/-- The `j`-th point of a block data element, with a junk value beyond the
stored count. -/
noncomputable def blockDataEval {Pos : Type*} [hPos : Nonempty Pos] (j : ℕ)
    (d : BlockData Pos) : Pos :=
  if h : j < d.1 then d.2 ⟨j, h⟩ else Classical.choice hPos

theorem measurable_blockDataEval {Pos : Type*} [MeasurableSpace Pos] [hPos : Nonempty Pos]
    (j : ℕ) : Measurable (fun d : BlockData Pos => blockDataEval j d) := by
  classical
  intro S hS
  change MeasurableSet {d : BlockData Pos | blockDataEval j d ∈ S}
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((Sigma.mk n) ⁻¹'
    {d : BlockData Pos | blockDataEval j d ∈ S})
  have hfib : (Sigma.mk n) ⁻¹' {d : BlockData Pos | blockDataEval j d ∈ S} =
      if h : j < n then ((fun u : Fin n → Pos => u ⟨j, h⟩) ⁻¹' S)
      else if (Classical.choice hPos) ∈ S then Set.univ else ∅ := by
    split_ifs with h hmem
    · ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq, blockDataEval, dif_pos h]
    · ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [blockDataEval, dif_neg h]
      exact hmem
    · ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [blockDataEval, dif_neg h]
      exact hmem
  rw [hfib]
  split_ifs with h hmem
  · exact (measurable_pi_apply (X := fun _ : Fin n => Pos) ⟨j, h⟩) hS
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

theorem measurable_blockData_fst {Pos : Type*} [MeasurableSpace Pos] :
    Measurable (fun d : BlockData Pos => d.1) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {d : BlockData Pos | d.1 = n}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  change MeasurableSet ((Sigma.mk a) ⁻¹' {d : BlockData Pos | d.1 = n})
  by_cases h : a = n
  · subst h
    simp
  · have hE : (Sigma.mk a) ⁻¹' {d : BlockData Pos | d.1 = n} = ∅ := by
      ext u
      simp [h]
    rw [hE]
    exact MeasurableSet.empty

/-- **The block-rescaling identity for the kinetic cost.**  If two unit-cube
points lie in the same block, the ambient kinetic cost at intensity `r` equals
the local kinetic cost of their rescaled block coordinates at intensity
`r / m ^ q`, provided the kernel is quadratically homogeneous in the
displacement. -/
theorem mKineticCost_eq_local_of_same_block
    {m : ℕ} (hm : 0 < m) {q : ℕ} (hq : 0 < q) {r : ℝ} (hr : 0 ≤ r)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {a : A} {b : B} {x y : Fin q → ℝ}
    (hx : x ∈ unitCubeSet q) (hy : y ∈ unitCubeSet q)
    (hxy : ∀ l, blockIndex ((m : ℝ)⁻¹) (x l) = blockIndex ((m : ℝ)⁻¹) (y l)) :
    r ^ (2 / (q : ℝ)) * kin a b (mDisplacement x y) =
      (r / ((m : ℝ) ^ q)) ^ (2 / (q : ℝ)) *
        kin a b (mDisplacement (blockScaledLocalPoint q m x)
          (blockScaledLocalPoint q m y)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hinv : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr hmR.le
  have hdisp := mDisplacement_blockScaledLocalPoint (q := q) hm hx hy hxy
  have hdispAmb := mDisplacement_eq_sub_of_mem hx hy
  have hhom := hkin_homog a b ((m : ℝ)⁻¹) hinv
    (mDisplacement (blockScaledLocalPoint q m x) (blockScaledLocalPoint q m y))
  have harg : (fun l => (m : ℝ)⁻¹ *
      mDisplacement (blockScaledLocalPoint q m x) (blockScaledLocalPoint q m y) l) =
      fun l => y l - x l := by
    funext l
    rw [hdisp]
    rw [← mul_assoc, inv_mul_cancel₀ hmR.ne', one_mul]
  rw [harg] at hhom
  rw [hdispAmb, hhom, rpow_div_natPow q hq hr hm]
  ring


/-! ## Measurability of the block matrix encoding -/

/-- The canonical block-data encoding of a marked cloud is measurable. -/
theorem measurable_blockDataMk (q : ℕ) (A : Type*) [MeasurableSpace A] :
    Measurable (fun z : MarkedCloudSpace q A =>
      (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData ((Fin q → ℝ) × A))) := by
  intro S hS
  have hcompMeas : ∀ n, Measurable (fun y : ℕ → (Fin q → ℝ) × A =>
      (⟨n, fun j : Fin n => y j⟩ : BlockData ((Fin q → ℝ) × A))) := by
    intro n
    exact (measurable_sigma_mk n).comp
      (measurable_pi_lambda (fun (y : ℕ → (Fin q → ℝ) × A) (j : Fin n) => y j)
        (fun j => measurable_pi_apply (X := fun _ : ℕ => (Fin q → ℝ) × A) (j : ℕ)))
  have hpre : (fun z : MarkedCloudSpace q A =>
        (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData ((Fin q → ℝ) × A))) ⁻¹' S =
      ⋃ n : ℕ, (Prod.fst ⁻¹' {n}) ∩
        (Prod.snd ⁻¹' ((fun y : ℕ → (Fin q → ℝ) × A =>
          (⟨n, fun j : Fin n => y j⟩ : BlockData ((Fin q → ℝ) × A))) ⁻¹' S)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨z.1, rfl, hz⟩
    · rintro ⟨n, hn, hz⟩
      subst hn
      exact hz
  rw [hpre]
  exact MeasurableSet.iUnion fun n =>
    MeasurableSet.inter
      (measurable_fst (measurableSet_singleton n))
      (measurable_snd ((hcompMeas n) hS))

set_option maxHeartbeats 800000 in
/-- Measurability of the block matrix value as a function of the two block data
elements. -/
theorem measurable_blockTiltedValue
    (q : ℕ) (r : ℝ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Nonempty A] [Nonempty B]
    {C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Measurable (fun p :
      BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockTiltedValue q r kin g t p.1 p.2) := by
  classical
  let Bnd : ℝ := r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G
  let e : (BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B)) →
      ℕ → ℕ → ℝ :=
    fun p i j =>
      r ^ (2 / (q : ℝ)) *
          kin (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
              (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2
              (mDisplacement (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1
                (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1) +
        t * g (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
              (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2
  have he : ∀ i j, Measurable fun p => e p i j := by
    intro i j
    have hsa : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockDataEval (Pos := (Fin q → ℝ) × A) i p.1 :=
      (measurable_blockDataEval i).comp measurable_fst
    have hsb : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockDataEval (Pos := (Fin q → ℝ) × B) j p.2 :=
      (measurable_blockDataEval j).comp measurable_snd
    have hsaP : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1 :=
      measurable_fst.comp hsa
    have hsaM : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2 :=
      measurable_snd.comp hsa
    have hsbP : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1 :=
      measurable_fst.comp hsb
    have hsbM : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2 :=
      measurable_snd.comp hsb
    have hdisp : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        mDisplacement (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1
          (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1 := by
      apply measurable_pi_lambda
      intro l
      exact ((measurable_cubeTruncPoint_apply q l).comp hsbP).sub
        ((measurable_cubeTruncPoint_apply q l).comp hsaP)
    have hkinm : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        kin (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
          (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2
          (mDisplacement (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1
            (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1) :=
      hkin.comp ((hsaM.prodMk hsbM).prodMk hdisp)
    have hgm : Measurable fun p : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        g (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
          (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2 :=
      hg.comp (hsaM.prodMk hsbM)
    exact (hkinm.const_mul _).add (hgm.const_mul t)
  have hBbound : ∀ p i j, e p i j ≤ Bnd := by
    intro p i j
    have hkinle : kin (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
        (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2
        (mDisplacement (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1
          (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1) ≤ C * (q : ℝ) := by
      calc kin (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
            (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2
            (mDisplacement (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1
              (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1)
          ≤ |kin (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
              (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2
              (mDisplacement (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1
                (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1)| := le_abs_self _
        _ ≤ C * ∑ l, (mDisplacement (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).1
              (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).1) l ^ 2 := hkin_bound _ _ _
        _ ≤ C * (q : ℝ) :=
            mul_le_mul_of_nonneg_left (mDisplacement_sq_sum_le q _ _) hC0
    have hprobe := probe_mul_le (A := A) (B := B) t (g := g) (G := G) hgb
      (blockDataEval (Pos := (Fin q → ℝ) × A) i p.1).2
      (blockDataEval (Pos := (Fin q → ℝ) × B) j p.2).2
    have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have hmul := mul_le_mul_of_nonneg_left hkinle hrpow
    dsimp only [e, Bnd]
    linarith
  have hNp : Measurable fun p : BlockData ((Fin q → ℝ) × A) ×
      BlockData ((Fin q → ℝ) × B) => p.1.1 :=
    measurable_blockData_fst.comp measurable_fst
  have hNm : Measurable fun p : BlockData ((Fin q → ℝ) × A) ×
      BlockData ((Fin q → ℝ) × B) => p.2.1 :=
    measurable_blockData_fst.comp measurable_snd
  have hcloud : Measurable (cloudValueNat e (fun p => p.1.1) (fun p => p.2.1)) :=
    measurable_cloudValueNat (Ω := BlockData ((Fin q → ℝ) × A) ×
      BlockData ((Fin q → ℝ) × B)) (e := e) he hNp hNm
      (B := fun _ => Bnd) measurable_const hBbound
  have hfun : (fun p :
      BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) =>
        blockTiltedValue q r kin g t p.1 p.2) =
      cloudValueNat e (fun p => p.1.1) (fun p => p.2.1) := by
    funext p
    unfold blockTiltedValue cloudValueNat
    congr 1
    funext i j
    dsimp only [e]
    have hi : blockDataEval (Pos := (Fin q → ℝ) × A) (↑i) p.1 = p.1.2 i := by
      rw [blockDataEval, dif_pos i.isLt]
    have hj : blockDataEval (Pos := (Fin q → ℝ) × B) (↑j) p.2 = p.2.2 j := by
      rw [blockDataEval, dif_pos j.isLt]
    rw [hi, hj]
  rw [hfun]
  exact hcloud


/-- Measurability of the block-data enumeration by a finite label vector. -/
theorem measurable_blockDataOfPairs {n K : ℕ} {Pos : Type*} [MeasurableSpace Pos]
    (b : Fin K) : Measurable (blockDataOfPairs (n := n) (Pos := Pos) b) := by
  classical
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin K) Pos (Fin n)
  have hcomp : Measurable ((blockDataOfPairs (n := n) (Pos := Pos) b) ∘ e.symm) := by
    intro S hS
    have hu : ∀ u : Fin n → Fin K, Measurable (fun y : Fin n → Pos =>
        (⟨(Finset.univ.filter (fun i => u i = b)).card,
          fun j => y (((Finset.univ.filter (fun i => u i = b)).orderIsoOfFin rfl) j).1⟩ :
          BlockData Pos)) := by
      intro u
      let s := Finset.univ.filter (fun i => u i = b)
      have hproj : Measurable (fun y : Fin n → Pos => fun j : Fin s.card =>
          y ((s.orderIsoOfFin rfl j).1)) :=
        measurable_pi_lambda _ (fun j => measurable_pi_apply (X := fun _ : Fin n => Pos) (s.orderIsoOfFin rfl j).1)
      exact (measurable_sigma_mk s.card).comp hproj
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
              BlockData Pos) := rfl
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
              BlockData Pos) := rfl
        rw [hval, hpu_eq]
        exact huf
    rw [hUnion]
    exact MeasurableSet.iUnion fun u =>
      MeasurableSet.prod (measurableSet_singleton u) ((hu u) hS)
  have hEq : blockDataOfPairs (n := n) (Pos := Pos) b =
      ((blockDataOfPairs (n := n) (Pos := Pos) b) ∘ e.symm) ∘ e := by
    funext z
    simp [e]
  rw [hEq]
  exact hcomp.comp e.measurable

/-- The encoded block cloud has at most as many points as the ambient cloud. -/
theorem blockLocalCloudEncoded_fst_le (q m : ℕ) [NeZero m] (b : Fin q → Fin m)
    (z : MarkedCloudSpace q A) :
    (blockLocalCloudEncoded (A := A) q m b z).1 ≤ z.1 := by
  classical
  unfold blockLocalCloudEncoded prefixBlockData
  change (Finset.univ.filter (fun i : Fin z.1 =>
    markedLabelCode q m z i = finFunctionFinEquiv b)).card ≤ z.1
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin z.1))
    (fun i => markedLabelCode q m z i = finFunctionFinEquiv b)

set_option maxHeartbeats 800000 in
/-- Measurability of the encoded block cloud. -/
theorem measurable_blockLocalCloudEncoded (q m : ℕ) [NeZero m] (b : Fin q → Fin m) :
    Measurable (blockLocalCloudEncoded (A := A) q m b) := by
  classical
  let Pos := (Fin q → ℝ) × A
  let Y : ℕ → MarkedCloudSpace q A → BlockData Pos := fun n z =>
    blockDataOfPairs (finFunctionFinEquiv b) (fun i : Fin n =>
      (markedLabelCode q m z i, blockLocalMark (A := A) q m (z.2 i)))
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    have hp : Measurable (fun z : MarkedCloudSpace q A => fun i : Fin n =>
        (markedLabelCode q m z i, blockLocalMark (A := A) q m (z.2 i))) :=
      measurable_pi_lambda _ (fun i =>
        (measurable_markedLabelCode q m i).prodMk
          ((measurable_blockLocalMark q m).comp
            ((measurable_pi_apply (X := fun _ : ℕ => (Fin q → ℝ) × A) i).comp measurable_snd)))
    exact (measurable_blockDataOfPairs (n := n) (Pos := Pos)
      (finFunctionFinEquiv b)).comp hp
  have hjoint : Measurable (fun p : ℕ × MarkedCloudSpace q A => Y p.1 p.2) := by
    intro S hS
    have hpre : (fun p : ℕ × MarkedCloudSpace q A => Y p.1 p.2) ⁻¹' S =
        ⋃ n : ℕ, ({n} : Set ℕ) ×ˢ (Y n ⁻¹' S) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro hp
        exact ⟨p.1, rfl, hp⟩
      · rintro ⟨n, hn, hp⟩
        subst hn
        exact hp
    rw [hpre]
    exact MeasurableSet.iUnion fun n =>
      MeasurableSet.prod (measurableSet_singleton n) ((hY n) hS)
  have hpair : Measurable (fun z : MarkedCloudSpace q A => (z.1, z)) :=
    measurable_fst.prodMk measurable_id
  have hcomp : Measurable (fun z : MarkedCloudSpace q A => Y (z.1) z) :=
    hjoint.comp hpair
  convert hcomp using 2
  unfold blockLocalCloudEncoded prefixBlockData Y blockDataOfPairs
  rfl


/-! ## The per-block deterministic identity -/

set_option maxHeartbeats 1600000 in
/-- **One block, one colour.**  On the unit cube, the ambient leaf-block value of
the real block `b` equals the block matrix of the rescaled block cloud, with the
ambient kinetic coefficient `r` rescaled to `r / m ^ q`. -/
theorem markedBlockValue_eq_blockTiltedValue
    {q m J : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hq : 0 < q)
    {r t C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (b : Fin q → Fin m) (ω : TwoMarkedCloudSpace q A B)
    (hz1 : ∀ i, mSourcePoint ω i ∈ unitCubeSet q)
    (hz2 : ∀ j, mTargetPoint ω j ∈ unitCubeSet q) :
    markedBlockValue q m J hm hJ r t kin g ω (blockLeafLabel q m J hJ b) =
      blockTiltedValue q (r / ((m : ℝ) ^ q)) kin g t
        (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2) := by
  classical
  let labS : Fin (mSourceCount ω) → Fin q → Fin (2 ^ J + 1) :=
    fun i => gridCellLabel q m J J hm hJ (markedTruncSource q ω i)
  let labT : Fin (mTargetCount ω) → Fin q → Fin (2 ^ J + 1) :=
    fun j => gridCellLabel q m J J hm hJ (markedTruncTarget q ω j)
  let edge : Fin (mSourceCount ω) → Fin (mTargetCount ω) → ℝ :=
    fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)
  let bl : Fin q → Fin (2 ^ J + 1) := blockLeafLabel q m J hJ b
  have hfinS : blockFinset labS bl = blockLocalFilter q m b ω.1 := by
    change Finset.univ.filter (fun i : Fin (mSourceCount ω) => labS i = bl) =
      Finset.univ.filter (fun i : Fin (mSourceCount ω) =>
        ∀ l, blockIndex ((m : ℝ)⁻¹) ((ω.1.2 i).1 l) = (b l).val)
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := gridCellLabel_trunc_eq_iff (q := q) (m := m) (J := J) hm hJ
      (hz1 (i : ℕ)) b
    simpa only [labS, bl, markedTruncSource, mSourcePoint] using h
  have hfinT : blockFinset labT bl = blockLocalFilter q m b ω.2 := by
    change Finset.univ.filter (fun j : Fin (mTargetCount ω) => labT j = bl) =
      Finset.univ.filter (fun j : Fin (mTargetCount ω) =>
        ∀ l, blockIndex ((m : ℝ)⁻¹) ((ω.2.2 j).1 l) = (b l).val)
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := gridCellLabel_trunc_eq_iff (q := q) (m := m) (J := J) hm hJ
      (hz2 (j : ℕ)) b
    simpa only [labT, bl, markedTruncTarget, mTargetPoint] using h
  have hsizeS : blockSizeS labS bl = (blockLocalFilter q m b ω.1).card := by
    rw [blockSizeS, hfinS]
    rfl
  have hsizeT : blockSizeT labT bl = (blockLocalFilter q m b ω.2).card := by
    rw [blockSizeT, hfinT]
    rfl
  -- The permutation relating `Finset.equivFin` (used by `blockCost`) with the
  -- increasing enumeration (used by `blockLocalCloud`).
  let eFunS : Fin (blockSizeS labS bl) → Fin (blockLocalCloud q m b ω.1).1 := fun p =>
    (blockLocalFilter q m b ω.1).orderIsoOfFin rfl |>.symm
      ⟨blockEmbeddingS labS bl p, hfinS ▸ blockEmbeddingS_mem labS bl p⟩
  let eFunT : Fin (blockSizeT labT bl) → Fin (blockLocalCloud q m b ω.2).1 := fun p =>
    (blockLocalFilter q m b ω.2).orderIsoOfFin rfl |>.symm
      ⟨blockEmbeddingT labT bl p, hfinT ▸ blockEmbeddingT_mem labT bl p⟩
  have hePropS : ∀ p, (blockLocalFilter q m b ω.1).orderIsoOfFin rfl (eFunS p) =
      ⟨blockEmbeddingS labS bl p, hfinS ▸ blockEmbeddingS_mem labS bl p⟩ := by
    intro p
    exact (blockLocalFilter q m b ω.1).orderIsoOfFin rfl |>.apply_symm_apply _
  have hePropT : ∀ p, (blockLocalFilter q m b ω.2).orderIsoOfFin rfl (eFunT p) =
      ⟨blockEmbeddingT labT bl p, hfinT ▸ blockEmbeddingT_mem labT bl p⟩ := by
    intro p
    exact (blockLocalFilter q m b ω.2).orderIsoOfFin rfl |>.apply_symm_apply _
  have heInjS : Function.Injective eFunS := by
    intro p q' hpq
    apply blockEmbeddingS_injective labS bl
    have h1 := congrArg (fun j =>
      ((blockLocalFilter q m b ω.1).orderIsoOfFin rfl j).1) hpq
    rw [hePropS p, hePropS q'] at h1
    exact h1
  have heInjT : Function.Injective eFunT := by
    intro p q' hpq
    apply blockEmbeddingT_injective labT bl
    have h1 := congrArg (fun j =>
      ((blockLocalFilter q m b ω.2).orderIsoOfFin rfl j).1) hpq
    rw [hePropT p, hePropT q'] at h1
    exact h1
  let eS : Fin (blockSizeS labS bl) ≃ Fin (blockLocalCloud q m b ω.1).1 :=
    Equiv.ofBijective eFunS
      (Fintype.bijective_iff_injective_and_card eFunS |>.mpr
        ⟨heInjS, by
          rw [Fintype.card_fin, Fintype.card_fin]
          exact hsizeS.trans (blockLocalCloud_fst q m b ω.1).symm⟩)
  let eT : Fin (blockSizeT labT bl) ≃ Fin (blockLocalCloud q m b ω.2).1 :=
    Equiv.ofBijective eFunT
      (Fintype.bijective_iff_injective_and_card eFunT |>.mpr
        ⟨heInjT, by
          rw [Fintype.card_fin, Fintype.card_fin]
          exact hsizeT.trans (blockLocalCloud_fst q m b ω.2).symm⟩)
  have heS_apply : ∀ p, eS p = eFunS p := fun p => rfl
  have heT_apply : ∀ p, eT p = eFunT p := fun p => rfl
  have hiS : ∀ p, ((blockLocalFilter q m b ω.1).orderIsoOfFin rfl (eS p)).1 =
      blockEmbeddingS labS bl p := by
    intro p
    rw [heS_apply p]
    exact congrArg Subtype.val (hePropS p)
  have hiT : ∀ p, ((blockLocalFilter q m b ω.2).orderIsoOfFin rfl (eT p)).1 =
      blockEmbeddingT labT bl p := by
    intro p
    rw [heT_apply p]
    exact congrArg Subtype.val (hePropT p)
  -- The local matrix indexed by the increasing enumeration.
  let L : Fin (blockLocalCloud q m b ω.1).1 →
      Fin (blockLocalCloud q m b ω.2).1 → ℝ := fun p q' =>
    (r / ((m : ℝ) ^ q)) ^ (2 / (q : ℝ)) *
        kin ((blockLocalCloud q m b ω.1).2 p).2
            ((blockLocalCloud q m b ω.2).2 q').2
          (mDisplacement ((blockLocalCloud q m b ω.1).2 p).1
            ((blockLocalCloud q m b ω.2).2 q').1) +
      t * g ((blockLocalCloud q m b ω.1).2 p).2
            ((blockLocalCloud q m b ω.2).2 q').2
  -- Local points of the block cloud are the scaled ambient points.
  have hpointS : ∀ p : Fin (blockSizeS labS bl),
      (blockLocalCloud q m b ω.1).2 (eS p) =
      (blockScaledLocalPoint q m
        (mSourcePoint ω ↑(blockEmbeddingS labS bl p)),
       mSourceMark ω ↑(blockEmbeddingS labS bl p)) := by
    intro p
    rw [blockLocalCloud_apply q m b ω.1 (eS p), hiS p]
    rfl
  have hpointT : ∀ p : Fin (blockSizeT labT bl),
      (blockLocalCloud q m b ω.2).2 (eT p) =
      (blockScaledLocalPoint q m
        (mTargetPoint ω ↑(blockEmbeddingT labT bl p)),
       mTargetMark ω ↑(blockEmbeddingT labT bl p)) := by
    intro p
    rw [blockLocalCloud_apply q m b ω.2 (eT p), hiT p]
    rfl
  have hpredS : ∀ p : Fin (blockSizeS labS bl),
      ∀ l, blockIndex ((m : ℝ)⁻¹)
        (mSourcePoint ω ↑(blockEmbeddingS labS bl p) l) = (b l).val := by
    intro p l
    have hmem : (blockEmbeddingS labS bl p) ∈ blockLocalFilter q m b ω.1 :=
      hfinS ▸ blockEmbeddingS_mem labS bl p
    have hpred := (mem_blockLocalFilter.mp hmem) l
    simpa only [mSourceCount, mSourcePoint] using hpred
  have hpredT : ∀ p : Fin (blockSizeT labT bl),
      ∀ l, blockIndex ((m : ℝ)⁻¹)
        (mTargetPoint ω ↑(blockEmbeddingT labT bl p) l) = (b l).val := by
    intro p l
    have hmem : (blockEmbeddingT labT bl p) ∈ blockLocalFilter q m b ω.2 :=
      hfinT ▸ blockEmbeddingT_mem labT bl p
    have hpred := (mem_blockLocalFilter.mp hmem) l
    simpa only [mTargetCount, mTargetPoint] using hpred
  -- The entrywise identity.
  have hentry : ∀ (p : Fin (blockSizeS labS bl)) (q' : Fin (blockSizeT labT bl)),
      edge (blockEmbeddingS labS bl p) (blockEmbeddingT labT bl q') = L (eS p) (eT q') := by
    intro p q'
    have hxy : ∀ l, blockIndex ((m : ℝ)⁻¹)
        (mSourcePoint ω ↑(blockEmbeddingS labS bl p) l) =
        blockIndex ((m : ℝ)⁻¹)
          (mTargetPoint ω ↑(blockEmbeddingT labT bl q') l) :=
      fun l => (hpredS p l).trans (hpredT q' l).symm
    have hk := mKineticCost_eq_local_of_same_block (q := q) (m := m) hm hq hr
      (kin := kin)
      hkin_homog
      (a := mSourceMark ω ↑(blockEmbeddingS labS bl p))
      (b := mTargetMark ω ↑(blockEmbeddingT labT bl q'))
      (x := mSourcePoint ω ↑(blockEmbeddingS labS bl p))
      (y := mTargetPoint ω ↑(blockEmbeddingT labT bl q'))
      (hz1 ↑(blockEmbeddingS labS bl p)) (hz2 ↑(blockEmbeddingT labT bl q')) hxy
    have hprobe : mProbe g ω ↑(blockEmbeddingS labS bl p)
        ↑(blockEmbeddingT labT bl q') =
        g ((blockLocalCloud q m b ω.1).2 (eS p)).2
          ((blockLocalCloud q m b ω.2).2 (eT q')).2 := by
      unfold mProbe
      rw [hpointS p, hpointT q']
    have hkin : mKineticCost q r kin ω ↑(blockEmbeddingS labS bl p)
        ↑(blockEmbeddingT labT bl q') =
        (r / ((m : ℝ) ^ q)) ^ (2 / (q : ℝ)) *
          kin ((blockLocalCloud q m b ω.1).2 (eS p)).2
              ((blockLocalCloud q m b ω.2).2 (eT q')).2
            (mDisplacement ((blockLocalCloud q m b ω.1).2 (eS p)).1
              ((blockLocalCloud q m b ω.2).2 (eT q')).1) := by
      unfold mKineticCost
      rw [hpointS p, hpointT q']
      exact hk
    dsimp only [edge, markedEdgeCost, L]
    rw [hkin, hprobe]
  -- The block matrix is a reindexing of the local matrix.
  have hcost : blockCost labS labT edge bl = fun p => fun q' => L (eS p) (eT q') := by
    funext p q'
    exact hentry p q'
  have hmax : PartialMatching.maxCardValue (blockCost labS labT edge bl) =
      PartialMatching.maxCardValue L := by
    rw [hcost]
    have hre := PartialMatching.maxCardValue_reindex L eS.symm eT.symm
    simpa only [Equiv.symm_symm] using hre
  rw [markedBlockValue]
  change PartialMatching.maxCardValue (blockCost labS labT edge bl) = _
  rw [hmax]
  unfold blockTiltedValue
  rfl


/-! ## Integration over one block -/

/-- An almost-everywhere property of the first factor of a product with a
probability measure. -/
theorem ae_fst_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν] {p : α → Prop}
    (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ z ∂(μ.prod ν), p z.1 := by
  have hh : μ {x | ¬ p x} = 0 := MeasureTheory.ae_iff.mp h
  rw [MeasureTheory.ae_iff]
  have hset : {z : α × β | ¬ p z.1} = {x | ¬ p x} ×ˢ (Set.univ : Set β) := by
    ext z
    simp
  rw [hset]
  refine le_antisymm ?_ zero_le
  calc (μ.prod ν) ({x | ¬ p x} ×ˢ (Set.univ : Set β))
      ≤ μ {x | ¬ p x} * ν (Set.univ : Set β) := Measure.prod_prod_le _ _
    _ = 0 := by rw [hh, measure_univ, zero_mul]

/-- An almost-everywhere property of the second factor of a product with a
probability measure. -/
theorem ae_snd_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] {p : β → Prop}
    (h : ∀ᵐ y ∂ν, p y) : ∀ᵐ z ∂(μ.prod ν), p z.2 := by
  have hh : ν {y | ¬ p y} = 0 := MeasureTheory.ae_iff.mp h
  rw [MeasureTheory.ae_iff]
  have hset : {z : α × β | ¬ p z.2} = (Set.univ : Set α) ×ˢ {y | ¬ p y} := by
    ext z
    simp
  rw [hset]
  refine le_antisymm ?_ zero_le
  calc (μ.prod ν) ((Set.univ : Set α) ×ˢ {y | ¬ p y})
      ≤ μ (Set.univ : Set α) * ν {y | ¬ p y} := Measure.prod_prod_le _ _
    _ = 0 := by rw [hh, measure_univ, mul_zero]

/-- The block matrix of a cloud encoded as block data is the marked tilted value
of the cloud. -/
theorem blockTiltedValue_blockDataMk (q : ℕ) (r : ℝ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} (t : ℝ)
    (zS : MarkedCloudSpace q A) (zT : MarkedCloudSpace q B) :
    blockTiltedValue q r kin g t
      (⟨zS.1, fun j : Fin zS.1 => zS.2 j⟩ : BlockData ((Fin q → ℝ) × A))
      (⟨zT.1, fun j : Fin zT.1 => zT.2 j⟩ : BlockData ((Fin q → ℝ) × B))
      = markedTilted q r kin g t (zS, zT) := by
  unfold blockTiltedValue markedTilted tiltedCloudValue mKineticCost mProbe
    mSourceMark mSourcePoint mTargetMark mTargetPoint
  rfl

set_option maxHeartbeats 1600000 in
/-- **Expectation of one block.**  The expected value of the rescaled block cloud
is the marked pressure at the per-block intensity `R / m ^ q`. -/
theorem integral_blockTiltedValue_blockLocalCloud
    (q m : ℕ) (hm : 0 < m) (hq : 0 < q) (R : ℝ≥0)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (b : Fin q → Fin m) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
          (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)
      ∂(twoMarkedCloudLaw (q := q) A B α β R)
      = markedPressure q A B α β (R / (m ^ q : ℝ≥0)) kin g t := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure α
  haveI : Nonempty B := nonempty_of_isProbabilityMeasure β
  let c : ℝ≥0 := R / (m ^ q : ℝ≥0)
  let rloc : ℝ := (c : ℝ)
  let PosA := (Fin q → ℝ) × A
  let PosB := (Fin q → ℝ) × B
  let encA : MarkedCloudSpace q A → BlockData PosA := blockLocalCloudEncoded (A := A) q m b
  let encB : MarkedCloudSpace q B → BlockData PosB := blockLocalCloudEncoded (A := B) q m b
  let mkA : MarkedCloudSpace q A → BlockData PosA :=
    fun z => (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData PosA)
  let mkB : MarkedCloudSpace q B → BlockData PosB :=
    fun z => (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData PosB)
  have hc0 : 0 ≤ rloc := c.coe_nonneg
  have hEncMeas : Measurable fun ω : TwoMarkedCloudSpace q A B =>
      (encA ω.1, encB ω.2) :=
    ((measurable_blockLocalCloudEncoded (A := A) q m b).comp measurable_fst).prodMk
      ((measurable_blockLocalCloudEncoded (A := B) q m b).comp measurable_snd)
  have hmkA : Measurable mkA := measurable_blockDataMk q A
  have hmkB : Measurable mkB := measurable_blockDataMk q B
  have hpairMeas : Measurable fun z : MarkedCloudSpace q A × MarkedCloudSpace q B =>
      (mkA z.1, mkB z.2) :=
    (hmkA.comp measurable_fst).prodMk (hmkB.comp measurable_snd)
  have hΦ : Measurable fun d : BlockData PosA × BlockData PosB =>
      blockTiltedValue q rloc kin g t d.1 d.2 :=
    measurable_blockTiltedValue q rloc hc0 hC0 hG0 hkin hkin_bound hg hgb t
  -- The law of the encoded block cloud is the block-data law.
  have hlawA : (markedPoissonLaw (q := q) A α R).map encA =
      blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
        (fun n => poissonMeasure c {n}) := by
    simpa only [encA, c] using
      (blockLocalCloudEncoded_law (q := q) (m := m) (A := A) hm R α b)
  have hlawB : (markedPoissonLaw (q := q) B β R).map encB =
      blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
        (fun n => poissonMeasure c {n}) := by
    simpa only [encB, c] using
      (blockLocalCloudEncoded_law (q := q) (m := m) (A := B) hm R β b)
  have hBD_A : blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
      (fun n => poissonMeasure c {n}) =
      (markedPoissonLaw (q := q) A α c).map mkA := by
    rw [blockDataLaw_eq_map_cloud]
    simp only [markedPoissonLaw, markedSeqLaw, mkA]
  have hBD_B : blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
      (fun n => poissonMeasure c {n}) =
      (markedPoissonLaw (q := q) B β c).map mkB := by
    rw [blockDataLaw_eq_map_cloud]
    simp only [markedPoissonLaw, markedSeqLaw, mkB]
  -- Almost-everywhere agreement of raw and encoded block clouds, on both sides.
  have hrawA := blockLocalCloud_ae_eq_encoded (q := q) (m := m) (A := A) hm R α b
  have hrawB := blockLocalCloud_ae_eq_encoded (q := q) (m := m) (A := B) hm R β b
  have hpairae : ∀ᵐ ω ∂((markedPoissonLaw (q := q) A α R).prod
      (markedPoissonLaw (q := q) B β R)),
      blockLocalCloud (A := A) q m b ω.1 = encA ω.1 ∧
      blockLocalCloud (A := B) q m b ω.2 = encB ω.2 :=
    (ae_fst_of_ae hrawA).and (ae_snd_of_ae hrawB)
  change ∫ ω, blockTiltedValue q rloc kin g t
      (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)
      ∂((markedPoissonLaw (q := q) A α R).prod (markedPoissonLaw (q := q) B β R))
    = markedPressure q A B α β c kin g t
  calc
    ∫ ω, blockTiltedValue q rloc kin g t
        (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)
        ∂((markedPoissonLaw (q := q) A α R).prod (markedPoissonLaw (q := q) B β R))
        = ∫ ω, blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2)
            ∂((markedPoissonLaw (q := q) A α R).prod
              (markedPoissonLaw (q := q) B β R)) := by
          apply integral_congr_ae
          filter_upwards [hpairae] with ω hω
          rw [hω.1, hω.2]
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((markedPoissonLaw (q := q) A α R).prod
              (markedPoissonLaw (q := q) B β R)).map
                (fun ω => (encA ω.1, encB ω.2))) := by
          exact (integral_map hEncMeas.aemeasurable hΦ.aestronglyMeasurable).symm
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((markedPoissonLaw (q := q) A α R).map encA).prod
              ((markedPoissonLaw (q := q) B β R).map encB)) := by
          rw [Measure.map_prod_map (markedPoissonLaw (q := q) A α R)
            (markedPoissonLaw (q := q) B β R)
            (measurable_blockLocalCloudEncoded (A := A) q m b)
            (measurable_blockLocalCloudEncoded (A := B) q m b)]
          rfl
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
                (fun n => poissonMeasure c {n})).prod
              (blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
                (fun n => poissonMeasure c {n})) := by
          rw [hlawA, hlawB]
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((markedPoissonLaw (q := q) A α c).map mkA).prod
              ((markedPoissonLaw (q := q) B β c).map mkB)) := by
          rw [hBD_A, hBD_B]
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((markedPoissonLaw (q := q) A α c).prod
              (markedPoissonLaw (q := q) B β c)).map
                (fun z => (mkA z.1, mkB z.2))) := by
          rw [Measure.map_prod_map (markedPoissonLaw (q := q) A α c)
            (markedPoissonLaw (q := q) B β c) hmkA hmkB]
          rfl
      _ = ∫ z : MarkedCloudSpace q A × MarkedCloudSpace q B,
            blockTiltedValue q rloc kin g t (mkA z.1) (mkB z.2)
            ∂((markedPoissonLaw (q := q) A α c).prod
              (markedPoissonLaw (q := q) B β c)) := by
          exact integral_map hpairMeas.aemeasurable hΦ.aestronglyMeasurable
      _ = ∫ z : MarkedCloudSpace q A × MarkedCloudSpace q B,
            markedTilted q rloc kin g t (z.1, z.2)
            ∂((markedPoissonLaw (q := q) A α c).prod
              (markedPoissonLaw (q := q) B β c)) := by
          apply integral_congr_ae
          filter_upwards with z
          exact blockTiltedValue_blockDataMk q rloc (kin := kin) (g := g) t z.1 z.2
      _ = markedPressure q A B α β c kin g t := rfl


/-- A uniform bound on the block matrix value. -/
theorem abs_blockTiltedValue_le
    (q : ℕ) {r C G t : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    |blockTiltedValue q r kin g t dS dT| ≤
      ((min dS.1 dT.1 : ℕ) : ℝ) *
        (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) := by
  unfold blockTiltedValue
  refine PartialMatching.abs_maxCardValue_perturbed_le
    (c := fun i j => r ^ (2 / (q : ℝ)) *
      kin (dS.2 i).2 (dT.2 j).2 (mDisplacement (dS.2 i).1 (dT.2 j).1))
    (g := fun i j => g (dS.2 i).2 (dT.2 j).2)
    (Bc := r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) (G := G) (t := t) ?_ ?_ ?_ hG0
  · intro i j
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
    have hkinle : |kin (dS.2 i).2 (dT.2 j).2
        (mDisplacement (dS.2 i).1 (dT.2 j).1)| ≤ C * (q : ℝ) := by
      calc |kin (dS.2 i).2 (dT.2 j).2 (mDisplacement (dS.2 i).1 (dT.2 j).1)|
          ≤ C * ∑ l, (mDisplacement (dS.2 i).1 (dT.2 j).1) l ^ 2 := hkin_bound _ _ _
        _ ≤ C * (q : ℝ) :=
            mul_le_mul_of_nonneg_left (mDisplacement_sq_sum_le q _ _) hC0
    exact mul_le_mul_of_nonneg_left hkinle (Real.rpow_nonneg hr _)
  · exact mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC0 (Nat.cast_nonneg q))
  · intro i j
    exact hgb _ _

set_option maxHeartbeats 1600000 in
/-- Integrability of the leaf-block value. -/
theorem integrable_markedBlockValue
    (q m J : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hq : 0 < q)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) {r t C G : ℝ} (hr : 0 ≤ r) (hrR : r = (R : ℝ))
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (b : Fin q → Fin m) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      markedBlockValue q m J hm hJ r t kin g ω (blockLeafLabel q m J hJ b))
      (twoMarkedCloudLaw (q := q) A B α β R) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure α
  haveI : Nonempty B := nonempty_of_isProbabilityMeasure β
  let c : ℝ≥0 := R / (m ^ q : ℝ≥0)
  let rloc : ℝ := (c : ℝ)
  let PosA := (Fin q → ℝ) × A
  let PosB := (Fin q → ℝ) × B
  let encA : MarkedCloudSpace q A → BlockData PosA := blockLocalCloudEncoded (A := A) q m b
  let encB : MarkedCloudSpace q B → BlockData PosB := blockLocalCloudEncoded (A := B) q m b
  let Bnd : ℝ := rloc ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G
  have hc0 : 0 ≤ rloc := c.coe_nonneg
  -- measurability of the encoded block value
  have hEncMeas : Measurable fun ω : TwoMarkedCloudSpace q A B =>
      (encA ω.1, encB ω.2) :=
    ((measurable_blockLocalCloudEncoded (A := A) q m b).comp measurable_fst).prodMk
      ((measurable_blockLocalCloudEncoded (A := B) q m b).comp measurable_snd)
  have hΦ : Measurable fun d : BlockData PosA × BlockData PosB =>
      blockTiltedValue q rloc kin g t d.1 d.2 :=
    measurable_blockTiltedValue q rloc hc0 hC0 hG0 hkin hkin_bound hg hgb t
  have hmeasEnc : AEStronglyMeasurable (fun ω : TwoMarkedCloudSpace q A B =>
      blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2))
      (twoMarkedCloudLaw (q := q) A B α β R) :=
    (hΦ.comp hEncMeas).aestronglyMeasurable
  -- domination by the source count
  have hbound : ∀ ω : TwoMarkedCloudSpace q A B,
      |blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2)| ≤
        ((mSourceCount ω : ℕ) : ℝ) * Bnd := by
    intro ω
    have hb := abs_blockTiltedValue_le q (r := rloc) (C := C) (G := G) (t := t)
      hc0 hC0 hG0 hkin_bound hgb (encA ω.1) (encB ω.2)
    have hle : ((min (encA ω.1).1 (encB ω.2).1 : ℕ) : ℝ) ≤ (mSourceCount ω : ℝ) := by
      have h1 : (encA ω.1).1 ≤ (ω.1).1 := by
        exact blockLocalCloudEncoded_fst_le (A := A) q m b ω.1
      have h2 : ((min (encA ω.1).1 (encB ω.2).1 : ℕ) : ℝ) ≤ ((encA ω.1).1 : ℝ) := by
        exact_mod_cast min_le_left _ _
      have h3 : ((encA ω.1).1 : ℝ) ≤ (mSourceCount ω : ℝ) := by
        exact_mod_cast h1
      linarith
    have hBnd0 : 0 ≤ Bnd := by
      dsimp only [Bnd]
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg hc0 _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
        (mul_nonneg (abs_nonneg t) hG0)
    exact hb.trans (mul_le_mul_of_nonneg_right hle hBnd0)
  have hIntEnc : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2))
      (twoMarkedCloudLaw (q := q) A B α β R) := by
    have hmaj : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        ((mSourceCount ω : ℕ) : ℝ) * Bnd) (twoMarkedCloudLaw (q := q) A B α β R) :=
      (integrable_mSourceCount (q := q) α β R).mul_const Bnd
    exact hmaj.mono' hmeasEnc (by
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact hbound ω)
  -- pointwise identity on the unit cube, with raw block clouds
  have hz1ae : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β R),
      ∀ i, mSourcePoint ω i ∈ unitCubeSet q := by
    have h := ae_mem_unitCubeSet_markedPoissonLaw (q := q) (A := A) α R
    simpa only [twoMarkedCloudLaw, mSourcePoint, mSourceCount] using
      (ae_fst_of_ae (μ := markedPoissonLaw (q := q) A α R)
        (ν := markedPoissonLaw (q := q) B β R) h)
  have hz2ae : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β R),
      ∀ j, mTargetPoint ω j ∈ unitCubeSet q := by
    have h := ae_mem_unitCubeSet_markedPoissonLaw (q := q) (A := B) β R
    simpa only [twoMarkedCloudLaw, mTargetPoint, mTargetCount] using
      (ae_snd_of_ae (μ := markedPoissonLaw (q := q) A α R)
        (ν := markedPoissonLaw (q := q) B β R) h)
  have hrloc : r / ((m : ℝ) ^ q) = rloc := by
    dsimp only [rloc, c]
    rw [hrR, NNReal.coe_div]
    push_cast
    ring
  have hpoint : (fun ω : TwoMarkedCloudSpace q A B =>
        markedBlockValue q m J hm hJ r t kin g ω (blockLeafLabel q m J hJ b))
      =ᵐ[twoMarkedCloudLaw (q := q) A B α β R]
      (fun ω => blockTiltedValue q rloc kin g t
        (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)) := by
    filter_upwards [hz1ae, hz2ae] with ω hz1 hz2
    rw [markedBlockValue_eq_blockTiltedValue hm hJ hq hr hC0 hG0
      hkin_bound hkin_homog hgb b ω hz1 hz2, hrloc]
  -- raw and encoded block clouds agree
  have hrawA := blockLocalCloud_ae_eq_encoded (q := q) (m := m) (A := A) hm R α b
  have hrawB := blockLocalCloud_ae_eq_encoded (q := q) (m := m) (A := B) hm R β b
  have hraw : (fun ω : TwoMarkedCloudSpace q A B =>
        blockTiltedValue q rloc kin g t
          (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2))
      =ᵐ[twoMarkedCloudLaw (q := q) A B α β R]
      (fun ω => blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2)) := by
    have hpair : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β R),
        blockLocalCloud q m b ω.1 = encA ω.1 ∧
        blockLocalCloud q m b ω.2 = encB ω.2 := by
      have h1 := ae_fst_of_ae (μ := markedPoissonLaw (q := q) A α R)
        (ν := markedPoissonLaw (q := q) B β R) hrawA
      have h2 := ae_snd_of_ae (μ := markedPoissonLaw (q := q) A α R)
        (ν := markedPoissonLaw (q := q) B β R) hrawB
      simpa only [twoMarkedCloudLaw] using h1.and h2
    filter_upwards [hpair] with ω hω
    rw [hω.1, hω.2]
  exact hIntEnc.congr ((hpoint.trans hraw).symm)


set_option maxHeartbeats 2400000 in
/-- **Expected leaf-block sum equals `m ^ q` times the block pressure.**  For a
marked Poisson cloud of intensity `R` tiled by the `m ^ q` equal blocks of the
uniform grid hierarchy, the expected sum of the optimal leaf-block values is
`m ^ q` times the marked pressure at the per-block intensity `R / m ^ q`. -/
theorem integral_gridBlockSum_eq
    (q m J : ℕ) [NeZero m] (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hq : 0 < q)
    (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) {r t C G : ℝ} (hr : 0 ≤ r) (hrR : r = (R : ℝ))
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∫ ω : TwoMarkedCloudSpace q A B,
      (∑ c : Fin q → Fin (2 ^ J + 1),
        PartialMatching.maxCardValue
          (blockCost
            (fun i : Fin (mSourceCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
            (fun j : Fin (mTargetCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
            (fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) c))
      ∂(twoMarkedCloudLaw (q := q) A B α β R) =
      (((m ^ q : ℕ) : ℝ)) *
        markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t := by
  classical
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure α
  haveI : Nonempty B := nonempty_of_isProbabilityMeasure β
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hC0 : 0 ≤ C := by
    have h := hkin_bound (Classical.choice ‹Nonempty A›) (Classical.choice ‹Nonempty B›)
      (fun _ : Fin q => 1)
    have hsum : ∑ l : Fin q, (fun _ : Fin q => (1 : ℝ)) l ^ 2 = (q : ℝ) := by
      simp
    rw [hsum] at h
    nlinarith [abs_nonneg (kin (Classical.choice ‹Nonempty A›)
      (Classical.choice ‹Nonempty B›) (fun _ : Fin q => 1))]
  have hG0 : 0 ≤ G :=
    le_trans (abs_nonneg _)
      (hgb (Classical.choice ‹Nonempty A›) (Classical.choice ‹Nonempty B›))
  have hz1ae : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β R),
      ∀ i, mSourcePoint ω i ∈ unitCubeSet q := by
    have h := ae_mem_unitCubeSet_markedPoissonLaw (q := q) (A := A) α R
    simpa only [twoMarkedCloudLaw, mSourcePoint, mSourceCount] using
      (ae_fst_of_ae (μ := markedPoissonLaw (q := q) A α R)
        (ν := markedPoissonLaw (q := q) B β R) h)
  have hz2ae : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β R),
      ∀ j, mTargetPoint ω j ∈ unitCubeSet q := by
    have h := ae_mem_unitCubeSet_markedPoissonLaw (q := q) (A := B) β R
    simpa only [twoMarkedCloudLaw, mTargetPoint, mTargetCount] using
      (ae_snd_of_ae (μ := markedPoissonLaw (q := q) A α R)
        (ν := markedPoissonLaw (q := q) B β R) h)
  have hrloc : r / ((m : ℝ) ^ q) = ((R / ((m ^ q : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
    rw [hrR, NNReal.coe_div]
    push_cast
    ring
  have hper : ∀ b : Fin q → Fin m,
      ∫ ω : TwoMarkedCloudSpace q A B,
          markedBlockValue q m J hm hJ r t kin g ω (blockLeafLabel q m J hJ b)
        ∂(twoMarkedCloudLaw (q := q) A B α β R) =
        markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t := by
    intro b
    have hswap : (fun ω : TwoMarkedCloudSpace q A B =>
          markedBlockValue q m J hm hJ r t kin g ω (blockLeafLabel q m J hJ b))
        =ᵐ[twoMarkedCloudLaw (q := q) A B α β R]
        (fun ω : TwoMarkedCloudSpace q A B =>
          blockTiltedValue q (r / ((m : ℝ) ^ q)) kin g t
            (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)) := by
      filter_upwards [hz1ae, hz2ae] with ω hz1 hz2
      exact markedBlockValue_eq_blockTiltedValue hm hJ hq hr hC0 hG0
        hkin_bound hkin_homog hgb b ω hz1 hz2
    have hcongr : (fun ω : TwoMarkedCloudSpace q A B =>
          blockTiltedValue q (r / ((m : ℝ) ^ q)) kin g t
            (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)) =
        (fun ω : TwoMarkedCloudSpace q A B => blockTiltedValue q
          (((R / ((m ^ q : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
          (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2)) := by
      funext ω
      rw [hrloc]
    have hint : R / ((m ^ q : ℕ) : ℝ≥0) = R / (m ^ q : ℝ≥0) := by
      rw [Nat.cast_pow]
    rw [integral_congr_ae hswap, hcongr, hint]
    exact integral_blockTiltedValue_blockLocalCloud q m hm hq R α β
      (t := t) hC0 hG0 hkin hkin_bound hg hgb b
  calc
    ∫ ω : TwoMarkedCloudSpace q A B,
        (∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost
              (fun i : Fin (mSourceCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
              (fun j : Fin (mTargetCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
              (fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) c))
        ∂(twoMarkedCloudLaw (q := q) A B α β R)
        = ∫ ω : TwoMarkedCloudSpace q A B,
            (∑ b : Fin q → Fin m,
              markedBlockValue q m J hm hJ r t kin g ω
                (blockLeafLabel q m J hJ b))
            ∂(twoMarkedCloudLaw (q := q) A B α β R) := by
          apply integral_congr_ae
          filter_upwards with ω
          exact markedBlockValue_sum_eq_realBlocks hm hJ r t ω
      _ = ∑ b : Fin q → Fin m,
            ∫ ω : TwoMarkedCloudSpace q A B,
              markedBlockValue q m J hm hJ r t kin g ω
                (blockLeafLabel q m J hJ b)
            ∂(twoMarkedCloudLaw (q := q) A B α β R) := by
          rw [integral_finset_sum]
          intro b _
          exact integrable_markedBlockValue q m J hm hJ hq α β R hr hrR
            hC0 hG0 hkin hkin_bound hkin_homog hg hgb b
      _ = ∑ _b : Fin q → Fin m,
            markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t := by
          refine Finset.sum_congr rfl ?_
          intro b _
          exact hper b
      _ = (((m ^ q : ℕ) : ℝ)) *
            markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]

end OTSelector.Probability
