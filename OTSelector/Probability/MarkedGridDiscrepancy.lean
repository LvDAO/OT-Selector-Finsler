import OTSelector.Probability.MarkedBlockLaw
import OTSelector.Finite.UnitCubeGridHierarchy
import OTSelector.Probability.PoissonLabelSplittingGeneral
import OTSelector.Probability.MarkedBlockComparison

/-!
# Expected grid-cell discrepancy of marked Poisson clouds

For the two-cloud marked Poisson model of intensity `R` on the unit cube, this
module bounds the expected total absolute discrepancy of the level-`k` cells of
the uniform `m`-grid hierarchy by `sqrt (2 * R * (#cells))`, where the number of
cells is `(2 ^ k + 1) ^ q`.

The hierarchy is encoded through the leaf labels `blockLabelFin q m` of the
uniform `m`-grid: a leaf index `a < m` is assigned to the level-`k` cell
`a / 2 ^ (J - k)`, using the hypothesis `m ≤ 2 ^ J` (so that the `2 ^ J`-fold
dyadic refinement is finer than the `m`-grid).  The codomain `Fin (2 ^ k + 1)`
carries one slack element, which makes the definition work uniformly for all
`k`, including `k > J`.  The resulting cell label is a coarsening of the leaf
label: it is a function of `blockLabelFin q m` only.

The estimate is obtained from the abstract grouping bound
`integral_grouped_label_discrepancy_le` of `PoissonLabelSplittingGeneral`.  The
marks are integrated out first, using
`map_markedPosCloud_twoMarkedCloudLaw` and the fact that almost every point of
a marked Poisson cloud lies in the unit cube, where coordinatewise truncation
is the identity.  The leaf labels of the position sequence are independent and
uniform on `Fin (m ^ q)`, so the abstract splitting law applies with label
probabilities `1 / m ^ q`.  Grouping the `m ^ q` leaf labels into the
`(2 ^ k + 1) ^ q` cells and comparing two independent samples gives the
square-root bound.

The cell labels are those of `MarkedGridHierarchy`: `gridLeaf` is the leaf
block of one coordinate and `gridCellLabel` is the padded level-`k` label.  The
only auxiliary map defined here is `gridDiscCellCode`, which transports a leaf
block code `Fin (m ^ q)` to the encoded cell label; it agrees with
`gridCellLabel` on the unit cube.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open OTSelector.Reconstruction

-- Local instances of the form `haveI` are needed for instance search.
set_option linter.style.haveILetI false

noncomputable section
namespace OTSelector.Probability

/-! ## The level-`k` cells of the uniform `m`-grid hierarchy -/

/-- The level-`k` cell of a leaf block label: the leaf index is divided by
`2 ^ (J - k)`.  The codomain `Fin (2 ^ k + 1)` is large enough for every
`k`, including `k > J`, because the extra slack element absorbs the case where
the dyadic refinement is coarser than the leaf grid. -/
def gridDiscCellOfLeaf (q m J k : ℕ) (_hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (b : Fin q → Fin m) : Fin q → Fin (2 ^ k + 1) :=
  fun l => ⟨(b l).val / 2 ^ (J - k), by
    have hb : (b l).val < m := (b l).isLt
    by_cases hkJ : k ≤ J
    · have hdiv : 0 < 2 ^ (J - k) := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
      have hpow : 2 ^ (J - k) * 2 ^ k = 2 ^ J := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hkJ]
      have hlt : (b l).val < 2 ^ (J - k) * 2 ^ k := by
        rw [hpow]
        exact lt_of_lt_of_le hb hJ
      have h2 : (b l).val / 2 ^ (J - k) < 2 ^ k := Nat.div_lt_of_lt_mul hlt
      omega
    · have hzero : J - k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_le hkJ)
      rw [hzero, pow_zero, Nat.div_one]
      have h1 : (b l).val < 2 ^ J := lt_of_lt_of_le hb hJ
      have h2 : 2 ^ J ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_le hkJ)
      omega⟩

theorem measurable_gridLeaf (m : ℕ) (hm : 0 < m) : Measurable (gridLeaf m hm) := by
  apply measurable_to_countable'
  intro a
  change MeasurableSet {x : ℝ | gridLeaf m hm x = a}
  have hpre : {x : ℝ | gridLeaf m hm x = a} =
      {x : ℝ | ⌊(m : ℝ) * x⌋₊ % m = (a : ℕ)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have := congrArg Fin.val h
      simpa only [gridLeaf] using this
    · intro h
      exact Fin.ext (by simpa only [gridLeaf] using h)
  rw [hpre]
  exact (measurableSet_singleton (a : ℕ)).preimage
    ((measurable_of_countable (fun n : ℕ => n % m)).comp
      (Nat.measurable_floor.comp (measurable_const.mul measurable_id)))

/-- On the unit interval the leaf block `gridLeaf` is the `Fin m`-valued block
index `blockIndexFin`. -/
theorem gridLeaf_eq_blockIndexFin {m : ℕ} [NeZero m] (hm : 0 < m) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    gridLeaf m hm x = blockIndexFin m x := by
  apply Fin.ext
  rw [gridLeaf_val_of_mem hm hx.1.le hx.2,
    blockIndexFin_apply (blockIndex_inv_lt (m := m) hx.1.le hx.2)]
  show ⌊(m : ℝ) * x⌋₊ = blockIndex ((m : ℝ)⁻¹) x
  unfold blockIndex
  rw [div_inv_eq_mul, mul_comm]

/-- On the unit cube the padded cell label `gridCellLabel` of
`MarkedGridHierarchy` coincides with the leaf-code cell label
`gridDiscCellOfLeaf`. -/
theorem gridCellLabel_eq_gridDiscCellOfLeaf (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) {x : Fin q → ℝ} (hx : x ∈ unitCube q) :
    gridCellLabel q m J k hm hJ x =
      gridDiscCellOfLeaf q m J k hm hJ (blockLabelFin q m x) := by
  funext l
  apply Fin.ext
  show (gridLeaf m hm (x l)).val / 2 ^ (J - k) =
    (blockLabelFin q m x l).val / 2 ^ (J - k)
  rw [gridLeaf_eq_blockIndexFin hm (Set.mem_pi.mp hx l (Set.mem_univ l))]
  rfl

/-- The padded cell label is measurable. -/
theorem measurable_gridCellLabel_coord (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (l : Fin q) :
    Measurable (fun x : Fin q → ℝ => gridCellLabel q m J k hm hJ x l) := by
  apply measurable_to_countable'
  intro c
  change MeasurableSet {x : Fin q → ℝ | gridCellLabel q m J k hm hJ x l = c}
  have hpre : {x : Fin q → ℝ | gridCellLabel q m J k hm hJ x l = c} =
      {x : Fin q → ℝ | (gridLeaf m hm (x l)).val / 2 ^ (J - k) = (c : ℕ)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      exact Fin.ext h
  rw [hpre]
  exact (measurableSet_singleton (c : ℕ)).preimage
    ((measurable_of_countable (fun n : ℕ => n / 2 ^ (J - k))).comp
      ((measurable_of_countable (fun a : Fin m => a.val)).comp
        ((measurable_gridLeaf m hm).comp (measurable_pi_apply l))))

theorem measurable_gridCellLabel (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J) :
    Measurable (gridCellLabel q m J k hm hJ) :=
  measurable_pi_lambda _ (fun l => measurable_gridCellLabel_coord q m J k hm hJ l)

/-- The encoding of the level-`k` grid cell label of a leaf block into
`Fin ((2 ^ k + 1) ^ q)`, through `finFunctionFinEquiv`. -/
def gridDiscCellCode (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (b : Fin (m ^ q)) : Fin ((2 ^ k + 1) ^ q) :=
  finFunctionFinEquiv (gridDiscCellOfLeaf q m J k hm hJ (finFunctionFinEquiv.symm b))

theorem measurable_gridDiscCellCode (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J) :
    Measurable (gridDiscCellCode q m J k hm hJ) :=
  measurable_of_countable _

/-- On the unit cube, the encoded cell label of a point is the encoding of its
padded cell label. -/
theorem gridDiscCellCode_blockLabelCode (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) {x : Fin q → ℝ} (hx : x ∈ unitCube q) :
    gridDiscCellCode q m J k hm hJ (blockLabelCode q m x) =
      finFunctionFinEquiv (gridCellLabel q m J k hm hJ x) := by
  unfold gridDiscCellCode blockLabelCode
  rw [Equiv.symm_apply_apply, gridCellLabel_eq_gridDiscCellOfLeaf q m J k hm hJ hx]

/-- On the unit cube, the leaf cell label equals `c` exactly when the encoded
leaf cell label equals the encoded cell `c`. -/
theorem gridDiscCellCode_blockLabelCode_eq_iff (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) {x : Fin q → ℝ} (hx : x ∈ unitCube q)
    (c : Fin q → Fin (2 ^ k + 1)) :
    gridDiscCellCode q m J k hm hJ (blockLabelCode q m x) = finFunctionFinEquiv c ↔
      gridCellLabel q m J k hm hJ x = c := by
  rw [gridDiscCellCode_blockLabelCode q m J k hm hJ hx, Equiv.apply_eq_iff_eq]

/-! ## Discrepancy functionals -/

/-- The total absolute discrepancy of the level-`k` grid cell counts of two
marked clouds, in the form used by the main theorem (with coordinates truncated
to the unit cube). -/
noncomputable def gridDiscMarkedDiscrepancy (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  ∑ c : Fin q → Fin (2 ^ k + 1),
    |(partitionCount (gridCellLabel q m J k hm hJ ∘ markedTruncSource q ω) c : ℝ) -
      (partitionCount (gridCellLabel q m J k hm hJ ∘ markedTruncTarget q ω) c : ℝ)|

/-- The total absolute discrepancy of the level-`k` grid cell counts of the two
position clouds of an unmarked sample. -/
noncomputable def gridDiscCloudDiscrepancy (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (z : TwoCloudSpace q) : ℝ :=
  ∑ c : Fin q → Fin (2 ^ k + 1),
    |(partitionCount (gridCellLabel q m J k hm hJ ∘
          (fun i : Fin (z.1.1) => z.1.2 (i : ℕ))) c : ℝ) -
      (partitionCount (gridCellLabel q m J k hm hJ ∘
          (fun j : Fin (z.2.1) => z.2.2 (j : ℕ))) c : ℝ)|

/-! ## Measurability -/

theorem measurable_gridDiscMarkedDiscrepancy (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] :
    Measurable (gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
      (hm := hm) (hJ := hJ) (A := A) (B := B)) := by
  classical
  unfold gridDiscMarkedDiscrepancy
  apply Finset.measurable_sum
  intro c _
  apply Measurable.comp continuous_abs.measurable
  apply Measurable.sub
  · simp only [partitionCount_eq_card_filter]
    exact Measurable.comp measurable_from_nat
      (measurable_prefixCount_eq
        (fun ω : TwoMarkedCloudSpace q A B => mSourceCount ω)
        (measurable_mSourceCount q)
        (fun i (ω : TwoMarkedCloudSpace q A B) =>
          gridCellLabel q m J k hm hJ (cubeTruncPoint (mSourcePoint ω i)))
        (fun i => (measurable_gridCellLabel q m J k hm hJ).comp
          (measurable_pi_lambda
            (fun (ω : TwoMarkedCloudSpace q A B) => cubeTruncPoint (mSourcePoint ω i))
            (fun l => (measurable_cubeTruncPoint_apply q l).comp
              (measurable_mSourcePoint q i))))
        c)
  · simp only [partitionCount_eq_card_filter]
    exact Measurable.comp measurable_from_nat
      (measurable_prefixCount_eq
        (fun ω : TwoMarkedCloudSpace q A B => mTargetCount ω)
        (measurable_mTargetCount q)
        (fun i (ω : TwoMarkedCloudSpace q A B) =>
          gridCellLabel q m J k hm hJ (cubeTruncPoint (mTargetPoint ω i)))
        (fun i => (measurable_gridCellLabel q m J k hm hJ).comp
          (measurable_pi_lambda
            (fun (ω : TwoMarkedCloudSpace q A B) => cubeTruncPoint (mTargetPoint ω i))
            (fun l => (measurable_cubeTruncPoint_apply q l).comp
              (measurable_mTargetPoint q i))))
        c)

theorem measurable_gridDiscCloudDiscrepancy (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) :
    Measurable (gridDiscCloudDiscrepancy q m J k hm hJ) := by
  classical
  unfold gridDiscCloudDiscrepancy
  apply Finset.measurable_sum
  intro c _
  apply Measurable.comp continuous_abs.measurable
  apply Measurable.sub
  · simp only [partitionCount_eq_card_filter]
    exact Measurable.comp measurable_from_nat
      (measurable_prefixCount_eq
        (fun z : TwoCloudSpace q => z.1.1) (measurable_fst.comp measurable_fst)
        (fun i (z : TwoCloudSpace q) => gridCellLabel q m J k hm hJ (z.1.2 i))
        (fun i => (measurable_gridCellLabel q m J k hm hJ).comp
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)))
        c)
  · simp only [partitionCount_eq_card_filter]
    exact Measurable.comp measurable_from_nat
      (measurable_prefixCount_eq
        (fun z : TwoCloudSpace q => z.2.1) (measurable_fst.comp measurable_snd)
        (fun i (z : TwoCloudSpace q) => gridCellLabel q m J k hm hJ (z.2.2 i))
        (fun i => (measurable_gridCellLabel q m J k hm hJ).comp
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))
        c)

/-! ## Removing the truncation and the marks -/

/-- Almost everywhere, coordinatewise truncation is the identity, so the marked
truncated discrepancy is the discrepancy of the position projection. -/
theorem gridDiscMarkedDiscrepancy_eq_cloud_ae (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (R : ℝ≥0) :
    (fun ω => gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
        (hm := hm) (hJ := hJ) (A := A) (B := B) ω)
      =ᵐ[twoMarkedCloudLaw (q := q) A B α β R]
    (fun ω => gridDiscCloudDiscrepancy q m J k hm hJ
      (markedPosCloud (q := q) (A := A) (B := B) ω)) := by
  filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw (q := q) α β R] with ω hω
  unfold gridDiscMarkedDiscrepancy gridDiscCloudDiscrepancy
  have hsrc : markedTruncSource q ω =
      fun i : Fin (mSourceCount ω) => mSourcePoint ω (i : ℕ) := by
    funext i
    exact cubeTruncPoint_eq_of_mem (hω.1 (i : ℕ))
  have htgt : markedTruncTarget q ω =
      fun j : Fin (mTargetCount ω) => mTargetPoint ω (j : ℕ) := by
    funext j
    exact cubeTruncPoint_eq_of_mem (hω.2 (j : ℕ))
  simp only [hsrc, htgt, markedPosCloud, markedPosition, mSourcePoint, mTargetPoint]
  rfl

/-! ## The abstract cell count form -/

/-- The unmarked discrepancy written as cardinalities of cell filters for the
encoded cell labels, which is the form produced by the abstract grouping
bound. -/
theorem gridDiscCloudDiscrepancy_eq_cardFilters (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (z : TwoCloudSpace q)
    (hsrc_mem : ∀ i, sourcePoint z i ∈ unitCube q)
    (htgt_mem : ∀ j, targetPoint z j ∈ unitCube q) :
    gridDiscCloudDiscrepancy q m J k hm hJ z =
      ∑ c : Fin ((2 ^ k + 1) ^ q),
        |((Finset.univ.filter (fun i : Fin (z.1.1) =>
              gridDiscCellCode q m J k hm hJ (blockLabelCode q m (z.1.2 (i : ℕ))) = c)).card : ℝ) -
          ((Finset.univ.filter (fun j : Fin (z.2.1) =>
              gridDiscCellCode q m J k hm hJ (blockLabelCode q m (z.2.2 (j : ℕ))) = c)).card : ℝ)| := by
  classical
  let e : (Fin q → Fin (2 ^ k + 1)) ≃ Fin ((2 ^ k + 1) ^ q) := finFunctionFinEquiv
  unfold gridDiscCloudDiscrepancy
  let F : (Fin q → Fin (2 ^ k + 1)) → ℝ := fun c =>
    |(partitionCount (gridCellLabel q m J k hm hJ ∘
        (fun i : Fin (z.1.1) => z.1.2 (i : ℕ))) c : ℝ) -
      (partitionCount (gridCellLabel q m J k hm hJ ∘
        (fun j : Fin (z.2.1) => z.2.2 (j : ℕ))) c : ℝ)|
  let G : Fin ((2 ^ k + 1) ^ q) → ℝ := fun c =>
    |((Finset.univ.filter (fun i : Fin (z.1.1) =>
          gridDiscCellCode q m J k hm hJ (blockLabelCode q m (z.1.2 (i : ℕ))) = c)).card : ℝ) -
      ((Finset.univ.filter (fun j : Fin (z.2.1) =>
          gridDiscCellCode q m J k hm hJ (blockLabelCode q m (z.2.2 (j : ℕ))) = c)).card : ℝ)|
  have hFG : ∀ c, F c = G (e c) := by
    intro c
    have hsrc : (Finset.univ.filter (fun i : Fin (z.1.1) =>
          gridCellLabel q m J k hm hJ (z.1.2 (i : ℕ)) = c))
        = (Finset.univ.filter (fun i : Fin (z.1.1) =>
          gridDiscCellCode q m J k hm hJ (blockLabelCode q m (z.1.2 (i : ℕ))) = e c)) := by
      apply Finset.filter_congr
      intro i _
      exact (gridDiscCellCode_blockLabelCode_eq_iff q m J k hm hJ
        (hsrc_mem (i : ℕ)) c).symm
    have htgt : (Finset.univ.filter (fun j : Fin (z.2.1) =>
          gridCellLabel q m J k hm hJ (z.2.2 (j : ℕ)) = c))
        = (Finset.univ.filter (fun j : Fin (z.2.1) =>
          gridDiscCellCode q m J k hm hJ (blockLabelCode q m (z.2.2 (j : ℕ))) = e c)) := by
      apply Finset.filter_congr
      intro j _
      exact (gridDiscCellCode_blockLabelCode_eq_iff q m J k hm hJ
        (htgt_mem (j : ℕ)) c).symm
    dsimp only [F, G]
    simp only [Function.comp_apply, partitionCount_eq_card_filter, hsrc, htgt]
  simpa only [F, G] using Fintype.sum_equiv e F G hFG

/-! ## The uniform law of the leaf labels -/

/-- The uniform measure on `Fin K` is the sum of the Dirac masses with equal
weights `1 / K`. -/
theorem uniformMeasure_eq_sum_inv_smul_dirac (K : ℕ) [NeZero K] :
    uniformMeasure (Fin K) =
      Measure.sum (fun b : Fin K => (((K : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • Measure.dirac b) := by
  classical
  have hK : ((K : ℝ≥0)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  refine Measure.ext_of_singleton (fun c => ?_)
  rw [uniformMeasure_singleton, Measure.sum_apply _ (measurableSet_singleton c),
    tsum_eq_single c]
  · rw [Measure.smul_apply, Measure.dirac_apply]
    simp [ENNReal.coe_inv hK]
  · intro b hb
    rw [Measure.smul_apply, Measure.dirac_apply]
    simp [hb]

/-! ## The main bound -/

set_option maxHeartbeats 800000 in
/-- **Expected grid-cell discrepancy bound.**  For the two-cloud marked Poisson
model of intensity `R` on the unit cube, the expected total absolute discrepancy
of the level-`k` cells of the uniform `m`-grid hierarchy is at most
`sqrt (2 * R * (2 ^ k + 1) ^ q)`, where `(2 ^ k + 1) ^ q` is the number of
cells. -/
theorem integral_markedGridDiscrepancy_le
    (q m J k : ℕ) [NeZero m] (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) :
    ∫ ω : TwoMarkedCloudSpace q A B,
      (∑ c : Fin q → Fin (2 ^ k + 1),
        |(partitionCount ((gridCellLabel q m J k hm hJ) ∘
              (fun i : Fin (mSourceCount ω) =>
                cubeTruncPoint (mSourcePoint ω (i : ℕ)))) c : ℝ) -
         (partitionCount ((gridCellLabel q m J k hm hJ) ∘
              (fun j : Fin (mTargetCount ω) =>
                cubeTruncPoint (mTargetPoint ω (j : ℕ)))) c : ℝ)|)
      ∂(twoMarkedCloudLaw (q := q) A B α β R)
    ≤ Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
  classical
  haveI hKne : NeZero (m ^ q) := ⟨pow_ne_zero q (NeZero.ne m)⟩
  haveI hMne : NeZero ((2 ^ k + 1) ^ q) := ⟨pow_ne_zero q (Nat.succ_ne_zero _)⟩
  -- The label probabilities: every leaf block has mass `1 / m ^ q`.
  have hp : ∑ b : Fin (m ^ q), ((m ^ q : ℝ≥0)⁻¹) = 1 := by
    have hne : ((m : ℝ≥0) ^ q) ≠ 0 :=
      pow_ne_zero q (Nat.cast_ne_zero.mpr (NeZero.ne m))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow]
    exact mul_inv_cancel₀ hne
  have hN : (poissonCubeLaw q R).map (fun z : PoissonCloudSpace q => z.1) = poissonMeasure R := by
    unfold poissonCubeLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  -- Independence of the leaf labels along the position sequence.
  have hseq : iIndepFun (fun (i : ℕ) (s : ℕ → (Fin q → ℝ)) => blockLabelCode q m (s i))
      (cubeSeqLaw q) := by
    haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
      isProbabilityMeasure_cubeMeasure (by norm_num)
    unfold cubeSeqLaw
    exact iIndepFun_infinitePi_apply_comp (cubeMeasure (Fin q) 1)
      (blockLabelCode q m) (measurable_blockLabelCode q m)
  have hw : ∀ n, iIndepFun (fun i : Fin n => fun z : PoissonCloudSpace q =>
      blockLabelCode q m (z.2 i)) (poissonCubeLaw q R) := by
    intro n
    have hfin : iIndepFun (fun i : Fin n => fun s : ℕ → (Fin q → ℝ) =>
        blockLabelCode q m (s i)) (cubeSeqLaw q) :=
      hseq.precomp (g := fun i : Fin n => (i : ℕ)) (fun a b hab => Fin.ext hab)
    unfold poissonCubeLaw
    exact iIndepFun_snd_prod (ν₁ := poissonMeasure R) (ν₂ := cubeSeqLaw q)
      (Y := fun i : Fin n => fun s : ℕ → (Fin q → ℝ) => blockLabelCode q m (s i))
      (fun i => (measurable_blockLabelCode q m).comp (measurable_pi_apply (i : ℕ))) hfin
  -- The law of each leaf label is uniform on the `m ^ q` leaf blocks.
  have hlaw_uniform : ∀ i : ℕ,
      (poissonCubeLaw q R).map (fun z : PoissonCloudSpace q =>
        blockLabelCode q m (z.2 i)) = uniformMeasure (Fin (m ^ q)) := by
    intro i
    haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
      isProbabilityMeasure_cubeMeasure (by norm_num)
    have hmpi := measurePreserving_eval_infinitePi
      (μ := fun _ : ℕ => cubeMeasure (Fin q) 1)
      (hμ := fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)) i
    have hmarg : (cubeSeqLaw q).map (fun x : ℕ → (Fin q → ℝ) =>
        blockLabelCode q m (x i)) = uniformMeasure (Fin (m ^ q)) := by
      have h1 : (fun x : ℕ → (Fin q → ℝ) => blockLabelCode q m (x i)) =
          blockLabelCode q m ∘ Function.eval i := rfl
      rw [h1, ← Measure.map_map (measurable_blockLabelCode q m) hmpi.measurable]
      unfold cubeSeqLaw
      rw [hmpi.map_eq, map_blockLabelCode_cubeMeasure q m hm]
    have hg : Measurable (fun x : ℕ → (Fin q → ℝ) => blockLabelCode q m (x i)) :=
      (measurable_blockLabelCode q m).comp (measurable_pi_apply i)
    have hpull : (poissonCubeLaw q R).map (fun z : PoissonCloudSpace q =>
        blockLabelCode q m (z.2 i)) =
        (cubeSeqLaw q).map (fun x : ℕ → (Fin q → ℝ) => blockLabelCode q m (x i)) := by
      rw [show (fun z : PoissonCloudSpace q => blockLabelCode q m (z.2 i)) =
          (fun x : ℕ → (Fin q → ℝ) => blockLabelCode q m (x i)) ∘ Prod.snd from rfl,
        ← Measure.map_map hg measurable_snd]
      unfold poissonCubeLaw
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hpull.trans hmarg
  have hlaw : ∀ i : ℕ,
      (poissonCubeLaw q R).map (fun z : PoissonCloudSpace q => blockLabelCode q m (z.2 i)) =
        Measure.sum (fun b : Fin (m ^ q) =>
          (((m ^ q : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • Measure.dirac b) := by
    intro i
    rw [hlaw_uniform i]
    simpa only [Nat.cast_pow] using (uniformMeasure_eq_sum_inv_smul_dirac (m ^ q))
  -- The Poisson count is independent of the label sequence.
  have hindep : ∀ n, IndepFun (fun z : PoissonCloudSpace q => z.1)
      (fun z => fun i : Fin n => blockLabelCode q m (z.2 i)) (poissonCubeLaw q R) := by
    intro n
    have hY : Measurable (fun x : ℕ → (Fin q → ℝ) =>
        fun i : Fin n => blockLabelCode q m (x i)) :=
      measurable_pi_lambda _ fun i =>
        (measurable_blockLabelCode q m).comp (measurable_pi_apply (i : ℕ))
    have h := indepFun_prod (μ := poissonMeasure R) (ν := cubeSeqLaw q)
      (X := fun n : ℕ => n)
      (Y := fun x : ℕ → (Fin q → ℝ) => fun i : Fin n => blockLabelCode q m (x i))
      measurable_id hY
    unfold poissonCubeLaw
    exact h
  -- The abstract grouping bound.
  have hmain := integral_grouped_label_discrepancy_le
    (Ω := PoissonCloudSpace q) (P := poissonCubeLaw q R)
    (K := m ^ q) (M := (2 ^ k + 1) ^ q)
    (Λ := R) (N := fun z : PoissonCloudSpace q => z.1)
    (w := fun i z => blockLabelCode q m (z.2 i))
    (f := gridDiscCellCode q m J k hm hJ)
    (p := fun _ => (m ^ q : ℝ≥0)⁻¹) hp hN hw hlaw hindep
  -- Remove the truncation and the marks.
  have hmarked :
      ∫ ω, gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
          (hm := hm) (hJ := hJ) (A := A) (B := B) ω
        ∂(twoMarkedCloudLaw (q := q) A B α β R)
        = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R) := by
    calc
      ∫ ω, gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
            (hm := hm) (hJ := hJ) (A := A) (B := B) ω
          ∂(twoMarkedCloudLaw (q := q) A B α β R)
          = ∫ ω, gridDiscCloudDiscrepancy q m J k hm hJ
                (markedPosCloud (q := q) (A := A) (B := B) ω)
              ∂(twoMarkedCloudLaw (q := q) A B α β R) :=
            integral_congr_ae (gridDiscMarkedDiscrepancy_eq_cloud_ae q m J k hm hJ A B α β R)
      _ = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z
              ∂((twoMarkedCloudLaw (q := q) A B α β R).map
                (markedPosCloud (q := q) (A := A) (B := B))) :=
            (integral_map (measurable_markedPosCloud q).aemeasurable
              (measurable_gridDiscCloudDiscrepancy q m J k hm hJ).aestronglyMeasurable).symm
      _ = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R) := by
            rw [map_markedPosCloud_twoMarkedCloudLaw (q := q) α β R]
  -- Identify the cloud discrepancy with the abstract cell-count expression.
  have hcloud :
      ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R)
        = ∫ z : PoissonCloudSpace q × PoissonCloudSpace q,
            (∑ c : Fin ((2 ^ k + 1) ^ q),
              |((Finset.univ.filter (fun i : Fin (z.1.1) =>
                    gridDiscCellCode q m J k hm hJ
                      (blockLabelCode q m (z.1.2 (i : ℕ))) = c)).card : ℝ) -
                 ((Finset.univ.filter (fun j : Fin (z.2.1) =>
                    gridDiscCellCode q m J k hm hJ
                      (blockLabelCode q m (z.2.2 (j : ℕ))) = c)).card : ℝ)|)
            ∂((poissonCubeLaw q R).prod (poissonCubeLaw q R)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_points_mem_unitCube_twoCloudLaw (q := q) R] with z hz
    exact gridDiscCloudDiscrepancy_eq_cardFilters q m J k hm hJ z hz.1 hz.2
  change ∫ ω : TwoMarkedCloudSpace q A B,
      gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
        (hm := hm) (hJ := hJ) (A := A) (B := B) ω
      ∂(twoMarkedCloudLaw (q := q) A B α β R)
    ≤ Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ))
  calc
    ∫ ω, gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
          (hm := hm) (hJ := hJ) (A := A) (B := B) ω
        ∂(twoMarkedCloudLaw (q := q) A B α β R)
        = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R) := hmarked
    _ = ∫ z : PoissonCloudSpace q × PoissonCloudSpace q,
          (∑ c : Fin ((2 ^ k + 1) ^ q),
            |((Finset.univ.filter (fun i : Fin (z.1.1) =>
                  gridDiscCellCode q m J k hm hJ
                    (blockLabelCode q m (z.1.2 (i : ℕ))) = c)).card : ℝ) -
               ((Finset.univ.filter (fun j : Fin (z.2.1) =>
                  gridDiscCellCode q m J k hm hJ
                    (blockLabelCode q m (z.2.2 (j : ℕ))) = c)).card : ℝ)|)
          ∂((poissonCubeLaw q R).prod (poissonCubeLaw q R)) := hcloud
    _ ≤ Real.sqrt (2 * (R : ℝ) * (Fintype.card (Fin ((2 ^ k + 1) ^ q)) : ℝ)) := hmain
    _ = Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
          simp only [Fintype.card_fin]

end OTSelector.Probability
