import OTSelector.Finite.MaxCardValueScaling
import OTSelector.Probability.MarkedBlockComparison
import OTSelector.Finite.UnitCubeGridHierarchy
import OTSelector.Probability.MarkedBlockLaw
import OTSelector.Probability.MarkedGridDiscrepancy

/-!
# Deterministic block comparison for an arbitrary block count

The dyadic block comparison of `MarkedBlockComparison` uses `2 ^ J` leaf
blocks.  The pressure block-subadditivity argument needs `m` leaf blocks per
side for every natural `m`.  This module repeats the deterministic comparison
with the uniform `m`-grid hierarchy of `MarkedGridHierarchy`, whose level-`k`
cells are indexed by `Fin q → Fin (2 ^ k + 1)` and have side at most
`4 * 2 ^ (-k)`.  The kinetic repair weight therefore carries the constant
`16` instead of `4`.
-/

open scoped BigOperators NNReal
open MeasureTheory

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The kinetic part of the level-`k` grid repair weight. -/
noncomputable def markedGridRepairWeight (q : ℕ) (r C : ℝ) (k : ℕ) : ℝ :=
  16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1)

/-- The grid cost bound at one repair level, including the probe shift. -/
noncomputable def markedGridRepairBound (q : ℕ) (r C t G : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else markedGridRepairWeight q r C k + 2 * |t| * G

/-- The level-`k` grid discrepancy of a marked cloud. -/
noncomputable def markedGridDiscrepancy (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  cellDiscrepancy (gridCellLabel q m J k hm hJ)
    (markedTruncSource q ω) (markedTruncTarget q ω)

/-- Kinetic edge bound for two points sharing a level-`k` grid cell. -/
theorem kinetic_markedEdge_le_of_same_gridCell
    (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    (hk : k ≤ J) {r C : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (a : A) (b : B) {x y : Fin q → ℝ}
    (hx : ∀ l, 0 ≤ x l ∧ x l < 1) (hy : ∀ l, 0 ≤ y l ∧ y l < 1)
    (hcell : gridCellLabel q m J k hm hJ x = gridCellLabel q m J k hm hJ y) :
    r ^ (2 / (q : ℝ)) * kin a b (fun l => y l - x l) ≤
      16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k := by
  have hsq : ∑ l, (x l - y l) ^ 2 ≤ 16 * (q : ℝ) * (1 / 4 : ℝ) ^ k :=
    gridCellLabel_sqDist_le hm hJ hJ2 hk hx hy hcell
  have hsq' : ∑ l, (fun l => y l - x l) l ^ 2 = ∑ l, (x l - y l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hb := hkin_bound a b (fun l => y l - x l)
  have hkinle : kin a b (fun l => y l - x l) ≤
      C * (16 * (q : ℝ) * (1 / 4 : ℝ) ^ k) := by
    calc kin a b (fun l => y l - x l)
        ≤ |kin a b (fun l => y l - x l)| := le_abs_self _
      _ ≤ C * ∑ l, (fun l => y l - x l) l ^ 2 := hb
      _ = C * ∑ l, (x l - y l) ^ 2 := by rw [hsq']
      _ ≤ C * (16 * (q : ℝ) * (1 / 4 : ℝ) ^ k) := by
          have := mul_le_mul_of_nonneg_left hsq hC0
          nlinarith
  have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  have hbase : (0 : ℝ) ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) * (1 / 4 : ℝ) ^ k :=
    mul_nonneg
      (mul_nonneg hrpow (mul_nonneg hC0 (Nat.cast_nonneg q)))
      (pow_nonneg (by norm_num) k)
  calc r ^ (2 / (q : ℝ)) * kin a b (fun l => y l - x l)
      ≤ r ^ (2 / (q : ℝ)) * (C * (16 * (q : ℝ) * (1 / 4 : ℝ) ^ k)) :=
        mul_le_mul_of_nonneg_left hkinle hrpow
    _ = 16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k := by ring

set_option maxHeartbeats 400000 in
/-- Deterministic grid block comparison for an arbitrary block count. -/
theorem markedTilted_le_gridBlockSum_add_repair
    (q m J : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    {r t C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (ω : TwoMarkedCloudSpace q A B) :
    markedTilted q r kin g t ω ≤
      (∑ c : Fin q → Fin (2 ^ J + 1),
        PartialMatching.maxCardValue
          (blockCost (fun i : Fin (mSourceCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
            (fun j : Fin (mTargetCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
            (fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) c))
      + ∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy q m J k hm hJ ω -
              markedGridDiscrepancy q m J (k - 1) hm hJ ω) := by
  classical
  let x : Fin (mSourceCount ω) → (Fin q → ℝ) := markedTruncSource q ω
  let y : Fin (mTargetCount ω) → (Fin q → ℝ) := markedTruncTarget q ω
  let cell : (k : ℕ) → (Fin q → ℝ) → (Fin q → Fin (2 ^ k + 1)) :=
    fun k v => gridCellLabel q m J k hm hJ v
  let edge : Fin (mSourceCount ω) → Fin (mTargetCount ω) → ℝ :=
    fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)
  let cost : Fin (mSourceCount ω) → Fin (mTargetCount ω) → ℝ :=
    fun i j => edge i j + |t| * G
  have hcost_nonneg : ∀ i j, 0 ≤ cost i j := by
    intro i j
    have hk : 0 ≤ mKineticCost q r kin ω (i : ℕ) (j : ℕ) := by
      unfold mKineticCost
      exact mul_nonneg (Real.rpow_nonneg hr _) (hkin_nonneg _ _ _)
    have hpl := probe_mul_le (A := A) (B := B) t (g := g) (G := G) hgb
      (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
    have hneg2 : -(t * mProbe g ω (i : ℕ) (j : ℕ)) ≤ |t| * G := by
      have h' := probe_mul_le (A := A) (B := B) (-t) (g := g) (G := G) hgb
        (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
      simpa only [mProbe, neg_mul, abs_neg] using h'
    have he : cost i j = mKineticCost q r kin ω (i : ℕ) (j : ℕ) +
        t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G := by
      unfold cost edge markedEdgeCost
      ring
    rw [he]
    linarith
  have hB : ∀ (k : ℕ), k < J → ∀ i j,
      cell k (x i) = cell k (y j) →
        cost i j ≤ markedGridRepairBound q r C t G (k + 1) := by
    intro k hkJ i j hcell
    simp only [cell] at hcell
    have hx : ∀ l, 0 ≤ x i l ∧ x i l < 1 := fun l =>
      cubeTruncPoint_mem (mSourcePoint ω (i : ℕ)) l
    have hy : ∀ l, 0 ≤ y j l ∧ y j l < 1 := fun l =>
      cubeTruncPoint_mem (mTargetPoint ω (j : ℕ)) l
    have hkin := kinetic_markedEdge_le_of_same_gridCell (q := q) (m := m) (J := J) (k := k)
      hm hJ hJ2 (Nat.le_of_lt hkJ) (r := r) (C := C) hr hC0 hkin_bound
      (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ)) hx hy hcell
    have hprobe := probe_mul_le (A := A) (B := B) t (g := g) (G := G) hgb
      (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
    have hbk : markedGridRepairBound q r C t G (k + 1) =
        16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k + 2 * |t| * G := by
      simp only [markedGridRepairBound, markedGridRepairWeight, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel]
    have he : cost i j = r ^ (2 / (q : ℝ)) *
        kin (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
          (mDisplacement (mSourcePoint ω (i : ℕ)) (mTargetPoint ω (j : ℕ))) +
        t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G := by
      unfold cost edge markedEdgeCost mKineticCost
      ring
    rw [hbk, he]
    change r ^ (2 / (q : ℝ)) * kin (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
        (fun l => cubeTruncPoint (mTargetPoint ω (j : ℕ)) l -
          cubeTruncPoint (mSourcePoint ω (i : ℕ)) l) +
        t * g (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ)) + |t| * G ≤
      16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k + 2 * |t| * G
    have hkin' : r ^ (2 / (q : ℝ)) * kin (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
        (fun l => cubeTruncPoint (mTargetPoint ω (j : ℕ)) l -
          cubeTruncPoint (mSourcePoint ω (i : ℕ)) l) ≤
        16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k := hkin
    linarith [hkin', hprobe]
  have hroot : ∀ u v : Fin q → ℝ, cell 0 u = cell 0 v := by
    intro u v
    simpa only [cell] using gridCellLabel_root hm hJ u v
  have hnested : ∀ (k l : ℕ), k ≤ l → ∀ u v : Fin q → ℝ,
      cell l u = cell l v → cell k u = cell k v := by
    intro k l hkl u v h
    by_cases hlJ : l ≤ J
    · exact gridCellLabel_nested hm hJ hkl hlJ h
    · have hJl : J ≤ l := le_of_lt (lt_of_not_ge hlJ)
      funext i
      apply Fin.ext
      have hcoord : (gridCellLabel q m J l hm hJ u i).val =
          (gridCellLabel q m J l hm hJ v i).val :=
        congrArg Fin.val (congrFun h i)
      simp only [gridCellLabel, cell] at hcoord ⊢
      rw [Nat.sub_eq_zero_of_le hJl] at hcoord
      simp only [Nat.pow_zero, Nat.div_one] at hcoord
      simp only [hcoord]
  have key := maxCardValue_le_blockSum_add_repair
    (X := Fin q → ℝ) (K := J) (C := fun k => Fin q → Fin (2 ^ k + 1))
    (cell := cell) (hnested := hnested) x y cost hcost_nonneg
    (B := markedGridRepairBound q r C t G) hB hroot
  have hval : cloudValueNat
      (mMarkedShiftedEdge (A := A) (B := B) q r kin g t G)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω =
      PartialMatching.maxCardValue cost := by
    unfold cloudValueNat
    congr 1
    funext i j
    unfold mMarkedShiftedEdge cost edge markedEdgeCost
    rw [if_pos ⟨i.isLt, j.isLt⟩]
  have hshifted := cloudValueNat_mMarkedShiftedEdge
    (A := A) (B := B) q r kin g t G ω
  have hblockval : ∀ c : Fin q → Fin (2 ^ J + 1),
      PartialMatching.maxCardValue (blockCost (fun i : Fin (mSourceCount ω) =>
          cell J (x i)) (fun j : Fin (mTargetCount ω) => cell J (y j)) cost c) =
      PartialMatching.maxCardValue (blockCost (fun i : Fin (mSourceCount ω) =>
          cell J (x i)) (fun j : Fin (mTargetCount ω) => cell J (y j)) edge c) +
        ((min (blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c)
              (blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c) : ℕ) : ℝ) *
          (|t| * G) := by
    intro c
    have hbc : blockCost (fun i : Fin (mSourceCount ω) => cell J (x i))
        (fun j : Fin (mTargetCount ω) => cell J (y j)) cost c =
        (fun i j => blockCost (fun i : Fin (mSourceCount ω) => cell J (x i))
          (fun j : Fin (mTargetCount ω) => cell J (y j)) edge c i j + |t| * G) := rfl
    rw [hbc, PartialMatching.maxCardValue_add_const, Nat.cast_min]
  have hsum_min_nat : (∑ c : Fin q → Fin (2 ^ J + 1),
      min (blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c)
        (blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c)) ≤
      min (mSourceCount ω) (mTargetCount ω) := by
    apply le_min
    · calc (∑ c : Fin q → Fin (2 ^ J + 1),
            min (blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c)
              (blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c))
          ≤ ∑ c : Fin q → Fin (2 ^ J + 1),
              blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c :=
            Finset.sum_le_sum (fun c _ => min_le_left _ _)
        _ = mSourceCount ω :=
            sum_card_blockFinset (fun i : Fin (mSourceCount ω) => cell J (x i))
    · calc (∑ c : Fin q → Fin (2 ^ J + 1),
            min (blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c)
              (blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c))
          ≤ ∑ c : Fin q → Fin (2 ^ J + 1),
              blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c :=
            Finset.sum_le_sum (fun c _ => min_le_right _ _)
        _ = mTargetCount ω :=
            sum_card_blockFinset (fun j : Fin (mTargetCount ω) => cell J (y j))
  have hsum_min_le : (∑ c : Fin q → Fin (2 ^ J + 1),
      ((min (blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c)
        (blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c) : ℕ) : ℝ)) ≤
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hsum_min_nat
  have hrepair_eq : (∑ k ∈ Finset.range (J + 1), if 0 < k then
      markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
        (cellDiscrepancy (cell k) x y - cellDiscrepancy (cell (k - 1)) x y)
      else 0) =
      ∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
          (markedGridDiscrepancy q m J k hm hJ ω -
            markedGridDiscrepancy q m J (k - 1) hm hJ ω) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun k _ => ?_)
    · ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    · rfl
  have hmain : markedTilted q r kin g t ω ≤
      (∑ c : Fin q → Fin (2 ^ J + 1),
        PartialMatching.maxCardValue
          (blockCost (fun i : Fin (mSourceCount ω) => cell J (x i))
            (fun j : Fin (mTargetCount ω) => cell J (y j)) edge c)) +
      ∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
          (markedGridDiscrepancy q m J k hm hJ ω -
            markedGridDiscrepancy q m J (k - 1) hm hJ ω) := by
    have hraw : PartialMatching.maxCardValue cost ≤
        (∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost (fun i : Fin (mSourceCount ω) => cell J (x i))
              (fun j : Fin (mTargetCount ω) => cell J (y j)) cost c)) +
        ∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy q m J k hm hJ ω -
              markedGridDiscrepancy q m J (k - 1) hm hJ ω) := by
      have h := key
      rw [hrepair_eq] at h
      exact h
    have hsplit : (∑ c : Fin q → Fin (2 ^ J + 1),
        PartialMatching.maxCardValue
          (blockCost (fun i : Fin (mSourceCount ω) => cell J (x i))
            (fun j : Fin (mTargetCount ω) => cell J (y j)) cost c)) =
        (∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost (fun i : Fin (mSourceCount ω) => cell J (x i))
              (fun j : Fin (mTargetCount ω) => cell J (y j)) edge c)) +
        (∑ c : Fin q → Fin (2 ^ J + 1),
          ((min (blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c)
            (blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c) : ℕ) : ℝ)) *
          (|t| * G) := by
      rw [Finset.sum_congr rfl (fun c _ => hblockval c), Finset.sum_add_distrib,
        Finset.sum_mul]
    have hshifted_val : markedTilted q r kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * (|t| * G) ≤
        (∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost (fun i : Fin (mSourceCount ω) => cell J (x i))
              (fun j : Fin (mTargetCount ω) => cell J (y j)) edge c)) +
        (∑ c : Fin q → Fin (2 ^ J + 1),
          ((min (blockSizeS (fun i : Fin (mSourceCount ω) => cell J (x i)) c)
            (blockSizeT (fun j : Fin (mTargetCount ω) => cell J (y j)) c) : ℕ) : ℝ)) *
          (|t| * G) +
        ∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy q m J k hm hJ ω -
              markedGridDiscrepancy q m J (k - 1) hm hJ ω) := by
      calc markedTilted q r kin g t ω +
            ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * (|t| * G)
          = cloudValueNat (mMarkedShiftedEdge (A := A) (B := B) q r kin g t G)
              (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω :=
            hshifted.symm
        _ = PartialMatching.maxCardValue cost := hval
        _ ≤ _ := hraw
        _ = _ := by rw [hsplit]
    have hs : (0 : ℝ) ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
    nlinarith [hshifted_val, hsum_min_le, hs]
  simpa only [cell, x, y, edge, markedTruncSource, markedTruncTarget] using hmain

end OTSelector.Probability

namespace OTSelector.Probability
open Reconstruction
open Reconstruction

/-! ## Integrability of the grid discrepancy -/

/-- The sum of partition counts over all cells is the cardinality of the index
type. -/
theorem sum_partitionCount_univ {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] (w : I → C) :
    (∑ c : C, partitionCount w c) = (Fintype.card I : ℝ) := by
  classical
  unfold partitionCount
  rw [Finset.sum_comm]
  have h : ∀ i : I, (∑ c : C, partitionIndicator (w i) c) = 1 := by
    intro i
    rw [Finset.sum_eq_single (w i)]
    · unfold partitionIndicator
      rw [if_pos rfl]
    · intro c _ hc
      unfold partitionIndicator
      rw [if_neg (Ne.symm hc)]
    · intro hc
      exact absurd (Finset.mem_univ (w i)) hc
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The discrepancy is bounded by the total number of points. -/
theorem cellDiscrepancy_le_card {X : Type*} {C : Type*} [Fintype C] [DecidableEq C]
    (cell : X → C) {a b : ℕ} (x : Fin a → X) (y : Fin b → X) :
    cellDiscrepancy cell x y ≤ (a : ℝ) + (b : ℝ) := by
  classical
  unfold cellDiscrepancy
  calc (∑ c : C, |partitionCount (cell ∘ x) c - partitionCount (cell ∘ y) c|)
      ≤ ∑ c : C, (partitionCount (cell ∘ x) c + partitionCount (cell ∘ y) c) := by
        apply Finset.sum_le_sum
        intro c _
        have ha : 0 ≤ partitionCount (cell ∘ x) c := by
          unfold partitionCount
          exact Finset.sum_nonneg fun _ _ => by
            unfold partitionIndicator; split_ifs <;> norm_num
        have hb : 0 ≤ partitionCount (cell ∘ y) c := by
          unfold partitionCount
          exact Finset.sum_nonneg fun _ _ => by
            unfold partitionIndicator; split_ifs <;> norm_num
        rw [abs_le]
        constructor <;> linarith
    _ = (∑ c : C, partitionCount (cell ∘ x) c) +
          ∑ c : C, partitionCount (cell ∘ y) c := Finset.sum_add_distrib
    _ = (Fintype.card (Fin a) : ℝ) + (Fintype.card (Fin b) : ℝ) := by
        rw [sum_partitionCount_univ, sum_partitionCount_univ]
    _ = (a : ℝ) + (b : ℝ) := by simp

/-- The grid discrepancy is measurable in the cloud. -/
theorem measurable_markedGridDiscrepancy (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] :
    Measurable (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ) := by
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
  have h := measurable_gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
    (hm := hm) (hJ := hJ) (A := A) (B := B)
  have hfun : markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ =
      gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
        (hm := hm) (hJ := hJ) (A := A) (B := B) := rfl
  rw [hfun]
  exact h

/-- The grid discrepancy is integrable under the two-cloud law. -/
theorem integrable_markedGridDiscrepancy (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (R : ℝ≥0) :
    Integrable (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ)
      (twoMarkedCloudLaw (q := q) A B α β R) := by
  classical
  have hsrc : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((mSourceCount ω : ℕ) : ℝ)) (twoMarkedCloudLaw (q := q) A B α β R) :=
    integrable_mSourceCount q α β R
  have htgt : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((mTargetCount ω : ℕ) : ℝ)) (twoMarkedCloudLaw (q := q) A B α β R) :=
    integrable_mTargetCount q α β R
  have hbound : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((mSourceCount ω : ℕ) : ℝ) + ((mTargetCount ω : ℕ) : ℝ))
      (twoMarkedCloudLaw (q := q) A B α β R) := hsrc.add htgt
  refine hbound.mono'
    (measurable_markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ).aestronglyMeasurable ?_
  filter_upwards with ω
  have h := cellDiscrepancy_le_card (gridCellLabel q m J k hm hJ)
    (markedTruncSource q ω) (markedTruncTarget q ω)
  simpa only [markedGridDiscrepancy, Real.norm_eq_abs, abs_of_nonneg
    (cellDiscrepancy_nonneg _ _ _)] using h

end OTSelector.Probability
