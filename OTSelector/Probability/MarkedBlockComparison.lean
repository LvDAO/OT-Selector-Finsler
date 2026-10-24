import OTSelector.Finite.MaxCardValueScaling
import OTSelector.Finite.MaxCardValueBlockRepair
import OTSelector.Finite.DyadicCellCost
import OTSelector.Probability.MarkedPressureBound

/-!
# Deterministic block comparison for the marked pressure

For a marked two-cloud sample with a nonnegative kinetic kernel, the optimal
maximum-cardinality value is bounded by the sum of the optimal values inside
the `2 ^ (q * J)` dyadic leaf blocks plus the cost of repairing the count
discrepancies of the dyadic hierarchy.

The repair term is the telescoping sum of `BlockRepair`; the leaf matching is
the block-optimal matching of `BlockMaxValueComparison`.  Every repaired pair
at level `k` lies in one dyadic cell of side `2 ^ (-k)`, so its kinetic cost is
at most `4 * r ^ (2 / q) * C * q * (1 / 4) ^ k`, while the probe contribution,
shifted by `|t| G` to make all edges nonnegative, is at most `2 * |t| G`.

This is the deterministic half of the block-subadditivity comparison for the
marked pressure; integrating the block values against the block decomposition
law produces the inequality `f (m * L) <= f L + error` of the paper.
-/

open scoped BigOperators
open MeasureTheory

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## Truncated position sequences -/

/-- The truncated source positions of a marked cloud. -/
def markedTruncSource (q : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    Fin (mSourceCount ω) → Fin q → ℝ :=
  fun i => cubeTruncPoint (mSourcePoint ω (i : ℕ))

/-- The truncated target positions of a marked cloud. -/
def markedTruncTarget (q : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    Fin (mTargetCount ω) → Fin q → ℝ :=
  fun j => cubeTruncPoint (mTargetPoint ω (j : ℕ))

/-- The unshifted edge cost of the marked cloud. -/
noncomputable def markedEdgeCost (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (t : ℝ) (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) : ℝ :=
  mKineticCost q r kin ω i j + t * mProbe g ω i j

/-- The kinetic part of the level-`k` repair weight. -/
noncomputable def markedRepairWeight (q : ℕ) (r C : ℝ) (k : ℕ) : ℝ :=
  4 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1)

/-- The cost bound at one repair level, including the probe shift. -/
noncomputable def markedRepairBound (q : ℕ) (r C t G : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else markedRepairWeight q r C k + 2 * |t| * G

/-! ## Two elementary edge bounds -/

/-- Kinetic edge bound for two points sharing a level-`k` dyadic cell. -/
theorem kinetic_markedEdge_le_of_same_cell
    (q k : ℕ) {r C : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (a : A) (b : B) {x y : Fin q → ℝ}
    (hx : ∀ l, 0 ≤ x l ∧ x l < 1) (hy : ∀ l, 0 ≤ y l ∧ y l < 1)
    (hcell : dyadicCell q k x = dyadicCell q k y) :
    r ^ (2 / (q : ℝ)) * kin a b (fun l => y l - x l) ≤
      4 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k := by
  have hsq : ∑ l, (x l - y l) ^ 2 ≤ (q : ℝ) * (1 / 4 : ℝ) ^ k :=
    sum_sq_le_of_dyadicCell_eq hx hy hcell
  have hsq' : ∑ l, (fun l => y l - x l) l ^ 2 = ∑ l, (x l - y l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hb := hkin_bound a b (fun l => y l - x l)
  have hkinle : kin a b (fun l => y l - x l) ≤
      C * ((q : ℝ) * (1 / 4 : ℝ) ^ k) := by
    calc kin a b (fun l => y l - x l)
        ≤ |kin a b (fun l => y l - x l)| := le_abs_self _
      _ ≤ C * ∑ l, (fun l => y l - x l) l ^ 2 := hb
      _ = C * ∑ l, (x l - y l) ^ 2 := by rw [hsq']
      _ ≤ C * ((q : ℝ) * (1 / 4 : ℝ) ^ k) := by
          have := mul_le_mul_of_nonneg_left hsq hC0
          nlinarith
  have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  have hbase : (0 : ℝ) ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) * (1 / 4 : ℝ) ^ k :=
    mul_nonneg
      (mul_nonneg hrpow (mul_nonneg hC0 (Nat.cast_nonneg q)))
      (pow_nonneg (by norm_num) k)
  calc r ^ (2 / (q : ℝ)) * kin a b (fun l => y l - x l)
      ≤ r ^ (2 / (q : ℝ)) * (C * ((q : ℝ) * (1 / 4 : ℝ) ^ k)) :=
        mul_le_mul_of_nonneg_left hkinle hrpow
    _ ≤ 4 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k := by
        nlinarith [hbase]

/-- The probe contribution of one edge. -/
theorem probe_mul_le (t : ℝ) {g : A → B → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (a : A) (b : B) :
    t * g a b ≤ |t| * G := by
  have h1 : t * g a b ≤ |t * g a b| := le_abs_self _
  have h2 : |t * g a b| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb a b) (abs_nonneg t)
  linarith

/-! ## The deterministic block comparison -/

set_option maxHeartbeats 400000 in
/-- The deterministic block comparison: the marked tilted value is at most the
sum of the leaf-block optimal values plus the hierarchical repair bound. -/
theorem markedTilted_le_blockSum_add_repair
    (q J : ℕ) {r t C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (ω : TwoMarkedCloudSpace q A B) :
    markedTilted q r kin g t ω ≤
      (∑ c : Fin q → Fin (2 ^ J),
        PartialMatching.maxCardValue
          (blockCost (fun i : Fin (mSourceCount ω) =>
              dyadicCell q J (markedTruncSource q ω i))
            (fun j : Fin (mTargetCount ω) =>
              dyadicCell q J (markedTruncTarget q ω j))
            (fun i j => markedEdgeCost q r kin g t ω (i : ℕ) (j : ℕ)) c))
      + ∑ k ∈ Finset.Icc 1 J,
          markedRepairBound q r C t G k * (1 / 2 : ℝ) *
            (markedTruncCellDiscrepancy q k ω -
              markedTruncCellDiscrepancy q (k - 1) ω) := by
  classical
  let x : Fin (mSourceCount ω) → (Fin q → ℝ) := markedTruncSource q ω
  let y : Fin (mTargetCount ω) → (Fin q → ℝ) := markedTruncTarget q ω
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
      dyadicCell q k (x i) = dyadicCell q k (y j) →
        cost i j ≤ markedRepairBound q r C t G (k + 1) := by
    intro k hkJ i j hcell
    have hx : ∀ l, 0 ≤ x i l ∧ x i l < 1 := fun l =>
      cubeTruncPoint_mem (mSourcePoint ω (i : ℕ)) l
    have hy : ∀ l, 0 ≤ y j l ∧ y j l < 1 := fun l =>
      cubeTruncPoint_mem (mTargetPoint ω (j : ℕ)) l
    have hkin := kinetic_markedEdge_le_of_same_cell (q := q) (k := k)
      (r := r) (C := C) hr hC0 hkin_bound
      (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ)) hx hy hcell
    have hprobe := probe_mul_le (A := A) (B := B) t (g := g) (G := G) hgb
      (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
    have hbk : markedRepairBound q r C t G (k + 1) =
        4 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k + 2 * |t| * G := by
      simp only [markedRepairBound, markedRepairWeight, Nat.succ_ne_zero, if_false,
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
      4 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k + 2 * |t| * G
    have hkin' : r ^ (2 / (q : ℝ)) * kin (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
        (fun l => cubeTruncPoint (mTargetPoint ω (j : ℕ)) l -
          cubeTruncPoint (mSourcePoint ω (i : ℕ)) l) ≤
        4 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ k := hkin
    linarith [hkin', hprobe]
  have hroot : ∀ u v : Fin q → ℝ, dyadicCell q 0 u = dyadicCell q 0 v := by
    intro u v
    funext l
    apply Fin.ext
    have h1 : (dyadicCell q 0 u l).val < 1 := (dyadicCell q 0 u l).isLt
    have h2 : (dyadicCell q 0 v l).val < 1 := (dyadicCell q 0 v l).isLt
    omega
  have key := maxCardValue_le_blockSum_add_repair
    (X := Fin q → ℝ) (K := J) (C := fun k => Fin q → Fin (2 ^ k))
    (cell := fun k v => dyadicCell q k v)
    (hnested := fun k l hkl u v h => dyadicCell_nested_global hkl h)
    x y cost hcost_nonneg (B := markedRepairBound q r C t G) hB hroot
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
  have hblockval : ∀ c : Fin q → Fin (2 ^ J),
      PartialMatching.maxCardValue (blockCost (fun i : Fin (mSourceCount ω) =>
          dyadicCell q J (x i)) (fun j : Fin (mTargetCount ω) =>
          dyadicCell q J (y j)) cost c) =
      PartialMatching.maxCardValue (blockCost (fun i : Fin (mSourceCount ω) =>
          dyadicCell q J (x i)) (fun j : Fin (mTargetCount ω) =>
          dyadicCell q J (y j)) edge c) +
        ((min (blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c)
              (blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c) : ℕ) : ℝ) *
          (|t| * G) := by
    intro c
    have hbc : blockCost (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
        (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) cost c =
        (fun i j => blockCost (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
          (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) edge c i j + |t| * G) := rfl
    rw [hbc, PartialMatching.maxCardValue_add_const, Nat.cast_min]
  have hsum_min_nat : (∑ c : Fin q → Fin (2 ^ J),
      min (blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c)
        (blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c)) ≤
      min (mSourceCount ω) (mTargetCount ω) := by
    apply le_min
    · calc (∑ c : Fin q → Fin (2 ^ J),
            min (blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c)
              (blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c))
          ≤ ∑ c : Fin q → Fin (2 ^ J),
              blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c :=
            Finset.sum_le_sum (fun c _ => min_le_left _ _)
        _ = mSourceCount ω :=
            sum_card_blockFinset (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
    · calc (∑ c : Fin q → Fin (2 ^ J),
            min (blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c)
              (blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c))
          ≤ ∑ c : Fin q → Fin (2 ^ J),
              blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c :=
            Finset.sum_le_sum (fun c _ => min_le_right _ _)
        _ = mTargetCount ω :=
            sum_card_blockFinset (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j))
  have hsum_min_le : (∑ c : Fin q → Fin (2 ^ J),
      ((min (blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c)
        (blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c) : ℕ) : ℝ)) ≤
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hsum_min_nat
  have hD : ∀ k : ℕ, cellDiscrepancy (fun v : Fin q → ℝ => dyadicCell q k v)
      (markedTruncSource q ω) (markedTruncTarget q ω) =
      markedTruncCellDiscrepancy q k ω := by
    intro k
    rfl
  -- Rewrite the raw repair sum into the dyadic discrepancy form.
  have hrepair_eq : (∑ k ∈ Finset.range (J + 1), if 0 < k then
      markedRepairBound q r C t G k * (1 / 2 : ℝ) *
        (cellDiscrepancy (fun v : Fin q → ℝ => dyadicCell q k v)
            (markedTruncSource q ω) (markedTruncTarget q ω) -
          cellDiscrepancy (fun v : Fin q → ℝ => dyadicCell q (k - 1) v)
            (markedTruncSource q ω) (markedTruncTarget q ω))
      else 0) =
      ∑ k ∈ Finset.Icc 1 J,
        markedRepairBound q r C t G k * (1 / 2 : ℝ) *
          (markedTruncCellDiscrepancy q k ω -
            markedTruncCellDiscrepancy q (k - 1) ω) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun k _ => ?_)
    · ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    · rw [hD k, hD (k - 1)]
  -- Assemble the pointwise inequality.
  have hmain : markedTilted q r kin g t ω ≤
      (∑ c : Fin q → Fin (2 ^ J),
        PartialMatching.maxCardValue
          (blockCost (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
            (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) edge c)) +
      ∑ k ∈ Finset.Icc 1 J,
        markedRepairBound q r C t G k * (1 / 2 : ℝ) *
          (markedTruncCellDiscrepancy q k ω -
            markedTruncCellDiscrepancy q (k - 1) ω) := by
    have hraw : PartialMatching.maxCardValue cost ≤
        (∑ c : Fin q → Fin (2 ^ J),
          PartialMatching.maxCardValue
            (blockCost (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
              (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) cost c)) +
        ∑ k ∈ Finset.Icc 1 J,
          markedRepairBound q r C t G k * (1 / 2 : ℝ) *
            (markedTruncCellDiscrepancy q k ω -
              markedTruncCellDiscrepancy q (k - 1) ω) := by
      have h := key
      rw [hrepair_eq] at h
      exact h
    have hsplit : (∑ c : Fin q → Fin (2 ^ J),
        PartialMatching.maxCardValue
          (blockCost (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
            (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) cost c)) =
        (∑ c : Fin q → Fin (2 ^ J),
          PartialMatching.maxCardValue
            (blockCost (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
              (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) edge c)) +
        (∑ c : Fin q → Fin (2 ^ J),
          ((min (blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c)
            (blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c) : ℕ) : ℝ)) *
          (|t| * G) := by
      rw [Finset.sum_congr rfl (fun c _ => hblockval c), Finset.sum_add_distrib,
        Finset.sum_mul]
    have hshifted_val : markedTilted q r kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * (|t| * G) ≤
        (∑ c : Fin q → Fin (2 ^ J),
          PartialMatching.maxCardValue
            (blockCost (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i))
              (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) edge c)) +
        (∑ c : Fin q → Fin (2 ^ J),
          ((min (blockSizeS (fun i : Fin (mSourceCount ω) => dyadicCell q J (x i)) c)
            (blockSizeT (fun j : Fin (mTargetCount ω) => dyadicCell q J (y j)) c) : ℕ) : ℝ)) *
          (|t| * G) +
        ∑ k ∈ Finset.Icc 1 J,
          markedRepairBound q r C t G k * (1 / 2 : ℝ) *
            (markedTruncCellDiscrepancy q k ω -
              markedTruncCellDiscrepancy q (k - 1) ω) := by
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
  simpa only [x, y, markedTruncSource, markedTruncTarget] using hmain

end OTSelector.Probability
