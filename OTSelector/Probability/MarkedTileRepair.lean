import OTSelector.Probability.MarkedTileModel
import OTSelector.Finite.BlockMaxValueComparison

/-!
# Deterministic tile decomposition of the marked tilted value

Partitioning the two clouds by the tile label carried by their marks, the global
maximum-cardinality value is at most the sum of the leaf tile values plus the
uniform edge bound times half the total label-count discrepancy.  This is the
one-level block comparison applied with the label maps; the tile values are the
submatrix maximum-cardinality values of the ambient tile cost.
-/

open MeasureTheory
open scoped BigOperators NNReal

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {C A B : Type*} [DecidableEq C] [Fintype C]

/-- The uniform bound on a tile edge cost. -/
theorem abs_markedEdge_tile_le (q : ℕ) {R t Cb G Kcross : ℝ}
    (hq : 0 < q) (hR : 0 ≤ R) (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G) (hK0 : 0 ≤ Kcross)
    {w : C → ℝ≥0} (hwle : ∀ c, w c ≤ 1)
    {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (ω : TwoMarkedCloudSpace q (C × A) (C × B)) (i j : ℕ) :
    |markedEdgeCost q R (tileKin q w kin Kcross) (tileProbe g) t ω i j| ≤
      R ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G := by
  unfold markedEdgeCost
  have hrpow : (0 : ℝ) ≤ R ^ (2 / (q : ℝ)) := Real.rpow_nonneg hR _
  have hk := abs_tileKin_le (q := q) (w := w) (kin := kin) (Kcross := Kcross)
    (Cb := Cb) hq hwle hkin_bound hCb0 hK0
    (mSourceMark ω i) (mTargetMark ω j)
    (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))
  have hsq := mDisplacement_sq_sum_le q (mSourcePoint ω i) (mTargetPoint ω j)
  have hk' : |tileKin q w kin Kcross (mSourceMark ω i) (mTargetMark ω j)
      (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| ≤
      max Cb Kcross * (q : ℝ) :=
    hk.trans (mul_le_mul_of_nonneg_left hsq (le_trans hCb0 (le_max_left _ _)))
  have hp := abs_tileProbe_le (g := g) (G := G) hG0 hgb
    (mSourceMark ω i) (mTargetMark ω j)
  calc |mKineticCost q R (tileKin q w kin Kcross) ω i j +
        t * mProbe (tileProbe g) ω i j|
      ≤ |mKineticCost q R (tileKin q w kin Kcross) ω i j| +
          |t * mProbe (tileProbe g) ω i j| := abs_add_le _ _
    _ = R ^ (2 / (q : ℝ)) *
          |tileKin q w kin Kcross (mSourceMark ω i) (mTargetMark ω j)
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| +
          |t| * |mProbe (tileProbe g) ω i j| := by
        rw [mKineticCost, abs_mul, abs_of_nonneg hrpow, abs_mul]
    _ ≤ R ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G :=
        add_le_add (mul_le_mul_of_nonneg_left hk' hrpow)
          (mul_le_mul_of_nonneg_left hp (abs_nonneg t))

/-- The label count of a source cloud. -/
def sourceLabelCount (c : C) (z : MarkedCloudSpace q (C × A)) : ℕ :=
  (Finset.univ.filter (fun i : Fin z.1 => (z.2 i).2.1 = c)).card

/-- The label count of a target cloud. -/
def targetLabelCount (c : C) (z : MarkedCloudSpace q (C × B)) : ℕ :=
  (Finset.univ.filter (fun j : Fin z.1 => (z.2 j).2.1 = c)).card

/-- **Deterministic tile repair.**  The global marked tilted value is at most the
sum of the leaf tile values plus the uniform edge bound times half the total
label-count discrepancy. -/
theorem markedTilted_le_tileBlockSum_add_discrepancy
    (q : ℕ) {R t Cb G Kcross : ℝ}
    (hq : 0 < q) (hR : 0 ≤ R) (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G) (hK0 : 0 ≤ Kcross)
    {w : C → ℝ≥0} (hwle : ∀ c, w c ≤ 1)
    {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (ω : TwoMarkedCloudSpace q (C × A) (C × B)) :
    markedTilted q R (tileKin q w kin Kcross) (tileProbe g) t ω ≤
      (∑ c : C,
        PartialMatching.maxCardValue
          (blockCost
            (fun i : Fin (mSourceCount ω) => (mSourceMark ω i).1)
            (fun j : Fin (mTargetCount ω) => (mTargetMark ω j).1)
            (fun i j => markedEdgeCost q R (tileKin q w kin Kcross)
              (tileProbe g) t ω (i : ℕ) (j : ℕ)) c)) +
        (R ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) *
          ((1 / 2 : ℝ) * ∑ c : C,
            |((sourceLabelCount (q := q) c ω.1 : ℕ) : ℝ) -
              ((targetLabelCount (q := q) c ω.2 : ℕ) : ℝ)|) := by
  classical
  have hB0 : (0 : ℝ) ≤ R ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G := by
    have h1 : 0 ≤ R ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) := by positivity
    have h2 : 0 ≤ |t| * G := by positivity
    linarith
  have hB : ∀ (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)),
      markedEdgeCost q R (tileKin q w kin Kcross) (tileProbe g) t ω
        (i : ℕ) (j : ℕ) ≤
      R ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G := by
    intro i j
    exact (le_abs_self _).trans
      (abs_markedEdge_tile_le q (t := t) (Cb := Cb) (G := G) (Kcross := Kcross)
        hq hR hCb0 hG0 hK0 hwle hkin_bound hgb ω i j)
  have h := OTSelector.maxCardValue_le_sum_block_add_half_discrepancy
    (blockS := fun i : Fin (mSourceCount ω) => (mSourceMark ω i).1)
    (blockT := fun j : Fin (mTargetCount ω) => (mTargetMark ω j).1)
    (c := fun i j => markedEdgeCost q R (tileKin q w kin Kcross) (tileProbe g) t ω
      (i : ℕ) (j : ℕ))
    (B := R ^ (2 / (q : ℝ)) * (max Cb Kcross * (q : ℝ)) + |t| * G) hB hB0
  have hval : markedTilted q R (tileKin q w kin Kcross) (tileProbe g) t ω =
      PartialMatching.maxCardValue
        (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
          markedEdgeCost q R (tileKin q w kin Kcross) (tileProbe g) t ω
            (i : ℕ) (j : ℕ)) := rfl
  rw [hval]
  exact h.trans (le_of_eq (by congr 2))

end OTSelector.Probability
