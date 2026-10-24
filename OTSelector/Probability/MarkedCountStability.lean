import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Finite.MaxCardValueStability
import OTSelector.Probability.MarkedPressureScale

/-!
# Count stability of the marked tilted value

The marked tilted value of a realized pair of Poissonized marked clouds is the
optimal maximum-cardinality matching value of the rectangular matrix of marked
edge costs.  Replacing the two cloud sizes by one common size `n` and keeping
the same cost formula at the indices `Fin n` changes the value by at most twice
the uniform edge bound for every row or column that is added or removed.  Since
every marked edge is bounded by `r^{2/q} C q + |t| G`, the total change is at
most that bound times the sum of the two count discrepancies.

This is the deterministic count-continuity estimate used to replace the random
cloud sizes by a fixed sample size.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 800000 in
/-- **Count stability of the marked tilted value.**  The tilted optimal value of
the realized marked clouds differs from the maximum-cardinality value of the
corresponding `n × n` cost matrix by at most twice the uniform marked edge
bound times the total discrepancy of the two cloud counts from `n`. -/
theorem abs_markedTilted_sub_fixedMatrix_le
    (q : ℕ) {r t C G : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (ω : TwoMarkedCloudSpace q A B) (n : ℕ) :
    |markedTilted q r kin g t ω -
      PartialMatching.maxCardValue
        (fun i : Fin n => fun j : Fin n =>
          mKineticCost q r kin ω (i : ℕ) (j : ℕ) +
            t * mProbe g ω (i : ℕ) (j : ℕ))| ≤
      2 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|) := by
  let Bnd : ℝ := r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G
  have hBnd0 : 0 ≤ Bnd := by
    dsimp only [Bnd]
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
      (mul_nonneg (abs_nonneg t) hG0)
  have hedge : ∀ i j : ℕ, |mKineticCost q r kin ω i j + t * mProbe g ω i j| ≤ Bnd := by
    intro i j
    have h1 := abs_mKineticCost_le q hr hC0 hkin_bound ω i j
    have h2 : |t * mProbe g ω i j| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_mProbe_le q hgb ω i j) (abs_nonneg t)
    have h3 : |mKineticCost q r kin ω i j + t * mProbe g ω i j| ≤
        r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G :=
      (abs_add_le _ _).trans (add_le_add h1 h2)
    simpa only [Bnd] using h3
  let NS : ℕ := mSourceCount ω
  let NT : ℕ := mTargetCount ω
  let mS : ℕ := min NS n
  let mT : ℕ := min NT n
  let δS : ℕ := NS - mS
  let δT : ℕ := NT - mT
  let εS : ℕ := n - mS
  let εT : ℕ := n - mT
  let Mfun : (N M : ℕ) → Fin N → Fin M → ℝ :=
    fun N M i j =>
      mKineticCost q r kin ω (i : ℕ) (j : ℕ) + t * mProbe g ω (i : ℕ) (j : ℕ)
  have hmarked : markedTilted q r kin g t ω =
      PartialMatching.maxCardValue (Mfun NS NT) := by
    unfold markedTilted tiltedCloudValue
    rfl
  -- Reindexing a matrix along an equality of the number of rows or columns.
  have hcastRow : ∀ {N N' M : ℕ} (h : N = N') (c : Fin N → Fin M → ℝ),
      PartialMatching.maxCardValue (fun i : Fin N' => fun j : Fin M =>
        c (Fin.cast h.symm i) j) = PartialMatching.maxCardValue c := by
    intro N N' M h c
    have hre := PartialMatching.maxCardValue_reindex c (finCongr h) (Equiv.refl (Fin M))
    simpa only [finCongr_symm_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq] using hre
  have hcastCol : ∀ {N M M' : ℕ} (h : M = M') (c : Fin N → Fin M → ℝ),
      PartialMatching.maxCardValue (fun i : Fin N => fun j : Fin M' =>
        c i (Fin.cast h.symm j)) = PartialMatching.maxCardValue c := by
    intro N M M' h c
    have hre := PartialMatching.maxCardValue_reindex c (Equiv.refl (Fin N)) (finCongr h)
    simpa only [finCongr_symm_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq] using hre
  -- Dropping the extra source rows.
  have hAB : |PartialMatching.maxCardValue (Mfun NS NT) -
      PartialMatching.maxCardValue (Mfun mS NT)| ≤ 2 * Bnd * (δS : ℝ) := by
    have h := PartialMatching.abs_maxCardValue_sub_le_add_rows
      (a := mS) (δ := δS) (b := NT)
      (c := Mfun (mS + δS) NT) hBnd0
      (fun i j => hedge (i : ℕ) (j : ℕ))
    have hsub : (fun i : Fin mS => fun j : Fin NT =>
        Mfun (mS + δS) NT (Fin.castLE (Nat.le_add_right mS δS) i) j) = Mfun mS NT :=
      rfl
    have hcast : PartialMatching.maxCardValue (Mfun NS NT) =
        PartialMatching.maxCardValue (Mfun (mS + δS) NT) := by
      have h' := hcastRow (N := mS + δS) (N' := NS) (M := NT)
        (Nat.add_sub_of_le (min_le_left NS n)) (Mfun (mS + δS) NT)
      rw [show (fun i : Fin NS => fun j : Fin NT =>
          Mfun (mS + δS) NT
            (Fin.cast (Nat.add_sub_of_le (min_le_left NS n)).symm i) j) =
          Mfun NS NT from rfl] at h'
      exact h'
    rw [hsub, ← hcast] at h
    exact h
  -- Dropping the extra target columns.
  have hBC : |PartialMatching.maxCardValue (Mfun mS NT) -
      PartialMatching.maxCardValue (Mfun mS mT)| ≤ 2 * Bnd * (δT : ℝ) := by
    have h := PartialMatching.abs_maxCardValue_sub_le_add_cols
      (a := mS) (b := mT) (δ := δT)
      (c := Mfun mS (mT + δT)) hBnd0
      (fun i j => hedge (i : ℕ) (j : ℕ))
    have hsub : (fun i : Fin mS => fun j : Fin mT =>
        Mfun mS (mT + δT) i (Fin.castLE (Nat.le_add_right mT δT) j)) = Mfun mS mT :=
      rfl
    have hcast : PartialMatching.maxCardValue (Mfun mS NT) =
        PartialMatching.maxCardValue (Mfun mS (mT + δT)) := by
      have h' := hcastCol (N := mS) (M := mT + δT) (M' := NT)
        (Nat.add_sub_of_le (min_le_left NT n)) (Mfun mS (mT + δT))
      rw [show (fun i : Fin mS => fun j : Fin NT =>
          Mfun mS (mT + δT) i
            (Fin.cast (Nat.add_sub_of_le (min_le_left NT n)).symm j)) =
          Mfun mS NT from rfl] at h'
      exact h'
    rw [hsub, ← hcast] at h
    exact h
  -- Adjoining the missing rows up to `n` (in the reverse direction).
  have hDC : |PartialMatching.maxCardValue (Mfun mS mT) -
      PartialMatching.maxCardValue (Mfun n mT)| ≤ 2 * Bnd * (εS : ℝ) := by
    have h := PartialMatching.abs_maxCardValue_sub_le_add_rows
      (a := mS) (δ := εS) (b := mT)
      (c := Mfun (mS + εS) mT) hBnd0
      (fun i j => hedge (i : ℕ) (j : ℕ))
    have hsub : (fun i : Fin mS => fun j : Fin mT =>
        Mfun (mS + εS) mT (Fin.castLE (Nat.le_add_right mS εS) i) j) = Mfun mS mT :=
      rfl
    have hcast : PartialMatching.maxCardValue (Mfun n mT) =
        PartialMatching.maxCardValue (Mfun (mS + εS) mT) := by
      have h' := hcastRow (N := mS + εS) (N' := n) (M := mT)
        (Nat.add_sub_of_le (min_le_right NS n)) (Mfun (mS + εS) mT)
      rw [show (fun i : Fin n => fun j : Fin mT =>
          Mfun (mS + εS) mT
            (Fin.cast (Nat.add_sub_of_le (min_le_right NS n)).symm i) j) =
          Mfun n mT from rfl] at h'
      exact h'
    rw [hsub, ← hcast, abs_sub_comm] at h
    exact h
  -- Adjoining the missing columns up to `n` (in the reverse direction).
  have hED : |PartialMatching.maxCardValue (Mfun n mT) -
      PartialMatching.maxCardValue (Mfun n n)| ≤ 2 * Bnd * (εT : ℝ) := by
    have h := PartialMatching.abs_maxCardValue_sub_le_add_cols
      (a := n) (b := mT) (δ := εT)
      (c := Mfun n (mT + εT)) hBnd0
      (fun i j => hedge (i : ℕ) (j : ℕ))
    have hsub : (fun i : Fin n => fun j : Fin mT =>
        Mfun n (mT + εT) i (Fin.castLE (Nat.le_add_right mT εT) j)) = Mfun n mT :=
      rfl
    have hcast : PartialMatching.maxCardValue (Mfun n n) =
        PartialMatching.maxCardValue (Mfun n (mT + εT)) := by
      have h' := hcastCol (N := n) (M := mT + εT) (M' := n)
        (Nat.add_sub_of_le (min_le_right NT n)) (Mfun n (mT + εT))
      rw [show (fun i : Fin n => fun j : Fin n =>
          Mfun n (mT + εT) i
            (Fin.cast (Nat.add_sub_of_le (min_le_right NT n)).symm j)) =
          Mfun n n from rfl] at h'
      exact h'
    rw [hsub, ← hcast, abs_sub_comm] at h
    exact h
  -- The count-discrepancy identities.
  have hS : (δS : ℝ) + (εS : ℝ) = |(NS : ℝ) - (n : ℝ)| := by
    rcases le_total NS n with hle | hle
    · have hmS : mS = NS := min_eq_left hle
      have hδS : δS = 0 := by
        show NS - mS = 0
        rw [hmS]
        simp
      have hεS : εS = n - NS := by
        show n - mS = n - NS
        rw [hmS]
      rw [hδS, hεS, Nat.cast_zero, zero_add, Nat.cast_sub hle, abs_sub_comm,
        abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hle)
    · have hmS : mS = n := min_eq_right hle
      have hδS : δS = NS - n := by
        show NS - mS = NS - n
        rw [hmS]
      have hεS : εS = 0 := by
        show n - mS = 0
        rw [hmS]
        simp
      rw [hδS, hεS, Nat.cast_zero, add_zero, Nat.cast_sub hle, abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hle)
  have hT : (δT : ℝ) + (εT : ℝ) = |(NT : ℝ) - (n : ℝ)| := by
    rcases le_total NT n with hle | hle
    · have hmT : mT = NT := min_eq_left hle
      have hδT : δT = 0 := by
        show NT - mT = 0
        rw [hmT]
        simp
      have hεT : εT = n - NT := by
        show n - mT = n - NT
        rw [hmT]
      rw [hδT, hεT, Nat.cast_zero, zero_add, Nat.cast_sub hle, abs_sub_comm,
        abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hle)
    · have hmT : mT = n := min_eq_right hle
      have hδT : δT = NT - n := by
        show NT - mT = NT - n
        rw [hmT]
      have hεT : εT = 0 := by
        show n - mT = 0
        rw [hmT]
        simp
      rw [hδT, hεT, Nat.cast_zero, add_zero, Nat.cast_sub hle, abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hle)
  rw [hmarked]
  change |PartialMatching.maxCardValue (Mfun NS NT) -
      PartialMatching.maxCardValue (Mfun n n)| ≤
    2 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
      (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
        |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
  have htri : |PartialMatching.maxCardValue (Mfun NS NT) -
      PartialMatching.maxCardValue (Mfun n n)| ≤
      |PartialMatching.maxCardValue (Mfun NS NT) -
        PartialMatching.maxCardValue (Mfun mS NT)| +
      |PartialMatching.maxCardValue (Mfun mS NT) -
        PartialMatching.maxCardValue (Mfun mS mT)| +
      |PartialMatching.maxCardValue (Mfun mS mT) -
        PartialMatching.maxCardValue (Mfun n mT)| +
      |PartialMatching.maxCardValue (Mfun n mT) -
        PartialMatching.maxCardValue (Mfun n n)| := by
    have h1 := abs_sub_le (PartialMatching.maxCardValue (Mfun NS NT))
      (PartialMatching.maxCardValue (Mfun mS NT))
      (PartialMatching.maxCardValue (Mfun n n))
    have h2 := abs_sub_le (PartialMatching.maxCardValue (Mfun mS NT))
      (PartialMatching.maxCardValue (Mfun mS mT))
      (PartialMatching.maxCardValue (Mfun n n))
    have h3 := abs_sub_le (PartialMatching.maxCardValue (Mfun mS mT))
      (PartialMatching.maxCardValue (Mfun n mT))
      (PartialMatching.maxCardValue (Mfun n n))
    linarith
  calc
    |PartialMatching.maxCardValue (Mfun NS NT) -
        PartialMatching.maxCardValue (Mfun n n)|
      ≤ |PartialMatching.maxCardValue (Mfun NS NT) -
          PartialMatching.maxCardValue (Mfun mS NT)| +
        |PartialMatching.maxCardValue (Mfun mS NT) -
          PartialMatching.maxCardValue (Mfun mS mT)| +
        |PartialMatching.maxCardValue (Mfun mS mT) -
          PartialMatching.maxCardValue (Mfun n mT)| +
        |PartialMatching.maxCardValue (Mfun n mT) -
          PartialMatching.maxCardValue (Mfun n n)| := htri
    _ ≤ 2 * Bnd * (δS : ℝ) + 2 * Bnd * (δT : ℝ) +
        2 * Bnd * (εS : ℝ) + 2 * Bnd * (εT : ℝ) := by
        linarith [hAB, hBC, hDC, hED]
    _ = 2 * Bnd * ((δS : ℝ) + (εS : ℝ) + ((δT : ℝ) + (εT : ℝ))) := by
        ring
    _ = 2 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|) := by
        rw [hS, hT]

end OTSelector.Probability
