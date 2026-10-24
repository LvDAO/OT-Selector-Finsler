import OTSelector.Probability.MarkedDiagonalLimit
import OTSelector.Probability.BinomialMixing

/-!
# The binomial-weighted block pressure limit

At a tile of mass `w`, the source and target counts of the physical sample are
independent `Bin(n, w)` variables.  The marked block value at sizes `m`, `k` has
a scale-dependent Lipschitz constant because its kinetic coefficient is the
tile intensity `floor (n w)`.  This module combines the count stability of the
block expectation, its diagonal limit at intensity equal to the size, and the
scale-dependent binomial mixing theorem to prove

`(1/n) sum_{m,k} Bin(n,w)(m) Bin(n,w)(k) E (floor (n w)) m k  ->  w * p t`.

The vanishing of the error term uses `q > 4`: the Lipschitz constant grows like
`(n w)^(2/q)` while the count deviation grows like `sqrt (n w)`, so the error is
`O(n^(2/q - 1/2)) -> 0`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal unitInterval Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A two-variable Lipschitz bound obtained from one-step stability in each
coordinate. -/
theorem abs_pair_sub_le_of_row_col {F : ℕ → ℕ → ℝ} {C : ℝ}
    (hrow : ∀ m δ k, |F (m + δ) k - F m k| ≤ C * (δ : ℝ))
    (hcol : ∀ m k δ, |F m (k + δ) - F m k| ≤ C * (δ : ℝ))
    (m k m' k' : ℕ) :
    |F m k - F m' k'| ≤
      C * (|(m : ℝ) - (m' : ℝ)| + |(k : ℝ) - (k' : ℝ)|) := by
  have htri : ∀ a b c : ℝ, |a - c| ≤ |a - b| + |b - c| := by
    intro a b c
    calc |a - c| = |(a - b) + (b - c)| := by ring_nf
      _ ≤ |a - b| + |b - c| := abs_add_le _ _
  have hd₁ : ∀ (j j' : ℕ), j ≤ j' →
      |(((j' : ℕ) : ℝ)) - (j : ℝ)| = ((j' - j : ℕ) : ℝ) := by
    intro j j' hjj
    have hcast : (j : ℝ) + ((j' - j : ℕ) : ℝ) = ((j' : ℕ) : ℝ) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le hjj]
    rw [← hcast, add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]
  have hd₂ : ∀ (j j' : ℕ), j ≤ j' →
      |((j : ℝ)) - (((j' : ℕ) : ℝ))| = ((j' - j : ℕ) : ℝ) := by
    intro j j' hjj
    rw [abs_sub_comm]
    exact hd₁ j j' hjj
  rcases le_total m' m with hm | hm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rcases le_total k' k with hk | hk
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hde : ((d : ℝ) + (e : ℝ)) =
          |(((m' + d : ℕ) : ℝ)) - (m' : ℝ)| +
            |(((k' + e : ℕ) : ℝ)) - (k' : ℝ)| := by
        rw [hd₁ m' (m' + d) (Nat.le_add_right _ _),
          hd₁ k' (k' + e) (Nat.le_add_right _ _)]
        rw [Nat.cast_sub (Nat.le_add_right m' d), Nat.cast_sub (Nat.le_add_right k' e)]
        push_cast
        ring
      calc |F (m' + d) (k' + e) - F m' k'|
          ≤ |F (m' + d) (k' + e) - F m' (k' + e)|
              + |F m' (k' + e) - F m' k'| := htri _ _ _
        _ ≤ C * (d : ℝ) + C * (e : ℝ) :=
            add_le_add (hrow m' d (k' + e)) (hcol m' k' e)
        _ = C * (|(((m' + d : ℕ) : ℝ)) - (m' : ℝ)| +
              |(((k' + e : ℕ) : ℝ)) - (k' : ℝ)|) := by
            rw [← mul_add, hde]
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hde : ((d : ℝ) + (e : ℝ)) =
          |(((m' + d : ℕ) : ℝ)) - (m' : ℝ)| +
            |((k : ℝ)) - (((k + e : ℕ) : ℝ))| := by
        rw [hd₁ m' (m' + d) (Nat.le_add_right _ _),
          hd₂ k (k + e) (Nat.le_add_right _ _)]
        rw [Nat.cast_sub (Nat.le_add_right m' d), Nat.cast_sub (Nat.le_add_right k e)]
        push_cast
        ring
      calc |F (m' + d) k - F m' (k + e)|
          ≤ |F (m' + d) k - F m' k| + |F m' k - F m' (k + e)| := htri _ _ _
        _ ≤ C * (d : ℝ) + C * (e : ℝ) := by
            refine add_le_add (hrow m' d k) ?_
            rw [abs_sub_comm]
            exact hcol m' k e
        _ = C * (|(((m' + d : ℕ) : ℝ)) - (m' : ℝ)| +
              |((k : ℝ)) - (((k + e : ℕ) : ℝ))|) := by
            rw [← mul_add, hde]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rcases le_total k' k with hk | hk
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hde : ((e : ℝ) + (d : ℝ)) =
          |((m : ℝ)) - (((m + d : ℕ) : ℝ))| +
            |(((k' + e : ℕ) : ℝ)) - (k' : ℝ)| := by
        rw [hd₂ m (m + d) (Nat.le_add_right _ _),
          hd₁ k' (k' + e) (Nat.le_add_right _ _)]
        rw [Nat.cast_sub (Nat.le_add_right m d), Nat.cast_sub (Nat.le_add_right k' e)]
        push_cast
        ring
      calc |F m (k' + e) - F (m + d) k'|
          ≤ |F m (k' + e) - F m k'| + |F m k' - F (m + d) k'| := htri _ _ _
        _ ≤ C * (e : ℝ) + C * (d : ℝ) := by
            refine add_le_add (hcol m k' e) ?_
            rw [abs_sub_comm]
            exact hrow m d k'
        _ = C * (|(m : ℝ) - (((m + d : ℕ) : ℝ))| +
              |(((k' + e : ℕ) : ℝ)) - (k' : ℝ)|) := by
            rw [← mul_add, hde]
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hde : ((d : ℝ) + (e : ℝ)) =
          |((m : ℝ)) - (((m + d : ℕ) : ℝ))| +
            |((k : ℝ)) - (((k + e : ℕ) : ℝ))| := by
        rw [hd₂ m (m + d) (Nat.le_add_right _ _),
          hd₂ k (k + e) (Nat.le_add_right _ _)]
        rw [Nat.cast_sub (Nat.le_add_right m d), Nat.cast_sub (Nat.le_add_right k e)]
        push_cast
        ring
      calc |F m k - F (m + d) (k + e)|
          ≤ |F m k - F (m + d) k| + |F (m + d) k - F (m + d) (k + e)| := htri _ _ _
        _ ≤ C * (d : ℝ) + C * (e : ℝ) := by
            refine add_le_add ?_ ?_
            · rw [abs_sub_comm]
              exact hrow m d k
            · rw [abs_sub_comm]
              exact hcol (m + d) k e
        _ = C * (|(m : ℝ) - (((m + d : ℕ) : ℝ))| +
              |(k : ℝ) - (((k + e : ℕ) : ℝ))|) := by
            rw [← mul_add, hde]

/-- **Binomial-weighted marked block limit.**  The normalized expected block
pressure at the binomial cell counts converges to the cell weight times the
local marked pressure. -/
theorem tendsto_markedFixedBlockExpectation_binomial
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
      atTop (𝓝 (p t)))
    (w : I) (hw : 0 < (w : ℝ)) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k *
          markedFixedBlockExpectation q
            ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
            ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) m k) / (n : ℝ))
      atTop (𝓝 ((w : ℝ) * p t)) := by
  classical
  set N : ℕ → ℕ := fun n => Nat.floor ((n : ℝ) * (w : ℝ)) with hN
  -- The scale-dependent Lipschitz constant.
  set Lip : ℕ → ℝ := fun M =>
    2 * (((M : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ))) + |t| * G) with hLip
  have hLip0 : ∀ M, 0 ≤ Lip M := by
    intro M
    refine mul_nonneg (by norm_num) (add_nonneg ?_ (mul_nonneg (abs_nonneg t) hG0))
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg M) _) (mul_nonneg hC0 (Nat.cast_nonneg q))
  refine tendsto_binomial_double_sum_of_lipschitz_scale
    (E := fun (M : ℕ) (m k : ℕ) =>
      markedFixedBlockExpectation q (M : ℝ) t kin g α β (M : ℝ≥0) m k)
    (C := Lip) (p := p t) hLip0 ?_ ?_ w hw ?_
  · -- Stability of the block expectation in the two sizes.
    intro M m k m' k'
    refine abs_pair_sub_le_of_row_col
      (F := fun (m k : ℕ) =>
        markedFixedBlockExpectation q (M : ℝ) t kin g α β (M : ℝ≥0) m k)
      (C := Lip M) ?_ ?_ m k m' k'
    · intro m δ k
      have h := abs_markedFixedBlockExpectation_sub_le_add_rows q (t := t)
        (Nat.cast_nonneg M) hC0 hG0 hkin hkin_bound hg hgb α β (M : ℝ≥0) m δ k
      simpa only [Lip] using h
    · intro m k δ
      have h := abs_markedFixedBlockExpectation_sub_le_add_cols q (t := t)
        (Nat.cast_nonneg M) hC0 hG0 hkin hkin_bound hg hgb α β (M : ℝ≥0) m k δ
      simpa only [Lip] using h
  · -- The diagonal limit.
    exact tendsto_markedFixedBlockExpectation_diagonal q hq hC0 hG0
      hkin hkin_bound hg hgb α β p hp t
  · -- The vanishing count-deviation error.
    have hq4 : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
    have hexp : (2 : ℝ) / (q : ℝ) < 1 / 2 := by
      rw [div_lt_iff₀ hqpos]
      nlinarith
    set y : ℝ := 1 / 2 - 2 / (q : ℝ) with hy
    have hy0 : 0 < y := by rw [hy]; linarith
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-y)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hy0).comp tendsto_natCast_atTop_atTop
    have hpowhalf : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
    -- The explicit majorant.
    have hmaj : Tendsto (fun n : ℕ =>
        8 * (C * (q : ℝ)) * (w : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (-y)
          + 8 * (|t| * G) * (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ =>
          8 * (C * (q : ℝ)) * (w : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (-y))
          atTop (𝓝 (8 * (C * (q : ℝ)) * (w : ℝ) ^ (2 / (q : ℝ)) * 0)) :=
        hpow.const_mul _
      have h2 : Tendsto (fun n : ℕ =>
          8 * (|t| * G) * (n : ℝ) ^ (-(1 / 2 : ℝ)))
          atTop (𝓝 (8 * (|t| * G) * 0)) :=
        hpowhalf.const_mul _
      have hsum := h1.add h2
      simpa using hsum
    -- The function whose limit is required.
    have hmain : Tendsto (fun n : ℕ =>
        2 * Lip (N n) * (Real.sqrt ((n : ℝ) * (w : ℝ)) + 1) / (n : ℝ))
        atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hmaj
      · filter_upwards with n
        have := hLip0 (N n)
        positivity
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
        have hwn0 : (0 : ℝ) ≤ (n : ℝ) * (w : ℝ) := mul_nonneg hn0 hw.le
        have hwnpos : (0 : ℝ) < (n : ℝ) * (w : ℝ) := mul_pos hnpos hw
        have hNle : ((N n : ℕ) : ℝ) ≤ (n : ℝ) * (w : ℝ) := by
          rw [hN]
          exact Nat.floor_le hwn0
        have hN0 : (0 : ℝ) ≤ ((N n : ℕ) : ℝ) := Nat.cast_nonneg _
        have hrpow : ((N n : ℕ) : ℝ) ^ (2 / (q : ℝ)) ≤
            ((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) :=
          Real.rpow_le_rpow hN0 hNle (by positivity)
        have hstepA : ((N n : ℕ) : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) ≤
            ((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right hrpow (mul_nonneg hC0 (Nat.cast_nonneg q))
        have hA : ((N n : ℕ) : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G ≤
            ((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
          linarith [hstepA]
        have hAb0 : (0 : ℝ) ≤
            ((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G :=
          add_nonneg
            (mul_nonneg (Real.rpow_nonneg hwn0 _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
            (mul_nonneg (abs_nonneg t) hG0)
        have hsqrtle : Real.sqrt ((n : ℝ) * (w : ℝ)) ≤ Real.sqrt (n : ℝ) :=
          Real.sqrt_le_sqrt (by nlinarith [w.2.2])
        have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [Real.le_sqrt (by norm_num) hn0]
          exact_mod_cast hn
        have hsqt : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
        have hZ0 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * (w : ℝ)) + 1 := by positivity
        -- Bound the numerator.
        have hnum1 : 2 * Lip (N n) * (Real.sqrt ((n : ℝ) * (w : ℝ)) + 1) ≤
            4 * (((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
              (Real.sqrt ((n : ℝ) * (w : ℝ)) + 1) := by
          rw [hLip]
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)) hZ0
          nlinarith
        have hZ2 : Real.sqrt ((n : ℝ) * (w : ℝ)) + 1 ≤ 2 * Real.sqrt (n : ℝ) := by
          linarith
        have hnum2 : 4 * (((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
              (Real.sqrt ((n : ℝ) * (w : ℝ)) + 1) ≤
            4 * (((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
              (2 * Real.sqrt (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hZ2 (mul_nonneg (by norm_num) hAb0)
        -- Identities for the two powers.
        have hinv : (n : ℝ)⁻¹ = (n : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg hn0, Real.rpow_one]
        have hfirst : (n : ℝ) ^ (2 / (q : ℝ)) * Real.sqrt (n : ℝ) / (n : ℝ) =
            (n : ℝ) ^ (-y) := by
          rw [hsqt, ← Real.rpow_add hnpos, div_eq_mul_inv, hinv, ← Real.rpow_add hnpos]
          congr 1
          rw [hy]
          ring
        have hhalf : Real.sqrt (n : ℝ) / (n : ℝ) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [hsqt, div_eq_mul_inv, hinv, ← Real.rpow_add hnpos]
          congr 1
          norm_num
        have hmulrw : ((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) =
            (n : ℝ) ^ (2 / (q : ℝ)) * (w : ℝ) ^ (2 / (q : ℝ)) :=
          Real.mul_rpow hn0 hw.le
        calc 2 * Lip (N n) * (Real.sqrt ((n : ℝ) * (w : ℝ)) + 1) / (n : ℝ)
            ≤ 4 * (((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
                (Real.sqrt ((n : ℝ) * (w : ℝ)) + 1) / (n : ℝ) :=
              div_le_div_of_nonneg_right hnum1 hn0
          _ ≤ 4 * (((n : ℝ) * (w : ℝ)) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
                (2 * Real.sqrt (n : ℝ)) / (n : ℝ) :=
              div_le_div_of_nonneg_right hnum2 hn0
          _ = 8 * ((n : ℝ) ^ (2 / (q : ℝ)) * (w : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) +
                |t| * G) * Real.sqrt (n : ℝ) / (n : ℝ) := by
              rw [hmulrw]
              ring
          _ = 8 * (C * (q : ℝ)) * (w : ℝ) ^ (2 / (q : ℝ)) *
                ((n : ℝ) ^ (2 / (q : ℝ)) * Real.sqrt (n : ℝ) / (n : ℝ))
              + 8 * (|t| * G) * (Real.sqrt (n : ℝ) / (n : ℝ)) := by
              ring
          _ = 8 * (C * (q : ℝ)) * (w : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (-y)
              + 8 * (|t| * G) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [hfirst, hhalf]
    simpa only [hN] using hmain

end OTSelector.Probability
