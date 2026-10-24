import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Finite.UnitCubeGridHierarchy

## Lemma skeleton

* **Conditions:** A positive block count m, m≤2^J≤2m for the diameter bound, levels k≤J, and points in the half-open unit cube.

* **Objects:** Padded multiscale floor labels; refinement, cardinalities and squared cell diameters.

* **Proof detail:** Take floor(mx) at the leaves, coarsen by integer division and apply the quotient-remainder bounds coordinatewise. Summing squared coordinate errors gives the stated dimension-dependent constant.

## Mathematical sources

- [Thomas W. Judson, Abstract Algebra: Theory and Applications (author online edition)](https://twjudson.github.io/aata-files/aata-html/integers-section-division-algorithm.html): Section 2.2, Theorem 2.2.1 (Division Algorithm).
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Local non-dyadic coding and its explicit constant; no probabilistic statement is part of this source attribution.
-/

/-!
# A non-dyadic uniform grid hierarchy on the unit cube

For an arbitrary block count `m` and a depth `J` with `m ≤ 2 ^ J`, a coordinate
of the unit cube is assigned the leaf block `⌊m * x⌋`.  Grouping leaf blocks by
division by `2 ^ (J - k)` gives a level-`k` cell label, so level `0` is the root
and level `J` is the leaf grid.  The level-`k` labels take values in the padded
type `Fin (2 ^ k + 1)`, which has at least as many values as the true number
`(2 ^ k + 1) ^ q` of cell labels; the padding keeps the label type independent
of `m`.

The main results are:

* `gridCellLabel_nested`: a finer level determines every coarser level;
* `gridCellLabel_root`: at level `0` all labels coincide;
* `gridCellLabel_sqDist_le`: two unit-cube points with equal level-`k` labels
  have squared distance at most `16 * q * (1 / 4) ^ k`, provided the depth
  satisfies `2 ^ J ≤ 2 * m` (so that the non-dyadic block width is comparable
  to the dyadic cell width `2 ^ (-k)`);
* `gridCellLabel_card`: the padded label type has cardinality
  `(2 ^ k + 1) ^ q`.

These are the deterministic geometric inputs for the multi-scale repair of the
non-dyadic block hierarchy.  The arithmetic is the same as in
`OTSelector.Finite.BlockIndexHierarchy` and `OTSelector.Finite.DyadicCellCost`,
with the dyadic floor `⌊2 ^ k * x⌋` replaced by the block floor `⌊m * x⌋`.
-/

open scoped BigOperators

namespace OTSelector.Probability

/-- The leaf block index of one coordinate of a point in the unit cube.

The modulo makes the definition total: on the unit cube,
`⌊m * x⌋` already lies below `m`, and `gridLeaf_val_of_mem` records this. -/
noncomputable def gridLeaf (m : ℕ) (hm : 0 < m) (x : ℝ) : Fin m :=
  ⟨⌊(m : ℝ) * x⌋₊ % m, Nat.mod_lt _ hm⟩

/-- On the unit cube the modulo in `gridLeaf` is redundant: the leaf index is
exactly the floor `⌊m * x⌋`. -/
theorem gridLeaf_val_of_mem {m : ℕ} (hm : 0 < m) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) : (gridLeaf m hm x).val = ⌊(m : ℝ) * x⌋₊ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnonneg : 0 ≤ (m : ℝ) * x := mul_nonneg hmR.le hx0
  have hlt : ⌊(m : ℝ) * x⌋₊ < m := by
    have hle : ((⌊(m : ℝ) * x⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) * x := Nat.floor_le hnonneg
    have hlt' : (m : ℝ) * x < (m : ℝ) := by
      calc
        (m : ℝ) * x < (m : ℝ) * 1 := mul_lt_mul_of_pos_left hx1 hmR
        _ = (m : ℝ) := mul_one _
    exact_mod_cast lt_of_le_of_lt hle hlt'
  dsimp only [gridLeaf]
  exact Nat.mod_eq_of_lt hlt

/-- The level-`k` grid cell label of a point, with the padded cell space
`Fin q → Fin (2 ^ k + 1)`.  At depth `J` the leaf index `a < m ≤ 2 ^ J` is
divided by `2 ^ (J - k)`; thus level `0` is the root and level `J` is the leaf
grid.  When `k > J` the divisor is `1` and the label is the leaf index itself.
-/
noncomputable def gridCellLabel (q m J k : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (x : Fin q → ℝ) : Fin q → Fin (2 ^ k + 1) :=
  fun l => ⟨(gridLeaf m hm (x l)).val / 2 ^ (J - k), by
    have ha : (gridLeaf m hm (x l)).val < 2 ^ J :=
      lt_of_lt_of_le (gridLeaf m hm (x l)).isLt hJ
    have hd : 0 < 2 ^ (J - k) := Nat.pow_pos (by norm_num : 0 < 2)
    have hlt : (gridLeaf m hm (x l)).val / 2 ^ (J - k) < 2 ^ k := by
      by_cases hkJ : k ≤ J
      · rw [Nat.div_lt_iff_lt_mul hd]
        calc
          (gridLeaf m hm (x l)).val < 2 ^ J := ha
          _ = 2 ^ k * 2 ^ (J - k) := by
            rw [← pow_add]
            congr 1
            omega
      · have hJk : J < k := Nat.lt_of_not_le hkJ
        have hsub : J - k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hJk)
        rw [hsub, pow_zero, Nat.div_one]
        exact lt_of_lt_of_le ha
          (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_of_lt hJk))
    omega⟩

/-- Nestedness: a finer level determines every coarser level. -/
theorem gridCellLabel_nested {q m J k l : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hkl : k ≤ l) (hlJ : l ≤ J) {x y : Fin q → ℝ}
    (h : gridCellLabel q m J l hm hJ x = gridCellLabel q m J l hm hJ y) :
    gridCellLabel q m J k hm hJ x = gridCellLabel q m J k hm hJ y := by
  funext i
  apply Fin.ext
  have hi : (gridLeaf m hm (x i)).val / 2 ^ (J - l) =
      (gridLeaf m hm (y i)).val / 2 ^ (J - l) := by
    have := congrArg Fin.val (congrFun h i)
    simpa only [gridCellLabel] using this
  have hpow : 2 ^ (J - l) * 2 ^ (l - k) = 2 ^ (J - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : (gridLeaf m hm (x i)).val / 2 ^ (J - k) =
      ((gridLeaf m hm (x i)).val / 2 ^ (J - l)) / 2 ^ (l - k) := by
    rw [Nat.div_div_eq_div_mul, hpow]
  have hdiv' : (gridLeaf m hm (y i)).val / 2 ^ (J - k) =
      ((gridLeaf m hm (y i)).val / 2 ^ (J - l)) / 2 ^ (l - k) := by
    rw [Nat.div_div_eq_div_mul, hpow]
  simp only [gridCellLabel]
  rw [hdiv, hdiv', hi]

/-- At level `0` every label is the root label: the divisor is `2 ^ J` and the
leaf index is below `m ≤ 2 ^ J`, so the quotient vanishes. -/
theorem gridCellLabel_root {q m J : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (x y : Fin q → ℝ) :
    gridCellLabel q m J 0 hm hJ x = gridCellLabel q m J 0 hm hJ y := by
  funext i
  apply Fin.ext
  simp only [gridCellLabel, Nat.sub_zero]
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le (gridLeaf m hm (x i)).isLt hJ),
    Nat.div_eq_of_lt (lt_of_lt_of_le (gridLeaf m hm (y i)).isLt hJ)]

/-- The level-`k` label is a function of the level-`l` label for `k ≤ l`: it is
obtained coordinatewise by dividing the finer label by `2 ^ (l - k)`. -/
theorem gridCellLabel_coarsen_eq {q m J k l : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hkl : k ≤ l) (hlJ : l ≤ J) (x : Fin q → ℝ) (i : Fin q) :
    (gridCellLabel q m J k hm hJ x i).val =
      (gridCellLabel q m J l hm hJ x i).val / 2 ^ (l - k) := by
  simp only [gridCellLabel]
  rw [Nat.div_div_eq_div_mul]
  congr 1
  rw [← pow_add]
  congr 1
  omega

/-- The padded level-`k` cell-label type has cardinality `(2 ^ k + 1) ^ q`. -/
theorem gridCellLabel_card (q k : ℕ) :
    Fintype.card (Fin q → Fin (2 ^ k + 1)) = (2 ^ k + 1) ^ q := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Natural division lemma: equal quotients by `d > 0` force the distances in
both directions to be below `d`.  Writing `a = d * (a / d) + a % d` and
`b = d * (b / d) + b % d`, the two remainders are both below `d` and their
difference is the distance between `a` and `b`. -/
private theorem sub_lt_of_div_eq {a b d : ℕ} (hd : 0 < d) (h : a / d = b / d) :
    b - a < d ∧ a - b < d := by
  have ha : (a / d) * d ≤ a ∧ a ≤ (a / d) * d + d - 1 :=
    (Nat.div_eq_iff (k := d) (x := a) (y := a / d) hd).mp rfl
  have hb : (b / d) * d ≤ b ∧ b ≤ (b / d) * d + d - 1 :=
    (Nat.div_eq_iff (k := d) (x := b) (y := b / d) hd).mp rfl
  rw [← h] at hb
  omega

/-- Two unit-cube coordinates sharing a level-`k` grid label differ by at most
`4 * (2 ^ k)⁻¹`.  With `d = 2 ^ (J - k)` the leaf indices differ by less than
`d`, hence `|m * x - m * y| < d`; dividing by `m` and using
`2 ^ J ≤ 2 * m` gives `|x - y| < d / m ≤ 2 * 2 ^ (-k)`. -/
private theorem abs_sub_le_of_gridCellLabel_eq
    {q m J k : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    (hk : k ≤ J) {x y : Fin q → ℝ}
    (hx : ∀ l, 0 ≤ x l ∧ x l < 1) (hy : ∀ l, 0 ≤ y l ∧ y l < 1)
    (h : gridCellLabel q m J k hm hJ x = gridCellLabel q m J k hm hJ y) (l : Fin q) :
    |x l - y l| ≤ 4 * ((2 : ℝ) ^ k)⁻¹ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < 2 ^ (J - k) := Nat.pow_pos (by norm_num : 0 < 2)
  have hval : (gridLeaf m hm (x l)).val / 2 ^ (J - k) =
      (gridLeaf m hm (y l)).val / 2 ^ (J - k) := by
    have := congrArg Fin.val (congrFun h l)
    simpa only [gridCellLabel] using this
  have hdist := sub_lt_of_div_eq hd hval
  have hxa := gridLeaf_val_of_mem hm (hx l).1 (hx l).2
  have hya := gridLeaf_val_of_mem hm (hy l).1 (hy l).2
  -- Integer inequalities for the floors.
  have hdistx := hdist.2
  have hdisty := hdist.1
  rw [hxa, hya] at hdistx hdisty
  have hIntx : ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℤ) - ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℤ) <
      ((2 ^ (J - k) : ℕ) : ℤ) := by omega
  have hInty : ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℤ) - ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℤ) <
      ((2 ^ (J - k) : ℕ) : ℤ) := by omega
  have hleIntx : ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℤ) - ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℤ) ≤
      ((2 ^ (J - k) : ℕ) : ℤ) - 1 := by omega
  have hleInty : ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℤ) - ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℤ) ≤
      ((2 ^ (J - k) : ℕ) : ℤ) - 1 := by omega
  have hleRx : ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℝ) - ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℝ) ≤
      ((2 ^ (J - k) : ℕ) : ℝ) - 1 := by exact_mod_cast hleIntx
  have hleRy : ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℝ) - ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℝ) ≤
      ((2 ^ (J - k) : ℕ) : ℝ) - 1 := by exact_mod_cast hleInty
  -- Floor sandwich around `m * x` and `m * y`.
  have hAx : ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) * x l :=
    Nat.floor_le (mul_nonneg hmR.le (hx l).1)
  have hBx : (m : ℝ) * x l < ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((m : ℝ) * x l)
    linarith
  have hAy : ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) * y l :=
    Nat.floor_le (mul_nonneg hmR.le (hy l).1)
  have hBy : (m : ℝ) * y l < ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((m : ℝ) * y l)
    linarith
  have hsubxy : (m : ℝ) * x l - (m : ℝ) * y l < ((2 ^ (J - k) : ℕ) : ℝ) := by
    have h1 : (m : ℝ) * x l - (m : ℝ) * y l <
        ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℝ) + 1 -
          ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℝ) := by
      linarith [hBx, hAy]
    linarith [h1, hleRx]
  have hsubyx : (m : ℝ) * y l - (m : ℝ) * x l < ((2 ^ (J - k) : ℕ) : ℝ) := by
    have h1 : (m : ℝ) * y l - (m : ℝ) * x l <
        ((⌊(m : ℝ) * y l⌋₊ : ℕ) : ℝ) + 1 -
          ((⌊(m : ℝ) * x l⌋₊ : ℕ) : ℝ) := by
      linarith [hBy, hAx]
    linarith [h1, hleRy]
  have habs_m : |(m : ℝ) * x l - (m : ℝ) * y l| < ((2 ^ (J - k) : ℕ) : ℝ) := by
    rw [abs_lt]
    exact ⟨by linarith, hsubxy⟩
  -- Divide the bound by `m > 0`.
  have hfactor : (m : ℝ) * x l - (m : ℝ) * y l = (m : ℝ) * (x l - y l) := by ring
  rw [hfactor, abs_mul, abs_of_pos hmR] at habs_m
  have hlt_div : |x l - y l| < ((2 ^ (J - k) : ℕ) : ℝ) / (m : ℝ) := by
    rw [lt_div_iff₀ hmR]
    calc
      |x l - y l| * (m : ℝ) = (m : ℝ) * |x l - y l| := by ring
      _ < ((2 ^ (J - k) : ℕ) : ℝ) := habs_m
  -- Bound the non-dyadic cell width by the dyadic one.
  have hdcast : ((2 ^ (J - k) : ℕ) : ℝ) = (2 : ℝ) ^ (J - k) := by
    rw [Nat.cast_pow]
    norm_num
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpowJ : (2 : ℝ) ^ J = (2 : ℝ) ^ (J - k) * (2 : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  have hJ2R : (2 : ℝ) ^ J ≤ 2 * (m : ℝ) := by exact_mod_cast hJ2
  have hdm : ((2 ^ (J - k) : ℕ) : ℝ) / (m : ℝ) ≤ 4 * ((2 : ℝ) ^ k)⁻¹ := by
    have hmain : ((2 ^ (J - k) : ℕ) : ℝ) / (m : ℝ) ≤ 2 * ((2 : ℝ) ^ k)⁻¹ := by
      rw [hdcast, div_le_iff₀ hmR]
      calc
        (2 : ℝ) ^ (J - k) = (2 : ℝ) ^ J / (2 : ℝ) ^ k := by
          rw [hpowJ, mul_div_cancel_right₀ _ h2k.ne']
        _ ≤ (2 * (m : ℝ)) / (2 : ℝ) ^ k :=
          div_le_div_of_nonneg_right hJ2R h2k.le
        _ = 2 * ((2 : ℝ) ^ k)⁻¹ * (m : ℝ) := by ring
    calc
      ((2 ^ (J - k) : ℕ) : ℝ) / (m : ℝ) ≤ 2 * ((2 : ℝ) ^ k)⁻¹ := hmain
      _ ≤ 4 * ((2 : ℝ) ^ k)⁻¹ := by
        have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
        linarith
  exact le_of_lt (lt_of_lt_of_le hlt_div hdm)

/-- Geometric input of the multi-scale repair: if two unit-cube points have
equal level-`k` grid labels and the depth satisfies `m ≤ 2 ^ J ≤ 2 * m`, then
their squared Euclidean distance is at most `16 * q * (1 / 4) ^ k`.

Per coordinate the leaf indices differ by less than `d = 2 ^ (J - k)`, so
`|x - y| ≤ d / m ≤ 2 * 2 ^ (-k) ≤ 4 * 2 ^ (-k)`, and squaring gives
`(x - y) ^ 2 ≤ 16 * (1 / 4) ^ k`; summing over the `q` coordinates yields the
claim. -/
theorem gridCellLabel_sqDist_le {q m J k : ℕ} (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m) (hk : k ≤ J) {x y : Fin q → ℝ}
    (hx : ∀ l, 0 ≤ x l ∧ x l < 1) (hy : ∀ l, 0 ≤ y l ∧ y l < 1)
    (h : gridCellLabel q m J k hm hJ x = gridCellLabel q m J k hm hJ y) :
    ∑ l, (x l - y l) ^ 2 ≤ 16 * (q : ℝ) * (1 / 4 : ℝ) ^ k := by
  have hterm : ∀ l, (x l - y l) ^ 2 ≤ 16 * (1 / 4 : ℝ) ^ k := by
    intro l
    have hle := abs_sub_le_of_gridCellLabel_eq hm hJ hJ2 hk hx hy h l
    have hpow : (((2 : ℝ) ^ k)⁻¹) ^ 2 = (1 / 4 : ℝ) ^ k := by
      rw [inv_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul, ← inv_pow]
      norm_num
    calc
      (x l - y l) ^ 2 = |x l - y l| ^ 2 := by rw [sq_abs]
      _ ≤ (4 * ((2 : ℝ) ^ k)⁻¹) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
      _ = 16 * (((2 : ℝ) ^ k)⁻¹) ^ 2 := by ring
      _ = 16 * (1 / 4 : ℝ) ^ k := by rw [hpow]
  calc
    ∑ l, (x l - y l) ^ 2 ≤ ∑ _l : Fin q, 16 * (1 / 4 : ℝ) ^ k :=
      Finset.sum_le_sum fun l _ => hterm l
    _ = 16 * (q : ℝ) * (1 / 4 : ℝ) ^ k := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end OTSelector.Probability
