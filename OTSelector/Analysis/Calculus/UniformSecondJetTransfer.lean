import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Analysis.Calculus.UniformSecondJetTransfer

Conditions: A continuous bilinear form, a stationary Peano expansion, and the explicitly uniform bounds on the second jets and O(w) displacements.

Objects: Diagonal quadratic difference estimates and uniform transfer of the stationary second-order expansion.

Proof detail: Expand the difference of bilinear diagonals into two mixed terms, bound with the operator norm, then combine the stationary remainder and displacement error at the given scales.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/html/sec_taylor.html): Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).
- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation: Locally proved quantitative Taylor/Peano transfer; uniformity and constants are supplied or derived exactly as in the signatures.
-/

/-!
# Quantitative uniform transfer of stationary second jets

These estimates separate the analytic inputs needed for uniform transfer: a bounded
quadratic coefficient, uniformly bounded endpoint displacements, a small mismatch,
and genuine quadratic action remainders. They do not supply those inputs for a
Finsler endpoint family.
-/

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative diagonal comparison, with no symmetry assumption. -/
theorem bilinear_diagonal_sub_norm_le
    (B : E →L[ℝ] E →L[ℝ] ℝ) {u v : E} {K δ L r : ℝ}
    (hB : ‖B‖ ≤ K) (hu : ‖u‖ ≤ L * r) (hv : ‖v‖ ≤ L * r)
    (huv : ‖u - v‖ ≤ δ * r) :
    ‖B u u - B v v‖ ≤ 2 * K * δ * L * r ^ 2 := by
  have hid : B u u - B v v = B (u - v) u + B v (u - v) := by
    simp only [map_sub, sub_apply]
    ring
  rw [hid]
  calc
    ‖B (u - v) u + B v (u - v)‖ ≤ ‖B (u - v) u‖ + ‖B v (u - v)‖ :=
      norm_add_le _ _
    _ ≤ K * (δ * r) * (L * r) + K * (L * r) * (δ * r) :=
      add_le_add (B.le_of_opNorm₂_le_of_le hB huv hu)
        (B.le_of_opNorm₂_le_of_le hB hv huv)
    _ = 2 * K * δ * L * r ^ 2 := by ring

/-- Explicit stationary Peano transfer. The two remainders are those of the same
actual scalar action at its common center, not assumed bounds on the conclusion. -/
theorem stationary_peano_comp_sub_norm_le
    (e : E → ℝ) (x : E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {X Y : E} {K δ ρ L r : ℝ}
    (hρ : 0 ≤ ρ)
    (hB : ‖B‖ ≤ K) (hX : ‖X - x‖ ≤ L * r) (hY : ‖Y - x‖ ≤ L * r)
    (hXY : ‖X - Y‖ ≤ δ * r)
    (heX : ‖e X - e x - (1 / 2 : ℝ) * B (X - x) (X - x)‖ ≤ ρ * ‖X - x‖ ^ 2)
    (heY : ‖e Y - e x - (1 / 2 : ℝ) * B (Y - x) (Y - x)‖ ≤ ρ * ‖Y - x‖ ^ 2) :
    ‖e X - e Y‖ ≤ (2 * ρ * L ^ 2 + K * δ * L) * r ^ 2 := by
  have hq := bilinear_diagonal_sub_norm_le B hB hX hY
    (show ‖(X - x) - (Y - x)‖ ≤ δ * r by
      simpa only [sub_sub_sub_cancel_right] using hXY)
  have hsX : ‖X - x‖ ^ 2 ≤ (L * r) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hX 2
  have hsY : ‖Y - x‖ ^ 2 ≤ (L * r) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hY 2
  have hid : e X - e Y =
      ((e X - e x - (1 / 2 : ℝ) * B (X - x) (X - x)) -
        (e Y - e x - (1 / 2 : ℝ) * B (Y - x) (Y - x))) +
      (1 / 2 : ℝ) * (B (X - x) (X - x) - B (Y - x) (Y - x)) := by ring
  rw [hid]
  calc
    _ ≤ (‖e X - e x - (1 / 2 : ℝ) * B (X - x) (X - x)‖ +
        ‖e Y - e x - (1 / 2 : ℝ) * B (Y - x) (Y - x)‖) +
        ‖(1 / 2 : ℝ) * (B (X - x) (X - x) - B (Y - x) (Y - x))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ρ * (L * r) ^ 2 + ρ * (L * r) ^ 2 +
        (1 / 2 : ℝ) * (2 * K * δ * L * r ^ 2) := by
      apply add_le_add
      · exact add_le_add (heX.trans (mul_le_mul_of_nonneg_left hsX hρ))
          (heY.trans (mul_le_mul_of_nonneg_left hsY hρ))
      · rw [norm_mul]
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = (2 * ρ * L ^ 2 + K * δ * L) * r ^ 2 := by ring

/-- Uniform transfer over any index set. A common small mismatch and common
stationary quadratic remainders yield one radius for all members of the family.
The inputs can in particular be supplied by compact endpoint and ambient jet bounds. -/
theorem uniform_stationary_peano_transfer
    {I T : Type*} (S : Set I) (e : I → E → ℝ) (x : I → E)
    (B : I → E →L[ℝ] E →L[ℝ] ℝ) (X Y : I → T → E) (scale : T → ℝ)
    {K L R : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hR : 0 < R)
    (hB : ∀ i ∈ S, ‖B i‖ ≤ K)
    (hsize : ∀ i ∈ S, ∀ t, scale t < R →
      ‖X i t - x i‖ ≤ L * scale t ∧ ‖Y i t - x i‖ ≤ L * scale t)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r →
      ‖X i t - Y i t‖ ≤ η * scale t ∧
      ‖e i (X i t) - e i (x i) -
        (1 / 2 : ℝ) * B i (X i t - x i) (X i t - x i)‖ ≤
          η * ‖X i t - x i‖ ^ 2 ∧
      ‖e i (Y i t) - e i (x i) -
        (1 / 2 : ℝ) * B i (Y i t - x i) (Y i t - x i)‖ ≤
          η * ‖Y i t - x i‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r →
      ‖e i (X i t) - e i (Y i t)‖ ≤ ε * (scale t) ^ 2 := by
  let C : ℝ := 2 * L ^ 2 + K * L
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg hK hL)
  have hC1 : 0 < C + 1 := by linarith
  let η : ℝ := ε / (C + 1)
  have hη : 0 < η := div_pos hε hC1
  have hηbound : η * C ≤ ε := by
    have heq : η * (C + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hC1)
    nlinarith
  obtain ⟨r, hr, hdata⟩ := hsmall η hη
  refine ⟨min R r, lt_min hR hr, ?_⟩
  intro i hi t ht
  obtain ⟨hX, hY⟩ := hsize i hi t (ht.trans_le (min_le_left _ _))
  obtain ⟨hXY, heX, heY⟩ := hdata i hi t (ht.trans_le (min_le_right _ _))
  have hbound := stationary_peano_comp_sub_norm_le (e i) (x i) (B i)
    hη.le (hB i hi) hX hY hXY heX heY
  have hcoeff : 2 * η * L ^ 2 + K * η * L = η * C := by dsimp [C]; ring
  rw [hcoeff] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hηbound (sq_nonneg _))

end OTSelector.Geometry
