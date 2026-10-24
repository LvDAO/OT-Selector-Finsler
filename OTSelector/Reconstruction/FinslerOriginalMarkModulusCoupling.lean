import OTSelector.Reconstruction.FinslerOriginalMatchingMomentBound

/-!
# Mark modulus coupling rate

This module produces input (b) of `FinslerOriginalHupperAssembly`: the normalized
coupling integral of the marked-edge error is `o (1)`, i.e. the mark rate vanishes
at the pairing scale.  The chain is deterministic and is split into its three
honest pieces.

1. **Single-edge mark-Lipschitz transfer**
   (`abs_markedEdgeError_le_of_markLipschitz`).  A marked edge cost is
   `edge = scale * kin + t * g` with `scale = L ^ (2 / q) ≥ 0`.  If on the pairing
   family `kin` and `g` are mark-Lipschitz with constants `Lk`, `Lg` in the mark
   distance `d`, then the edge-cost difference of two coupled marks is at most
   `(scale * Lk + |t| * Lg) * d`.  This is the mark modulus estimate in its
   sharpest deterministic form.

2. **Moment form** (`abs_markedEdgeError_le_of_momentMarkLipschitz`).  Feeding the
   matching moment bound of `FinslerOriginalPhysicalCostRemainder` /
   `FinslerOriginalMatchingMomentBound`: when the kinetic mark-Lipschitz bound is
   paid by the total squared matched displacement `sum v l ^ 2`,
   `|kin₁ - kin₂| ≤ Lk * d * sum v l ^ 2`, the edge error is at most
   `(scale * Lk * sum v l ^ 2 + |t| * Lg) * d`.  Consequently the min-count
   weighted sum of edge errors is at most a *budget* `budget L` times the mark
   modulus `ω L`, where `budget` is bounded by the pressure scale (matching
   moment) and the count.

3. **Vanishing normalized rate** (`tendsto_markRate_zero`).  If the mark modulus
   `ω L -> 0` (the marked point law coupling has vanishing mark distance at the
   pairing scale) and the moment/pressure budget converges to a finite `b`,
   then the normalized coupling integral `rate L = budget L * ω L` tends to `0`.
   This is exactly the `markRate -> 0` hypothesis consumed by
   `FinslerOriginalHupperAssembly`.

Remaining analytic input, stated precisely: local Lipschitz constants `Lk`, `Lg` of
`kin` and `g` on the pairing neighbourhood family of marks (the compact-root
smoothness lane), and a coupling of the marked point law with the reference one
whose mark modulus `ω L -> 0` at the pairing scale.  Everything else is proved
here; no mark-kernel modulus or Lipschitz constant is assumed silently.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- **Single-edge mark-Lipschitz transfer.**  The marked edge cost difference of
two coupled marks is controlled by the mark distance with the mark-Lipschitz
constants of `kin` and `g`. -/
theorem abs_markedEdgeError_le_of_markLipschitz
    {scale t Lk Lg d kinA kinB gA gB : ℝ} (hscale : 0 ≤ scale)
    (hk : |kinA - kinB| ≤ Lk * d) (hg : |gA - gB| ≤ Lg * d) :
    |(scale * kinA + t * gA) - (scale * kinB + t * gB)| ≤
      (scale * Lk + |t| * Lg) * d := by
  have hdecomp : (scale * kinA + t * gA) - (scale * kinB + t * gB) =
      scale * (kinA - kinB) + t * (gA - gB) := by ring
  rw [hdecomp]
  have hscale_abs : |scale| = scale := abs_of_nonneg hscale
  have h1 : |scale * (kinA - kinB)| = scale * |kinA - kinB| := by
    rw [abs_mul, hscale_abs]
  have h2 : |t * (gA - gB)| = |t| * |gA - gB| := by rw [abs_mul]
  have htri : |scale * (kinA - kinB) + t * (gA - gB)| ≤
      |scale * (kinA - kinB)| + |t * (gA - gB)| := by
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le (scale * (kinA - kinB)), neg_abs_le (t * (gA - gB))]
    · nlinarith [le_abs_self (scale * (kinA - kinB)), le_abs_self (t * (gA - gB))]
  calc |scale * (kinA - kinB) + t * (gA - gB)|
      ≤ |scale * (kinA - kinB)| + |t * (gA - gB)| := htri
    _ = scale * |kinA - kinB| + |t| * |gA - gB| := by rw [h1, h2]
    _ ≤ scale * (Lk * d) + |t| * (Lg * d) := by
        have h1' := mul_le_mul_of_nonneg_left hk hscale
        have h2' := mul_le_mul_of_nonneg_left hg (abs_nonneg t)
        linarith
    _ = (scale * Lk + |t| * Lg) * d := by ring

/-- **Moment form of the mark-Lipschitz transfer.**  When the kinetic part is
mark-Lipschitz with a constant paid by the total squared matched displacement
`sum v l ^ 2`, the edge error is bounded by
`(scale * Lk * sum v l ^ 2 + |t| * Lg) * d`. -/
theorem abs_markedEdgeError_le_of_momentMarkLipschitz {n : Type*} [Fintype n]
    {v : n → ℝ} {scale t Lk Lg d kinA kinB gA gB : ℝ} (hscale : 0 ≤ scale)
    (hk : |kinA - kinB| ≤ Lk * d * (∑ l, v l ^ 2))
    (hg : |gA - gB| ≤ Lg * d) :
    |(scale * kinA + t * gA) - (scale * kinB + t * gB)| ≤
      (scale * Lk * (∑ l, v l ^ 2) + |t| * Lg) * d := by
  have h := abs_markedEdgeError_le_of_markLipschitz (scale := scale) (t := t)
    (Lk := Lk * (∑ l, v l ^ 2)) (Lg := Lg) (d := d) hscale (by
      calc |kinA - kinB| ≤ Lk * d * (∑ l, v l ^ 2) := hk
        _ = (Lk * (∑ l, v l ^ 2)) * d := by ring) hg
  calc |(scale * kinA + t * gA) - (scale * kinB + t * gB)|
      ≤ (scale * (Lk * (∑ l, v l ^ 2)) + |t| * Lg) * d := h
    _ = (scale * Lk * (∑ l, v l ^ 2) + |t| * Lg) * d := by ring

/-- **Sum form: the min-count weighted coupling integral is at most the budget
times the mark modulus.**  If every matched pair has mark distance at most `ω`
and the per-pair moment/kinetic budget is at most `B`, then the total coupling
edge error is at most `B * ω * count`. -/
theorem sum_markedEdgeError_le_of_markModulus {N : ℕ}
    {kinA kinB gA gB d : Fin N → ℝ} {scale t Lk Lg ω B : ℝ}
    (hscale : 0 ≤ scale) (hLk : 0 ≤ Lk) (hLg : 0 ≤ Lg) (_hω : 0 ≤ ω)
    (hd0 : ∀ i, 0 ≤ d i)
    (hper : ∀ i, |kinA i - kinB i| ≤ Lk * d i)
    (hgper : ∀ i, |gA i - gB i| ≤ Lg * d i)
    (hd : ∀ i, d i ≤ ω)
    (hbudget : (scale * Lk + |t| * Lg) ≤ B)
    (hB : 0 ≤ B) :
    ∑ i, |(scale * kinA i + t * gA i) - (scale * kinB i + t * gB i)| ≤
      B * ω * (N : ℝ) := by
  have hper2 : ∀ i : Fin N,
      |(scale * kinA i + t * gA i) - (scale * kinB i + t * gB i)| ≤ B * ω := by
    intro i
    have h1 := abs_markedEdgeError_le_of_markLipschitz (t := t) hscale (hper i) (hgper i)
    have hconst : (scale * Lk + |t| * Lg) ≤ B := hbudget
    have hnonneg : (0 : ℝ) ≤ scale * Lk + |t| * Lg := by positivity
    have hdω : d i ≤ ω := hd i
    have hmul : (scale * Lk + |t| * Lg) * d i ≤ B * ω :=
      mul_le_mul hconst hdω (hd0 i) hB
    nlinarith [h1, hmul]
  calc ∑ i, |(scale * kinA i + t * gA i) - (scale * kinB i + t * gB i)|
      ≤ ∑ _i : Fin N, B * ω := Finset.sum_le_sum fun i _ => hper2 i
    _ = B * ω * (N : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Vanishing normalized mark rate.**  A bounded moment/pressure budget times
a vanishing mark modulus gives a vanishing normalized coupling integral. -/
theorem tendsto_markRate_zero {budget ω : ℝ → ℝ} {b : ℝ}
    (hbudget : Tendsto budget atTop (𝓝 b)) (hω : Tendsto ω atTop (𝓝 0)) :
    Tendsto (fun L => budget L * ω L) atTop (𝓝 (b * 0)) := hbudget.mul hω

/-- The same vanishing rate in the exact `𝓝 0` form consumed by the hupper
assembly. -/
theorem tendsto_markRate_zero' {budget ω : ℝ → ℝ} {b : ℝ}
    (hbudget : Tendsto budget atTop (𝓝 b)) (hω : Tendsto ω atTop (𝓝 0)) :
    Tendsto (fun L => budget L * ω L) atTop (𝓝 0) := by
  simpa using hbudget.mul hω

end OTSelector.Reconstruction
