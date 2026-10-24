import OTSelector.Probability.BipartiteAssignmentConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Centered assignment pressures at sub-square-root cost scales

For original independent iid colors, bounded edge costs growing like `n^a`
with `a < 1/2` give concentration of the actual normalized assignment minimum.
This includes the distance-pressure scale `a = 2/q` whenever `q > 4`.
The measures may vary between rows; no coupling of different rows is needed.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace OTSelector.Probability

/-- The finite-sample variance bound vanishes for costs growing slower than square root. -/
theorem tendsto_assignmentVarianceBound_zero (L a : ℝ) (ha : a < 1 / 2) :
    Tendsto (fun n : ℕ ↦ 16 * (L * ((n + 1 : ℕ) : ℝ) ^ a) ^ 2 /
      ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hexp : 0 < 1 - 2 * a := by linarith
  have hn : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow := (tendsto_rpow_neg_atTop hexp).comp hn
  have hlim := hpow.const_mul (16 * L ^ 2)
  simp only [mul_zero] at hlim
  convert hlim using 1
  funext n
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [Function.comp_apply]
  rw [show -(1 - 2 * a) = a * 2 - 1 by ring,
    Real.rpow_sub hnpos, Real.rpow_one, Real.rpow_mul hnpos.le]
  norm_cast
  ring

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Centering the genuine assignment minimum removes all sampling fluctuations in probability.
Only independence within each row is used. -/
theorem tendsto_centered_bipartiteAssignmentMean
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure T) [IsProbabilityMeasure ν]
    (X : ∀ n, Fin (n + 1) → Ω n → S) (Y : ∀ n, Fin (n + 1) → Ω n → T)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = μ) (hYlaw : ∀ n i, (P n).map (Y n i) = ν)
    (hXY : ∀ n, IndepFun (fun ω i ↦ X n i ω) (fun ω i ↦ Y n i ω) (P n))
    (c : ℕ → S → T → ℝ) (hc : ∀ n, Measurable (Function.uncurry (c n)))
    {L a : ℝ} (hL : 0 ≤ L) (ha : a < 1 / 2)
    (hbound : ∀ n x y, |c n x y| ≤ L * ((n + 1 : ℕ) : ℝ) ^ a)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {ω |
      ε ≤ |sampleAssignmentMean (c n) (fun i ↦ (X n i ω, Y n i ω)) -
        ∫ ω', sampleAssignmentMean (c n) (fun i ↦ (X n i ω', Y n i ω')) ∂P n|})
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ measureReal_nonneg)
    (fun n ↦ deviation_bipartiteAssignmentMean_le (P n) μ ν (Nat.succ_pos n)
      (X n) (Y n) (hX n) (hY n) (hXi n) (hYi n) (hXlaw n) (hYlaw n) (hXY n)
      (hc n) (mul_nonneg hL (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hbound n) hε)
  simpa using (tendsto_assignmentVarianceBound_zero L a ha).div_const (ε ^ 2)

end OTSelector.Probability
