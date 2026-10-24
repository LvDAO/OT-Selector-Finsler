import OTSelector.Reconstruction.FinslerOriginalTileEntryBound

/-!
# Concrete normalization of the scale and probe sequences

This module closes the last two hypotheses of FinslerOriginalTileEntryBound.lean by
exhibiting the concrete normalization of the tile lane:

  tileScale n = 1/(n+1),
  tileProbe (K := K) base f t n s c = (1/((1+|t|)(n+1))) • base n s c.

## Why this is the right normalization

* tileScale n = 1/(n+1) satisfies 0 <= tileScale n <= 1/(n+1) (i.e. S = 1), the
  scale normalization needed for the pointwise entry bound;

* the probe matrix of the tile cost enters multiplied by the coupling parameter t,
  so the probe must itself be normalized to make t * probe = O(1/(n+1)) uniformly
  in t.  The factor 1/(1+|t|) makes t * tileProbe bounded by the base probe bound
  (|t|/(1+|t|) <= 1), and the factor 1/(n+1) makes it vanish at the tile rate.
  This gives exactly the hypothesis t * probe_ij <= Bp/(n+1) of the entry-bound
  theorem, with the explicit constant Bp (the sup bound on the base probe matrix).

## Contents

* tileScale_nonneg, tileScale_le: the scale normalization facts.
* tileProbe_mul_le: t * tileProbe (K := K) base f t n s c i j <= Bp/(n+1) from
  |base n s c i j| <= Bp.
* tilePlanResidualVanishing_of_normalizedData: T.TilePlanResidualVanishing for the
  concrete normalized data from the uniform frozen physical cost bound, the optimal
  tile plan structure and integrability.

## Exact remaining gap

The uniform frozen physical cost bound phys <= B (structural, from the frozen core
geometry) and the base probe sup bound |base| <= Bp (structural: the base probe is
the bounded probe readout), plus the optimal tile plan structure and integrability.
The scale and probe normalizations are now concrete definitions, not hypotheses.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

/-- The concrete scale normalization of the tile lane: scale n = 1/(n+1). -/
noncomputable def tileScale : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)

/-- The concrete probe normalization of the tile lane: the base probe matrix is
scaled by 1/((1+|t|)(n+1)), so that t times it is O(1/(n+1)) uniformly in t. -/
noncomputable def tileProbe {ι : Type*}
    (base : ∀ n, Ω n → ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ι →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun f t n s c ↦ (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) • base n s c

/-- The concrete scale normalization is nonnegative. -/
theorem tileScale_nonneg (n : ℕ) : 0 ≤ tileScale n := by
  unfold tileScale
  positivity

/-- The concrete scale normalization is at most 1/(n+1). -/
theorem tileScale_le (n : ℕ) :
    tileScale n ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
  unfold tileScale
  exact le_rfl

/-- **Probe normalization bound.**  If the base probe matrix is bounded by Bp,
then t times the normalized probe entry is at most Bp/(n+1), uniformly in t. -/
theorem tileProbe_mul_le {ι : Type*}
    (base : ∀ n, Ω n → ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c : ι) (i j : Fin (n + 1)),
      |base n s c i j| ≤ Bp)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (c : ι)
    (i j : Fin (n + 1)) :
    t * tileProbe (K := K) base f t n s c i j ≤ Bp / ((n + 1 : ℕ) : ℝ) := by
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hden : (0 : ℝ) < 1 + |t| := by positivity
  have hcoef : |t| / (1 + |t|) ≤ 1 := by
    rw [div_le_one hden]
    linarith [le_abs_self t]
  have hval : t * tileProbe (K := K) base f t n s c i j =
      (t / (1 + |t|)) * (base n s c i j / ((n + 1 : ℕ) : ℝ)) := by
    have hden' : (1 + |t|) ≠ 0 := ne_of_gt hden
    have hm' : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hm
    simp only [tileProbe, Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [hval]
  have hstep : (t / (1 + |t|)) * (base n s c i j / ((n + 1 : ℕ) : ℝ)) ≤
      (|t| / (1 + |t|)) * (|base n s c i j| / ((n + 1 : ℕ) : ℝ)) := by
    calc (t / (1 + |t|)) * (base n s c i j / ((n + 1 : ℕ) : ℝ))
        ≤ |(t / (1 + |t|)) * (base n s c i j / ((n + 1 : ℕ) : ℝ))| :=
          le_abs_self _
      _ = |t / (1 + |t|)| * |base n s c i j / ((n + 1 : ℕ) : ℝ)| := by
          rw [abs_mul]
      _ = (|t| / (1 + |t|)) * (|base n s c i j| / ((n + 1 : ℕ) : ℝ)) := by
          rw [abs_div, abs_of_pos hden, abs_div, abs_of_pos hm]
  calc (t / (1 + |t|)) * (base n s c i j / ((n + 1 : ℕ) : ℝ))
      ≤ (|t| / (1 + |t|)) * (|base n s c i j| / ((n + 1 : ℕ) : ℝ)) := hstep
    _ ≤ 1 * (Bp / ((n + 1 : ℕ) : ℝ)) := by
        refine mul_le_mul hcoef ?_ (by positivity) (by norm_num)
        exact div_le_div_of_nonneg_right (hbase n s c i j) hm.le
    _ = Bp / ((n + 1 : ℕ) : ℝ) := one_mul _

/-- **Plan-residual vanishing for the concrete normalized tile data.**

With scale n = 1/(n+1) and the probe normalized as 1/((1+|t|)(n+1)) times a base
probe matrix bounded by Bp, T.TilePlanResidualVanishing follows from the uniform
frozen physical cost bound, the optimal tile plan structure and the two
integrability facts. -/
theorem tilePlanResidualVanishing_of_normalizedData
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B Bp : ℝ) (hB : 0 ≤ B) (hBp : 0 ≤ Bp)
    (hε0 : 0 ≤ 1 - 2 * ε)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ B)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c : T.Index) (i j : Fin (n + 1)),
      |base n s c i j| ≤ Bp)
    (hAnonneg : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)), 0 ≤ A n s i j)
    (hrow : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)), ∑ j, A n s i j = 1)
    (hcol : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)), ∑ i, A n s i j = 1)
    (hopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n),
      fractionalAssignmentCost
        (T.tileCostMatrix f t X Y tileScale (tileProbe (K := K) base) n c s) (A n s) ≤
      fractionalAssignmentCost
        (T.tileCostMatrix f t X Y tileScale (tileProbe (K := K) base) n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y tileScale (tileProbe (K := K) base) n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y tileScale (tileProbe (K := K) base) n c s i j) (sample n)) :
    T.TilePlanResidualVanishing sample A X Y tileScale (tileProbe (K := K) base) := by
  have hC₀ : 0 ≤ (1 - 2 * ε) * 1 * B + Bp := by
    have h1 : 0 ≤ (1 - 2 * ε) * B := mul_nonneg hε0 hB
    linarith
  refine tilePlanResidualVanishing_of_scaleBounds (T := T) sample A X Y
    tileScale (tileProbe (K := K) base) 1 B Bp hB hε0 hC₀ ?_ ?_ hphys ?_ hAnonneg hrow hcol
    hopt hintCost hintRes
  · intro n
    exact tileScale_nonneg n
  · intro n
    exact tileScale_le n
  · intro f t n c s i j
    exact tileProbe_mul_le base hBp hbase f t n s c i j

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction