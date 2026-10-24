import OTSelector.Reconstruction.FinslerOriginalDualSlackBound

/-!
# Pointwise tile entry bound from the scale normalization

This module closes the last input of FinslerOriginalDualSlackBound.lean: the
pointwise bound 0 <= tileCostMatrix f t n c s i j <= C0/(n+1).

## The frozen core formula

The tile cost is the masked frozen core matrix

  E = maskedFrozenCost Q (fun i j => max ((1-2 eps) * (scale n * phys_ij) + t * probe_ij) 0),

so E is zero off the mask and equals the clipped frozen expression on the mask.
Nonnegativity is by construction (the max and the indicator).  For the upper bound:

* the frozen physical cost is bounded by a constant B,
* the probe contribution t * probe_ij is bounded by P/(n+1) (probe normalization),
* the scale sequence satisfies 0 <= scale n <= S/(n+1) (scale normalization),
* 0 <= 1 - 2 eps.

Then the clipped expression is at most ((1-2 eps) * S * B + P)/(n+1): the scale
factor multiplies the physical bound, and the probe bound already carries the
normalization.  This is exactly the entry bound required by
FinslerOriginalDualSlackBound.lean with C0 = (1-2 eps) * S * B + P, the explicit
analogue of (1-2 eps) * C_f + |t| * C_p.

## Contents

* tileCostMatrix_nonneg: 0 <= E for every argument.
* tileCostMatrix_le_of_scaleBound: E <= C0/(n+1) from the three bounds above.
* tilePlanResidualVanishing_of_scaleBounds: T.TilePlanResidualVanishing from the
  frozen data (uniform physical bound, probe and scale normalizations) plus the
  optimal tile plan structure and integrability of the uniform tile cost and of
  the plan residual.

## Exact remaining gap

In the concrete instantiation, the two analytic inputs are the uniform bound
phys <= B and the probe normalization t * probe_ij <= P/(n+1); the abstract lane
keeps hprobe and scale as parameters, so these are stated as hypotheses (they are
the concrete normalization facts of the construction).  Everything else is proved.

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

/-- **Nonnegativity of the tile cost entries.**  The masked frozen entry is either
zero or the clipped frozen expression, so it is nonnegative. -/
theorem tileCostMatrix_nonneg
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)) :
    0 ≤ T.tileCostMatrix f t X Y scale hprobe n c s i j := by
  show 0 ≤ maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
    (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
      (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t (hprobe f t n s c)) i j
  exact maskedFrozenCost_nonneg
    (fun i j ↦ frozenCoreMatrix_nonneg (T.core c) ε
      (fun _ _ ↦ T.reference c) (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t
      (hprobe f t n s c) i j) i j

/-- **Pointwise tile entry bound from the scale normalization.**

Given the uniform physical cost bound, the probe normalization and the scale
normalization 0 <= scale n <= S/(n+1), every masked frozen tile entry is at most
C0/(n+1) with the explicit constant C0 = (1-2 eps) * S * B + P. -/
theorem tileCostMatrix_le_of_scaleBound
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (S B P : ℝ) (hB : 0 ≤ B)
    (hε0 : 0 ≤ 1 - 2 * ε)
    (hC₀ : 0 ≤ (1 - 2 * ε) * S * B + P)
    (hscale0 : ∀ n, 0 ≤ scale n)
    (hscale : ∀ n, scale n ≤ S / ((n + 1 : ℕ) : ℝ))
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ B)
    (hprobeB : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      t * hprobe f t n s c i j ≤ P / ((n + 1 : ℕ) : ℝ)) :
    ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      T.tileCostMatrix f t X Y scale hprobe n c s i j ≤
        ((1 - 2 * ε) * S * B + P) / ((n + 1 : ℕ) : ℝ) := by
  intro n c s i j
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hC0' : 0 ≤ ((1 - 2 * ε) * S * B + P) / ((n + 1 : ℕ) : ℝ) := div_nonneg hC₀ hm.le
  have hexpr : max ((1 - 2 * ε) *
      ((scale n) * (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)) +
      t * hprobe f t n s c i j) 0 ≤
      ((1 - 2 * ε) * S * B + P) / ((n + 1 : ℕ) : ℝ) := by
    refine max_le ?_ hC0'
    have h1 : (1 - 2 * ε) *
        ((scale n) * (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)) ≤
        ((1 - 2 * ε) * S * B) / ((n + 1 : ℕ) : ℝ) := by
      have h2 : (scale n) *
          (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤
          (S / ((n + 1 : ℕ) : ℝ)) * B := by
        have h3 : (scale n) *
            (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤
            (scale n) * B :=
          mul_le_mul_of_nonneg_left (hphys n c s i j) (hscale0 n)
        have h4 : (scale n) * B ≤ (S / ((n + 1 : ℕ) : ℝ)) * B :=
          mul_le_mul_of_nonneg_right (hscale n) hB
        linarith
      calc (1 - 2 * ε) *
            ((scale n) * (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s))
          ≤ (1 - 2 * ε) * ((S / ((n + 1 : ℕ) : ℝ)) * B) :=
            mul_le_mul_of_nonneg_left h2 hε0
        _ = ((1 - 2 * ε) * S * B) / ((n + 1 : ℕ) : ℝ) := by ring
    have h5 : t * hprobe f t n s c i j ≤ P / ((n + 1 : ℕ) : ℝ) := hprobeB n c s i j
    calc (1 - 2 * ε) *
          ((scale n) * (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)) +
          t * hprobe f t n s c i j
        ≤ ((1 - 2 * ε) * S * B) / ((n + 1 : ℕ) : ℝ) + P / ((n + 1 : ℕ) : ℝ) :=
          add_le_add h1 h5
      _ = ((1 - 2 * ε) * S * B + P) / ((n + 1 : ℕ) : ℝ) := by ring
  show maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
    (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
      (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t (hprobe f t n s c)) i j ≤
    ((1 - 2 * ε) * S * B + P) / ((n + 1 : ℕ) : ℝ)
  by_cases hmem : (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · rw [maskedFrozenCost_apply_of_mem hmem]
    exact hexpr
  · rw [maskedFrozenCost_apply_of_not_mem hmem]
    exact hC0'

/-- **Plan-residual vanishing from the frozen data and the scale normalization.**

The explicit entry bound C0 = (1-2 eps) * S * B + P of
tileCostMatrix_le_of_scaleBound feeds the pointwise-entry-bound theorem, so
T.TilePlanResidualVanishing follows from the uniform physical bound, the probe and
scale normalizations, the optimal tile plan structure and the two integrability
facts. -/
theorem tilePlanResidualVanishing_of_scaleBounds
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (S B P : ℝ) (hB : 0 ≤ B)
    (hε0 : 0 ≤ 1 - 2 * ε)
    (hC₀ : 0 ≤ (1 - 2 * ε) * S * B + P)
    (hscale0 : ∀ n, 0 ≤ scale n)
    (hscale : ∀ n, scale n ≤ S / ((n + 1 : ℕ) : ℝ))
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ B)
    (hprobeB : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)), t * hprobe f t n s c i j ≤ P / ((n + 1 : ℕ) : ℝ))
    (hAnonneg : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)), 0 ≤ A n s i j)
    (hrow : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)), ∑ j, A n s i j = 1)
    (hcol : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)), ∑ i, A n s i j = 1)
    (hopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n),
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s) (A n s) ≤
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n)) :
    T.TilePlanResidualVanishing sample A X Y scale hprobe := by
  refine tilePlanResidualVanishing_of_entryBound (T := T) sample A X Y scale hprobe
    (C₀ := (1 - 2 * ε) * S * B + P) hC₀ ?_ ?_ hAnonneg hrow hcol hopt hintCost hintRes
  · intro f t n c s i j
    exact tileCostMatrix_nonneg (T := T) f t X Y scale hprobe n c s i j
  · intro f t n c s i j
    exact tileCostMatrix_le_of_scaleBound (T := T) f t X Y scale hprobe S B P hB hε0 hC₀
      hscale0 hscale hphys (hprobeB f t) n c s i j

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction