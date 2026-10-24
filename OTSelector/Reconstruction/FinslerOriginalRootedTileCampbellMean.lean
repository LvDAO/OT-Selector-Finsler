import OTSelector.Reconstruction.FinslerOriginalCampbellMeanBound
import OTSelector.Reconstruction.FinslerOriginalFrozenCoreLLN
import OTSelector.Reconstruction.FinslerOriginalFiniteDomination

/-!
# Rooted tile Campbell mean identification

This module closes the named input `RootedTileCampbellMeanIdentification` of
`FinslerOriginalCampbellMeanBound.lean` in its *reducible* form: the integral
decomposition conjunct is **proved** from the repo's tile decomposition of the
actual frozen core functional, and the remaining content is reduced to a single
named per-tile statement `RootedTileMeanCampbellValues` (per-tile population
Campbell values, per-tile budgets, and the Campbell discretization of the
Campbell-averaged frozen cost by the finite tile values).

Main results:

* `rootedTileCampbellMeanIdentification_of_tile_means`: for the actual frozen
  core functional `fractionalAssignmentCost (originalFrozenCoreMatrix) / (n+1)`
  of the retained Taylor tiles, the named Prop
  `RootedTileCampbellMeanIdentification` holds as soon as there are per-tile
  population values and budgets with (i) the Campbell discretization bound,
  (ii) vanishing total budget, and (iii) per-tile mean lower bounds.  The
  integral decomposition of the frozen core functional over the tiles is not an
  assumption: it is proved by
  `integral_originalFrozenCorePressure_eq_sum_tiles`;
* `RootedTileMeanCampbellValues` (def): the single named per-tile statement
  remaining (the per-tile Campbell values and their error control);
* `camFrozenMeanBound_of_rootedTileMeanValues`: the named per-tile statement
  implies the Campbell mean bound for the empirical frozen core functional.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
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

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **The named per-tile Campbell values.**  The single remaining per-tile
statement: for every physical probe and tilt there are per-tile population
Campbell values and per-tile budgets such that the Campbell-averaged frozen cost
is bounded by the finite value sum up to every accuracy, the total budget
vanishes, and every tile mean dominates its population value minus its budget. -/
def RootedTileMeanCampbellValues
    (q : ℝ) (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
  ∃ (value budget : ℕ → T.Index → ℝ),
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      campbellAveragedFrozenCost P a κ lambda (g f t) q ≤ (∑ c, value n c) + δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, budget n c ≤ δ) ∧
    (∀ n (c : T.Index), value n c - budget n c ≤
      (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c s ∂sample n) / ((n + 1 : ℕ) : ℝ))

/-- **The named Prop `RootedTileCampbellMeanIdentification` from per-tile means.**

For the actual frozen core functional of the retained Taylor tiles
`fractionalAssignmentCost (originalFrozenCoreMatrix) / (n+1)`, the named Prop
`RootedTileCampbellMeanIdentification` holds as soon as the per-tile Campbell
values exist.  The integral decomposition of the frozen core functional over the
disjoint retained tiles is *proved* here from
`integral_originalFrozenCorePressure_eq_sum_tiles`, not assumed. -/
theorem rootedTileCampbellMeanIdentification_of_tile_means
    (sample : ∀ n, Measure (Ω n))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c) (sample n))
    (hdata : T.RootedTileMeanCampbellValues q g sample X Y scale hprobe A) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (fun f t n s ↦ fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s))
        (A n s) / ((n + 1 : ℕ) : ℝ)) T.Index := by
  have hdata' : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      ∃ (value budget : ℕ → T.Index → ℝ),
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
          campbellAveragedFrozenCost P a κ lambda (g f t) q ≤ (∑ c, value n c) + δ) ∧
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, budget n c ≤ δ) ∧
        (∀ n (c : T.Index), value n c - budget n c ≤
          (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
            (hprobe f t n) (A n) (scale n) t c s ∂sample n) / ((n + 1 : ℕ) : ℝ)) :=
    hdata
  intro f t
  obtain ⟨value, budget, hdiscret, hbudget, htile⟩ := hdata' f t
  refine ⟨value, budget, fun n s c ↦
    T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
      (hprobe f t n) (A n) (scale n) t c s / ((n + 1 : ℕ) : ℝ),
    hdiscret, hbudget, ?_, ?_⟩
  · intro n
    have h := T.integral_originalFrozenCorePressure_eq_sum_tiles (P₀ := sample n)
      (n := n + 1)
      (X := fun (s : Ω n) (i : Fin (n + 1)) ↦ X n i s)
      (Y := fun (s : Ω n) (i : Fin (n + 1)) ↦ Y n i s)
      (h := hprobe f t n) (A := A n) (scale := scale n) (t := t)
      (hint := fun c ↦ hint f t n c)
    simpa only [div_eq_mul_inv] using h
  · intro n c
    refine (htile n c).trans_eq ?_
    rw [MeasureTheory.integral_div]


/-- **The Campbell mean bound for the actual frozen core functional from the named
per-tile values.**  Composing the identification theorem with the mean-bound
reduction `camFrozenMeanBound_of_rootedTileIdentification` of
`FinslerOriginalCampbellMeanBound.lean`: the per-tile Campbell values yield the
mean lower bound for `fractionalAssignmentCost (originalFrozenCoreMatrix) / (n+1)`,
i.e. conjunct (iv) of `RootedFrozenCampbellIdentification` for the actual frozen
core functional of the retained Taylor tiles. -/
theorem camFrozenMeanBound_of_rootedTileMeanValues
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c) (sample n))
    (hdata : T.RootedTileMeanCampbellValues q g sample X Y scale hprobe A) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      campbellAveragedFrozenCost P a κ lambda (g f t) q - ε ≤
        ∫ s, fractionalAssignmentCost
          (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
            (scale n) t (hprobe f t n s))
          (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n :=
  camFrozenMeanBound_of_rootedTileIdentification (Seed := P) (a := a) (κ := κ)
    (lambda := lambda) (g := g) (q := q) (P := sample)
    (frozenCost := fun f t n s ↦ fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
        (scale n) t (hprobe f t n s))
      (A n s) / ((n + 1 : ℕ) : ℝ))
    (rootedTileCampbellMeanIdentification_of_tile_means T sample hint hdata)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
