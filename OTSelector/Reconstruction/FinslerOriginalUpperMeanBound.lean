import OTSelector.Reconstruction.FinslerOriginalCampbellMeanBound
import OTSelector.Reconstruction.FinslerOriginalScenePressureWiring

/-!
# The matching upper population mean bound

This module supplies item (b) of the hprob chain: the upper population mean
bound for the frozen core functional, mirroring the lower bound
camFrozenMeanBound_of_rootedTileIdentification of
FinslerOriginalCampbellMeanBound.lean.

## Contents

* RootedTileCampbellMeanUpper: the mirror of the named lower limit-law content
  RootedTileCampbellMeanIdentification: per-tile population values whose sum is
  the Campbell-averaged frozen cost, per-tile upper bounds on the empirical tile
  means, and a total budget vanishing in the sample size.

* camFrozenMeanUpperBound_of_rootedTileUpper: the upper mean bound
  E[frozenCost f t n] <= campbellAveragedFrozenCost (g f t) q + eps eventually,
  obtained from the tile upper control by a finite-sum argument.

* rootedTileMeanUpper_of_tileMeanUpperBound and
  camFrozenMeanUpperBound_of_tileMeanUpperBound: the same upper mean bound
  derived from the per-tile integrals and the exact frozen-core integral
  decomposition, which is the shape the probability lane supplies from the
  two-sided per-tile counting convergence (RootedTileMeanConvergence plus
  campbell = sum of the population tile values).

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **The named tile upper control of the frozen core mean.**

Mirror of the lower limit-law content RootedTileCampbellMeanIdentification: for
every probe and tilt there are per-tile population values summing to the
Campbell-averaged frozen cost, and per-tile budgets with vanishing total, such
that the expected frozen core cost is at most the sum of values plus the total
budget.  This is the upper counterpart of RootedTileCampbellMeanIdentification. -/
def RootedTileCampbellMeanUpper
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (ι : Type*) [Fintype ι] : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
    ∃ (value : ι → ℝ) (budget : ℕ → ι → ℝ),
      (∑ c, value c) ≤ campbellAveragedFrozenCost Seed a κ lambda (g f t) q ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, budget n c ≤ δ) ∧
      (∀ n, ∫ s, frozenCost f t n s ∂P n ≤ ∑ c, value c + ∑ c, budget n c)

/-- **The matching upper population mean bound.**

From the named tile upper control of the frozen core mean, the expected frozen
core cost is eventually at most the Campbell-averaged frozen cost of the frozen
root integrand plus eps: the mirror of camFrozenMeanBound_of_rootedTileIdentification. -/
theorem camFrozenMeanUpperBound_of_rootedTileUpper
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (hUp : RootedTileCampbellMeanUpper Seed a κ lambda g q P frozenCost ιt) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, frozenCost f t n s ∂P n ≤
        campbellAveragedFrozenCost Seed a κ lambda (g f t) q + ε := by
  intro f t ε hε
  obtain ⟨value, budget, hvalue, hbudget, hupper⟩ := hUp f t
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [hbudget (ε / 2) hε2] with n hb
  have h := hupper n
  linarith

/-- **The tile upper control from per-tile upper bounds.**

Given per-tile population values summing to the Campbell-averaged frozen cost,
the exact integral decomposition of the frozen core functional over the finite
tile family, and per-tile upper bounds of the expected tile costs by the
population value plus a per-tile error with vanishing total, the named tile
upper control holds.  This mirrors the lower composition
tileMeanLower_of_campbellDiscretization. -/
theorem rootedTileMeanUpper_of_tileMeanUpperBound
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → ιt → ℝ)
    (tileCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ιt → ℝ)
    (hpop : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q = ∑ c, popVal f t c)
    (hdec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∫ s, frozenCost f t n s ∂P n = ∑ c, ∫ s, tileCost f t n s c ∂P n)
    (hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      ∃ err : ℕ → ιt → ℝ,
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, err n c ≤ δ) ∧
        (∀ (n : ℕ) (c : ιt), ∫ s, tileCost f t n s c ∂P n ≤ popVal f t c + err n c)) :
    RootedTileCampbellMeanUpper Seed a κ lambda g q P frozenCost ιt := by
  intro f t
  obtain ⟨err, herrSum, herrBound⟩ := hbound f t
  refine ⟨popVal f t, err, ?_, herrSum, ?_⟩
  · rw [hpop f t]
  · intro n
    rw [hdec f t n]
    calc (∑ c, ∫ s, tileCost f t n s c ∂P n)
        ≤ ∑ c, (popVal f t c + err n c) :=
          Finset.sum_le_sum fun c _ ↦ herrBound n c
      _ = (∑ c, popVal f t c) + ∑ c, err n c := Finset.sum_add_distrib

/-- **The upper population mean bound from the per-tile upper bounds.**

Composing the two previous results: the per-tile upper bounds and the integral
decomposition of the frozen core functional yield the matching upper population
mean bound.  This is the upper counterpart of
camFrozenMeanBound_of_rootedTileMeanValues, and the shape in which the
probability lane supplies it from the two-sided per-tile counting convergence. -/
theorem camFrozenMeanUpperBound_of_tileMeanUpperBound
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → ιt → ℝ)
    (tileCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ιt → ℝ)
    (hpop : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q = ∑ c, popVal f t c)
    (hdec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∫ s, frozenCost f t n s ∂P n = ∑ c, ∫ s, tileCost f t n s c ∂P n)
    (hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      ∃ err : ℕ → ιt → ℝ,
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, err n c ≤ δ) ∧
        (∀ (n : ℕ) (c : ιt), ∫ s, tileCost f t n s c ∂P n ≤ popVal f t c + err n c)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, frozenCost f t n s ∂P n ≤
        campbellAveragedFrozenCost Seed a κ lambda (g f t) q + ε :=
  camFrozenMeanUpperBound_of_rootedTileUpper Seed a κ lambda g (P := P)
    (frozenCost := frozenCost)
    (rootedTileMeanUpper_of_tileMeanUpperBound Seed a κ lambda g (P := P)
      (frozenCost := frozenCost) popVal tileCost hpop hdec hbound)

/-- **The two-sided identification of the pressure lower readout.**

With the lower mean bound discharged internally from the named tile Campbell
mean identification hId, the upper mean bound of this file, the empirical mean
convergence hlim and the assembled readout identity hread, the assembly's
pressureLower readout equals the assembled Palm readout Psi.  This closes the
two-sided identification leaving no mean-bound sub-gap. -/
theorem pressureLower_eq_sceneReadout_of_tileMeanUpperBound
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hId : OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.RootedTileCampbellMeanIdentification
      Seed a κ lambda g q P frozenCost ιt)
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → ιt → ℝ)
    (tileCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ιt → ℝ)
    (hpop : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q = ∑ c, popVal f t c)
    (hdec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∫ s, frozenCost f t n s ∂P n = ∑ c, ∫ s, tileCost f t n s c ∂P n)
    (hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      ∃ err : ℕ → ιt → ℝ,
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, err n c ≤ δ) ∧
        (∀ (n : ℕ) (c : ιt), ∫ s, tileCost f t n s c ∂P n ≤ popVal f t c + err n c))
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, frozenCost f t n s ∂P n) atTop
        (𝓝 (pressureLower f t)))
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower Seed a κ lambda g q = Ψ) :
    pressureLower = Ψ :=
  pressureLower_eq_sceneReadout_of_empirical_limit Seed a κ lambda g (P := P)
    (frozenCost := frozenCost) pressureLower hId hlim
    (camFrozenMeanUpperBound_of_tileMeanUpperBound Seed a κ lambda g (P := P)
      (frozenCost := frozenCost) popVal tileCost hpop hdec hbound) Ψ hread

end OTSelector.Reconstruction