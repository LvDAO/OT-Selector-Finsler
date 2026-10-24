import OTSelector.Reconstruction.FinslerOriginalFrozenCoreLLN
import OTSelector.Reconstruction.FinslerOriginalRootedSceneCampbellFormula
import OTSelector.Reconstruction.FinslerCampbellLowerAssembly

/-!
# Rooted Campbell mean bound for the empirical frozen core functional

This module attacks the second substantive conjunct of
`RootedFrozenCampbellIdentification`: the Campbell mean bound for the empirical
frozen core functional, i.e. eventually

  `camAveragedFrozenCost (g f t) q + |t| * ||f|| - eps <= E[frozenCost f t n]`.

Following the paper, the frozen core functional is decomposed over the retained
Taylor tiles (proved in `FinslerOriginalFrozenCoreLLN.lean`:
`integral_originalFrozenCoreCost_eq_sum_tiles` and
`integral_originalFrozenCorePressure_ge_sum_of_tile_bounds`).  This module
proves the remaining algebraic and reduction content:

* `integral_camWeight_mul_add_const`: per-piece affineness of the atlas
  integrand: `∫ θ^(-2/q) * (g + B) = ∫ θ^(-2/q) * g + B * ∫ θ^(-2/q)`;
* `camAveragedFrozenCost_add_const`: the Campbell-averaged frozen cost is
  affine, `cam (g + B) = cam g + B * W` with total atlas root weight
  `W = ∑' j, ∫ z in piece_j, θ_j(z)^(-2/q)` (the population normalization
  `W = 1` is the mass balance of the atlas);
* `tileMeanLower_of_campbellDiscretization`: **the reduction**: if the frozen
  core functional is the finite sum of its per-tile costs, every tile mean is at
  least its population value minus its own budget, the population tile values sum
  to at least the Campbell-averaged frozen cost (the named Campbell
  discretization step), and the total budget vanishes, then the Campbell mean
  bound holds;
* `RootedTileCampbellMeanIdentification` (def): the single named limit-law
  statement remaining for the mean bound;
* `camFrozenMeanBound_of_rootedTileIdentification`: the named statement plus the
  total-weight normalization `W = 1` implies conjunct (iv), with the probe
  constant added to the frozen root integrand as in the paper.

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

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open OTSelector.Reconstruction OTSelector.PointProcess

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

variable {K : Set M} {u : M → ℝ}

/-! ## Affineness of the Campbell average -/

/-- Per-piece affineness of the atlas integrand: the weighted integral of
`g + B` is the weighted integral of `g` plus `B` times the total weight of the
piece. -/
theorem integral_camWeight_mul_add_const
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    {q B : ℝ} (g : Z → ℝ) (j : ℕ)
    (hintg : IntegrableOn
      (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z)
      (populationSeedRootPiece Seed a κ lambda j) lambda)
    (hintw : IntegrableOn
      (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (-2 / q))
      (populationSeedRootPiece Seed a κ lambda j) lambda) :
    ∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * (g z + B) ∂lambda =
      (∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z ∂lambda) +
        B * (∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) := by
  have hpt : ∀ z, populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * (g z + B) =
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z +
        B * populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) := by
    intro z; ring
  simp only [hpt]
  rw [integral_add hintg (hintw.const_mul B), integral_const_mul]

/-- **Affineness of the Campbell-averaged frozen cost.**

Adding the probe surplus `B` to the frozen root integrand shifts the
Campbell-averaged frozen cost by `B` times the total atlas root weight
`W = ∑' j, ∫ z in piece_j, θ_j(z)^(-2/q)`.  Under the population normalization
`W = 1` this is exactly the probe constant `|t| ||f||`. -/
theorem camAveragedFrozenCost_add_const
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    {q B : ℝ} (g : Z → ℝ)
    (hintg : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z)
      (populationSeedRootPiece Seed a κ lambda j) lambda)
    (hintw : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (-2 / q))
      (populationSeedRootPiece Seed a κ lambda j) lambda)
    (hsumg : Summable (fun j ↦ ∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z ∂lambda))
    (hsumw : Summable (fun j ↦ ∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda)) :
    campbellAveragedFrozenCost Seed a κ lambda (fun z ↦ g z + B) q =
      campbellAveragedFrozenCost Seed a κ lambda g q +
        B * (∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) := by
  rw [campbellAveragedFrozenCost_def, campbellAveragedFrozenCost_def]
  have hper : ∀ j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * (g z + B) ∂lambda =
      (∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z ∂lambda) +
        B * (∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) :=
    fun j => integral_camWeight_mul_add_const Seed a κ lambda g j (hintg j) (hintw j)
  rw [tsum_congr hper, Summable.tsum_add hsumg (hsumw.mul_left B), tsum_mul_left]

/-! ## The abstract tile reduction -/

/-- **Campbell mean bound from the tile decomposition and the named
discretization step.**

If the frozen core functional `Γ n` is the finite sum of its per-tile costs,
every tile mean is at least its population value minus its own budget, the
population tile values sum to at least the Campbell-averaged frozen cost
`cam` (the named Campbell discretization step), and the total budget vanishes,
then `cam - eps <= Γ n` eventually. -/
theorem tileMeanLower_of_campbellDiscretization
    {ι : Type*} [Fintype ι]
    (Γ : ℕ → ℝ) (tileCost : ℕ → ι → ℝ)
    (value budget : ℕ → ι → ℝ) {cam : ℝ}
    (hdecomp : ∀ n, Γ n = ∑ c, tileCost n c)
    (htile : ∀ n c, value n c - budget n c ≤ tileCost n c)
    (hdiscret : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, cam ≤ (∑ c, value n c) + δ)
    (hbudget : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, budget n c ≤ δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, cam - ε ≤ Γ n := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [hdiscret (ε / 2) hε2, hbudget (ε / 2) hε2] with n hd hb
  have hsum : (∑ c, value n c) - (∑ c, budget n c) ≤ (∑ c, tileCost n c) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun c _ ↦ htile n c
  rw [hdecomp]
  linarith

/-! ## The named limit-law statement -/

/-- **The named tile-level Campbell mean identification.**

For every physical probe `f` and tilt `t`: the empirical frozen core functional is the
finite sum of its per-tile frozen costs (in expectation), every tile mean is
asymptotically at least its population Campbell value minus its own budget, the
population tile values sum to at least the Campbell-averaged frozen cost of the
frozen root integrand, and the total budget vanishes.  This is the remaining
limit-law content of conjunct (iv), complementing the Campbell identification of
the root integrand (conjunct (iii), proved in
`FinslerOriginalRootedSceneCampbellFormula.lean`). -/
def RootedTileCampbellMeanIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (ι : Type*) [Fintype ι] : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
    ∃ (value budget : ℕ → ι → ℝ) (tileCost : ∀ n, Ω n → ι → ℝ),
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        campbellAveragedFrozenCost Seed a κ lambda (g f t) q ≤ (∑ c, value n c) + δ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, budget n c ≤ δ) ∧
      (∀ n, ∫ s, frozenCost f t n s ∂P n = ∑ c, ∫ s, tileCost n s c ∂P n) ∧
      (∀ n c, value n c - budget n c ≤ ∫ s, tileCost n s c ∂P n)

/-- **The Campbell mean bound (conjunct (iv)) from the named tile identification.**

From the named tile-level limit law and the finite-tile mean aggregation, the
Campbell-averaged frozen cost of the frozen root integrand is asymptotically at
most the expected frozen core cost: this is conjunct (iv) of
`RootedFrozenCampbellIdentification` up to the probe constant, which is absorbed
into the frozen root integrand by `camAveragedFrozenCost_add_const` under the
total-atlas-weight normalization. -/
theorem camFrozenMeanBound_of_rootedTileIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ι : Type*} [Fintype ι]
    (hId : RootedTileCampbellMeanIdentification Seed a κ lambda g q P frozenCost ι) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q - ε ≤
        ∫ s, frozenCost f t n s ∂P n := by
  intro f t ε hε
  obtain ⟨value, budget, tileCost, hdiscret, hbudget, hdecomp, htile⟩ := hId f t
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [hdiscret (ε / 2) hε2, hbudget (ε / 2) hε2] with n hd hb
  have hsum : (∑ c, value n c) - (∑ c, budget n c) ≤ (∑ c, ∫ s, tileCost n s c ∂P n) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun c _ ↦ htile n c
  rw [hdecomp n]
  linarith

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
