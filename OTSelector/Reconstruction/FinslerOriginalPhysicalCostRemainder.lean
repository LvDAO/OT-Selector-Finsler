import OTSelector.Reconstruction.FinslerFiniteTilePressure
import OTSelector.Reconstruction.FinslerOriginalMatchingMomentBound

/-!
# Physical cost Taylor remainder in the pressure lane

This module closes the remainder input isolated in
`FinslerCoefficientPressureFreezing.relative_cost_of_quadratic_remainder` and assembles
it with the matching moment bound of `FinslerOriginalMatchingMomentBound`.

The actual physical cost edge of a matched pair of retained roots is the population
seed pair deficit `populationSeedPairDeficit`.  The finite Taylor cover already
produces its *relative* Taylor remainder (`TaylorRootCover.relative_distance`): the
deficit is within a factor `1 ± 2 ε` of the frozen quadratic cost
`matrixQuadratic (C.matrix z₀ p) v`, uniformly over every retained root pair in one
common Taylor neighborhood.  That is exactly the input consumed by the matching
moment chain.

Main results.
* `sum_sqDisplacement_le_of_relative_remainder`: a *relative* remainder
  `|cost i - Q i| ≤ ε * Q i` together with a positive quadratic lower bound
  `m * ‖v i‖^2 ≤ Q i` gives the total squared matched displacement bound
  `sum sqDisplacement ≤ (dim / ((1 - ε) * m)) * sum cost`.  Unlike the absolute
  remainder of the moment module this uses the frozen quadratic cost itself, which
  is the form the Taylor cover produces.
* `average_sqDisplacement_le_of_relative_remainder`: the per-pair average form:
  average cost ≤ eta forces average squared matched displacement
  ≤ `(dim / ((1 - ε) * m)) * eta`, the limit shape needed by the blockwise
  stabilization error.
* `TaylorRootCover.matching_moment_bound`: the end-to-end assembly — for the actual
  retained-root matching the total squared matched displacement is bounded by the
  total physical (population seed pair deficit) matching cost, using the Taylor
  relative remainder and the on-diagonal Hessian lower bound.  The constant `m` is
  an input here; `OriginalPopulationCoefficientCore.exists_quadratic_lower_bound`
  produces it from the positive definite frozen coefficient (this is exactly the
  constant of `exists_matching_moment_constant` in the matching moment module).

Exact remaining sub-gap: the pressure-side budget step is not formalized here --
to turn the estimate into a vanishing block-wise stabilization error one still
needs the optimal matching of the block marked cloud to have average matching cost
bounded by the pressure scale (the hupper-lane pressure budget), and the mark
modulus estimate for the position-dependent marks.  The Taylor remainder input and
the matching moment transfer are closed in this module.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-! ## Relative Taylor remainder controls the matching moment -/

/-- **Relative-remainder matching moment bound.**  If every matched pair has a
positive quadratic lower bound `m * ‖v i‖^2 ≤ Q i` on the frozen cost and the true
cost satisfies the *relative* remainder `|cost i - Q i| ≤ ε * Q i`, then the total
squared matched displacement is bounded by the total true matching cost. -/
theorem sum_sqDisplacement_le_of_relative_remainder {N : ℕ} {n : Type*} [Fintype n]
    (hcard : 0 < Fintype.card n) {v : Fin N → n → ℝ} {Q cost : Fin N → ℝ}
    {m ε : ℝ} (hm : 0 < m) (_hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hQ : ∀ i, m * ‖v i‖ ^ 2 ≤ Q i)
    (hcost : ∀ i, |cost i - Q i| ≤ ε * Q i) :
    ∑ i, sqDisplacement (v i) ≤
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i := by
  have hcardpos : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast hcard
  have hc : 0 < (1 - ε) * m := mul_pos (by linarith) hm
  have hc0 : 0 < ((1 - ε) * m) / (Fintype.card n : ℝ) := div_pos hc hcardpos
  have hnonneg : (0 : ℝ) ≤ 1 - ε := by linarith
  have hpair : ∀ i : Fin N,
      (((1 - ε) * m) / (Fintype.card n : ℝ)) * sqDisplacement (v i) ≤ cost i := by
    intro i
    have hlow : (m / (Fintype.card n : ℝ)) * sqDisplacement (v i) ≤ Q i :=
      sqDisplacement_le_card_mul_of_quadratic_lower hm hcard (hQ i)
    have hbase : (1 - ε) * Q i ≤ cost i := by
      have h := (abs_le.mp (hcost i)).1
      nlinarith
    have hstep : (((1 - ε) * m) / (Fintype.card n : ℝ)) * sqDisplacement (v i) =
        (1 - ε) * ((m / (Fintype.card n : ℝ)) * sqDisplacement (v i)) := by ring
    rw [hstep]
    nlinarith [mul_le_mul_of_nonneg_left hlow hnonneg]
  have hsum : (((1 - ε) * m) / (Fintype.card n : ℝ)) *
      ∑ i, sqDisplacement (v i) ≤ ∑ i, cost i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hpair i
  have hkey : ∑ i, sqDisplacement (v i) ≤
      (∑ i, cost i) / (((1 - ε) * m) / (Fintype.card n : ℝ)) := by
    refine (le_div_iff₀ hc0).mpr ?_
    rwa [mul_comm]
  have hconst : (∑ i, cost i) / (((1 - ε) * m) / (Fintype.card n : ℝ)) =
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i := by
    field_simp
  rwa [hconst] at hkey

/-- Per-pair average form of the relative-remainder matching moment bound. -/
theorem average_sqDisplacement_le_of_relative_remainder {N : ℕ} {n : Type*}
    [Fintype n] (hcard : 0 < Fintype.card n) {v : Fin N → n → ℝ}
    {Q cost : Fin N → ℝ} {m ε eta : ℝ} (hm : 0 < m) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (hN : 0 < N)
    (hQ : ∀ i, m * ‖v i‖ ^ 2 ≤ Q i)
    (hcost : ∀ i, |cost i - Q i| ≤ ε * Q i)
    (havg : (1 / (N : ℝ)) * ∑ i, cost i ≤ eta) :
    (1 / (N : ℝ)) * ∑ i, sqDisplacement (v i) ≤
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * eta := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hK : 0 ≤ (Fintype.card n : ℝ) / ((1 - ε) * m) := by positivity
  have hsum := sum_sqDisplacement_le_of_relative_remainder hcard hm hε0 hε1 hQ hcost
  have h1 : (1 / (N : ℝ)) * ∑ i, sqDisplacement (v i) ≤
      (1 / (N : ℝ)) * (((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have h2 : (1 / (N : ℝ)) * (((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i) =
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ((1 / (N : ℝ)) * ∑ i, cost i) := by
    ring
  have h3 : ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ((1 / (N : ℝ)) * ∑ i, cost i) ≤
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * eta :=
    mul_le_mul_of_nonneg_left havg hK
  linarith

/-! ## The physical lane: actual retained-root matching -/

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}
  [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instTileMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **End-to-end matching moment bound for the actual retained-root matching.**
The Taylor cover's relative remainder and the on-diagonal Hessian lower bound give,
for every finite matching of retained roots in one common Taylor neighborhood, a
bound on the total squared matched displacement in terms of the total actual
physical matching cost `populationSeedPairDeficit` (the actual distance cost edge
of the pressure lane). -/
theorem TaylorRootCover.matching_moment_bound
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε m : ℝ}
    (D : C.TaylorRootCover ε) (hε0 : 0 ≤ ε) (hε2 : 2 * ε < 1) (hm : 0 < m)
    (hquad : ∀ z ∈ C.roots, ∀ p ∈ C.window.region, ∀ v,
      m * ‖v‖ ^ 2 ≤ matrixQuadratic (C.matrix z p) v)
    (hdim : 0 < finrank ℝ (P C.seedIndex).seed.covector.ker)
    {N : ℕ} {z₀ : Z} (hz₀ : z₀ ∈ D.centers)
    (z z' : Fin N → Z) (p : Fin N → ℝ × ℝ)
    (hz : ∀ i, z i ∈ C.roots ∩ D.neighborhood z₀)
    (hz' : ∀ i, z' i ∈ C.roots ∩ D.neighborhood z₀)
    (hp : ∀ i, p i ∈ C.window.region) :
    ∑ i, sqDisplacement ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P C.seedIndex).seed a (z' i) -
          populationSeedRootLabelValue (P C.seedIndex).seed a (z i))) ≤
      ((finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ) / ((1 - 2 * ε) * m)) *
        ∑ i, populationSeedPairDeficit (P C.seedIndex).seed (p i)
          (populationSeedRootLabelValue (P C.seedIndex).seed a (z i),
            populationSeedRootLabelValue (P C.seedIndex).seed a (z' i)) := by
  let w := populationSeedRootLabelValue (P C.seedIndex).seed a
  let bW := Module.finBasis ℝ (P C.seedIndex).seed.covector.ker
  let v : Fin N → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ :=
    fun i => bW.equivFun (w (z' i) - w (z i))
  let Q : Fin N → ℝ := fun i => matrixQuadratic (C.matrix z₀ (p i)) (v i)
  let cost : Fin N → ℝ :=
    fun i => populationSeedPairDeficit (P C.seedIndex).seed (p i) (w (z i), w (z' i))
  have hcard : 0 < Fintype.card (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) := by
    simpa using hdim
  have hQ : ∀ i, m * ‖v i‖ ^ 2 ≤ Q i := by
    intro i
    exact hquad z₀ (D.subset hz₀) (p i) (hp i) (v i)
  have hcost : ∀ i, |cost i - Q i| ≤ (2 * ε) * Q i := by
    intro i
    have h := D.relative_distance hF hcomplete hu ha hinj hε0 hz₀ (hz i) (hz' i) (hp i)
    dsimp only at h
    simpa only [cost, Q, v, w] using h
  have hmain := sum_sqDisplacement_le_of_relative_remainder (hcard := hcard)
    (hm := hm) (_hε0 := by linarith) (hε1 := by linarith) hQ hcost
  simpa only [v, cost, Q, w, Fintype.card_fin] using hmain

end OTSelector.Reconstruction
