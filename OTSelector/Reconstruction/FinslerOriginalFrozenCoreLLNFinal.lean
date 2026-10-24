import OTSelector.Reconstruction.FinslerOriginalFrozenCoreLLN
import OTSelector.Reconstruction.FinslerFrozenCoreDomination
import OTSelector.Reconstruction.FinslerOriginalFiniteDomination

/-!
# Frozen-core LLN, final step: the lower one-sided per-edge passage

The frozen core matrix of `FinslerFrozenCoreDomination.lean` is
`frozenCoreMatrix C ε z₀ X Y k t h = max ((1 - 2 ε) * (k * frozenPhysicalCost) + t * h) 0`,
and only the *upper* passage
`frozenCoreMatrix ≤ k * slack + t * g + |t| * probeError` was packaged there.
This module proves the *lower* passage, which compares the frozen core cost with
the actual tilted cost from below, and composes it with the deterministic
aggregation of `FinslerOriginalFrozenCoreLLN.lean`.

## Lower one-sided per-edge passage (task item A1)

From the two-sided Taylor relative comparison

  `|actual slack - frozenPhysicalCost| ≤ 2 ε * frozenPhysicalCost`

and the model-probe bounds `|g - h| ≤ probeError`, `|g| ≤ Bg`, one obtains on
every retained edge

  `(1 - 2 ε)^2 * (k * slack + t * g) - (4 ε |t| Bg + |t| probeError) ≤ frozenCoreMatrix …`

with `β = (1 - 2 ε)^2 = 1 - 4 ε + 4 ε^2 → 1` and
`γ = 4 ε |t| Bg + |t| probeError → 0` as `ε → 0`.  The arithmetic core is
`OTSelector.absoluteFrozenLower_of_relative`; the geometric form is
`frozenCoreMatrix_lower_of_relative`; `maskedFrozenCost_ge_value_of_geometry`
composes it with `OTSelector.maskedFrozenCost_ge_value_sub_unretained` to give,
at the actual optimal fractional plan, frozen core cost
`≥ β` (optimal value − unretained edge energy) `− γ n`.

## Status of the remaining input (task item A2) and the honest gap

The vanishing of the unretained edge energy
(`E[∑_{(i,j) ∉ retained} A i j c i j] = o(n)`) is the paper's legal-screening /
invariant-partition mass-loss statement.  It is NOT proved here; the far-pair
part is controllable from the already-proved expected far-pair mass bound
`expected_optimalFractionalEdgeMass_le_pressure` (mass `≤ (E[V] + |t| G)/(k gap)`),
but the energy bound and the cell-boundary layer remain open.

More importantly, this module also records the composition-theoretic fact that
A1 together with A2 alone does *not* manufacture the frozen-core LLN
`P_w(t) + B ≤ E[Γ]`: combining `Γ ≥ β (V − unret) − γ n` with the proven finite
domination `Γ ≤ V + B` only yields a *relation* between `E[Γ]` and `E[V]`, and
cannot be converted into a lower bound for `E[Γ]` without circularity.  The
direct route to `E[Γ] ≥ P_w + B` is the rooted-scene stationary/Campbell
analysis (Campbell's formula on the limiting forward stationary matching), i.e.
exactly the `hdom` input of
`FinslerCampbellLowerAssembly.campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost`
identified with the limiting frozen core functional.

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

namespace OTSelector

/-- **Lower one-sided passage, arithmetic core.**

Let `slack` be the actual length slack, `F` the frozen physical cost, with the
two-sided Taylor comparison scaled by `k ≥ 0`,
`|k slack - k F| ≤ 2 ε (k F)`, and probes with `|g - h| ≤ probeError`,
`|g| ≤ Bg`.  Then the actual tilted cost, scaled by `1 - 4 ε`, is at most the
unclipped frozen expression plus `γ = 4 ε |t| Bg + |t| probeError`. -/
theorem absoluteFrozenLower_of_relative
    {k ε t probeError Bg slack F h g : ℝ}
    (hk : 0 ≤ k) (hε : 0 < ε) (hε1 : 2 * ε ≤ 1) (hF : 0 ≤ F)
    (hrel : |k * slack - k * F| ≤ 2 * ε * (k * F))
    (hgh : |g - h| ≤ probeError) (hgB : |g| ≤ Bg) :
    (1 - 2 * ε) ^ 2 * (k * slack + t * g) -
        (4 * ε * |t| * Bg + |t| * probeError) ≤
      (1 - 2 * ε) * (k * F) + t * h := by
  have hkF : 0 ≤ k * F := mul_nonneg hk hF
  have h1 : k * slack - k * F ≤ 2 * ε * (k * F) := (abs_le.mp hrel).2
  have htg : -(|t| * Bg) ≤ t * g := by
    have habs : |t * g| ≤ |t| * Bg := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hgB (abs_nonneg t)
    have := neg_abs_le (t * g)
    linarith
  have htgh : t * g - |t| * probeError ≤ t * h := by
    have hdiff : t * (g - h) ≤ |t| * |g - h| := by
      calc t * (g - h) ≤ |t * (g - h)| := le_abs_self _
        _ = |t| * |g - h| := abs_mul _ _
    have hle : t * (g - h) ≤ |t| * probeError :=
      hdiff.trans (mul_le_mul_of_nonneg_left hgh (abs_nonneg t))
    nlinarith
  have hε1' : 0 ≤ 1 - 2 * ε := by linarith
  have hβ0 : 0 ≤ (1 - 2 * ε) ^ 2 := sq_nonneg _
  have hkgtg : -(t * g) ≤ |t| * Bg := by
    have habs : |t * g| ≤ |t| * Bg := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hgB (abs_nonneg t)
    linarith [neg_abs_le (t * g), habs]
  have hmain : (1 - 2 * ε) ^ 2 * (k * slack) ≤ (1 - 2 * ε) * (k * F) := by
    have h1' : k * slack ≤ (k * F) * (1 + 2 * ε) := by nlinarith [h1]
    have h2 : (1 - 2 * ε) ^ 2 * (k * slack) ≤
        (1 - 2 * ε) ^ 2 * ((k * F) * (1 + 2 * ε)) :=
      mul_le_mul_of_nonneg_left h1' hβ0
    have h3 : (1 - 2 * ε) ^ 2 * ((k * F) * (1 + 2 * ε)) =
        ((1 - 2 * ε) * (k * F)) * (1 - 4 * ε ^ 2) := by ring
    have h4 : (1 - 4 * ε ^ 2) ≤ 1 := by nlinarith [sq_nonneg ε]
    have h5 : 0 ≤ (1 - 2 * ε) * (k * F) := mul_nonneg hε1' hkF
    rw [h3] at h2
    calc (1 - 2 * ε) ^ 2 * (k * slack)
        ≤ ((1 - 2 * ε) * (k * F)) * (1 - 4 * ε ^ 2) := h2
      _ ≤ ((1 - 2 * ε) * (k * F)) * 1 := mul_le_mul_of_nonneg_left h4 h5
      _ = (1 - 2 * ε) * (k * F) := by ring
  have hprobe : (1 - 2 * ε) ^ 2 * (t * g) -
      (4 * ε * |t| * Bg + |t| * probeError) ≤ t * h := by
    have hcoef : 0 ≤ 4 * ε * (1 - ε) := by nlinarith
    have hstep : (4 * ε * (1 - ε)) * (-(t * g)) ≤ (4 * ε * (1 - ε)) * (|t| * Bg) :=
      mul_le_mul_of_nonneg_left hkgtg hcoef
    have hle : 4 * ε * (1 - ε) ≤ 4 * ε := by nlinarith [hε.le]
    have hBg0 : 0 ≤ |t| * Bg := mul_nonneg (abs_nonneg t) (le_trans (abs_nonneg g) hgB)
    have hstep2 : (4 * ε * (1 - ε)) * (|t| * Bg) ≤ (4 * ε) * (|t| * Bg) :=
      mul_le_mul_of_nonneg_right hle hBg0
    have hfac : (1 - 2 * ε) ^ 2 * (t * g) = t * g - (4 * ε * (1 - ε)) * (t * g) := by ring
    linarith [htgh, hstep, hstep2, hfac]
  linarith [hmain, hprobe]

end OTSelector

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- **Lower one-sided passage at the frozen core matrix.**

On every retained Taylor edge, the clipped frozen core matrix dominates the
actual tilted cost scaled by `1 - 4 ε`, up to the explicit constant
`γ = 4 ε |t| Bg + |t| probeError`.  This is the lower companion of
`frozenCoreMatrix_le_slack_add_probeBound`: the same two-sided Taylor comparison
`|actual - frozen| ≤ 2 ε frozen` is the geometric input, and only the
arithmetic direction differs. -/
theorem frozenCoreMatrix_lower_of_relative
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenLowerMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 < ε) (hε1 : 2 * ε ≤ 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {n : ℕ} {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hg_bound : ∀ i j, |g i j| ≤ Bg) :
    ∀ i j, (i, j) ∈ Q →
      (1 - 2 * ε) ^ 2 * (k * distanceSlackEdgeCost X Y φ i j + t * g i j) -
        (4 * ε * |t| * Bg + |t| * probeError) ≤
      frozenCoreMatrix C ε z₀ X Y k t h i j := by
  intro i j hij
  obtain ⟨hz₀, hx, hy, hp, hxread, hyread⟩ := hgeom i j hij
  have hb := D.physical_relative hF hcomplete hu ha hinj hε.le hz₀ hx hy hp hxread hyread
  have habs : 0 ≤ |((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) -
      C.frozenPhysicalCost (z₀ i j) (X i) (Y j)| := abs_nonneg _
  have hFnn : 0 ≤ C.frozenPhysicalCost (z₀ i j) (X i) (Y j) := by
    have h2 : 0 ≤ 2 * ε * C.frozenPhysicalCost (z₀ i j) (X i) (Y j) := le_trans habs hb
    nlinarith [hε]
  have hkscale : |k * ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) -
      k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)| ≤
      2 * ε * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) := by
    have hmul : k * ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) -
        k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j) =
        k * (((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) -
          C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) := by ring
    rw [hmul, abs_mul, abs_of_nonneg hk]
    calc k * |((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) -
          C.frozenPhysicalCost (z₀ i j) (X i) (Y j)|
        ≤ k * (2 * ε * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) :=
          mul_le_mul_of_nonneg_left hb hk
      _ = 2 * ε * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) := by ring
  have hslack : distanceSlackEdgeCost X Y φ i j =
      (F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i) := by
    unfold distanceSlackEdgeCost
    rw [hdist (X i) (Y j), hφu (Y j), hφu (X i)]
  have hmain := OTSelector.absoluteFrozenLower_of_relative (k := k) (ε := ε) (t := t)
    (probeError := probeError) (Bg := Bg)
    (slack := (F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i))
    (F := C.frozenPhysicalCost (z₀ i j) (X i) (Y j))
    (h := h i j) (g := g i j) hk hε hε1 hFnn hkscale
    (hgh i j hij) (hg_bound i j)
  rw [hslack]
  refine hmain.trans ?_
  exact le_max_left _ _

/-- **Frozen lower bound at the actual optimal plan (geometric form).**

Composition of the lower one-sided per-edge passage
`frozenCoreMatrix_lower_of_relative` with the deterministic aggregation
`OTSelector.maskedFrozenCost_ge_value_sub_unretained`: for an optimal fractional
assignment of the actual tilted cost, the masked frozen core cost is at least
`(1 - 2 ε)^2` times the retained part of the optimal value, minus the explicit
constants.  This is the form in which the frozen core cost is compared with the
empirical pressure from below. -/
theorem maskedFrozenCost_ge_value_of_geometry
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenLowerCompMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 < ε) (hε1 : 2 * ε ≤ 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {n : ℕ} {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k) (hprobe0 : 0 ≤ probeError) (hBg0 : 0 ≤ Bg)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hg_bound : ∀ i j, |g i j| ≤ Bg)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t) A) :
    (1 - 2 * ε) ^ 2 *
        (fractionalAssignmentCost
            (perturbedEdgeCost (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t) A -
          ∑ i, ∑ j, Qᶜ.indicator (fun p : Fin n × Fin n ↦
            A p.1 p.2 * perturbedEdgeCost
              (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t p.1 p.2) (i, j)) -
        (4 * ε * |t| * Bg + |t| * probeError) * (n : ℝ) ≤
      fractionalAssignmentCost (maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h)) A := by
  classical
  have hγ : 0 ≤ 4 * ε * |t| * Bg + |t| * probeError := by positivity
  refine OTSelector.maskedFrozenCost_ge_value_sub_unretained hA hγ ?_
  intro i j hij
  have hlow := frozenCoreMatrix_lower_of_relative (t := t) hF hcomplete hu ha hinj D hε hε1
    hdist hφu hk hgeom hgh hg_bound i j hij
  simpa only [perturbedEdgeCost] using hlow

end OTSelector.Reconstruction
