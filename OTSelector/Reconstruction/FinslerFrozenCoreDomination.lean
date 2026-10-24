import OTSelector.Reconstruction.FinslerFiniteTilePressure
import OTSelector.Reconstruction.FinslerTileBlockFrozenComparison
import OTSelector.Reconstruction.FiniteDominationCore

/-!
# Geometric pointwise domination for the frozen core

This module is the deterministic bridge between the reconstruction lane's Taylor
relative comparison and the finite-domination lower bound.  The geometric input
is `OriginalPopulationCoefficientCore.TaylorRootCover.physical_relative`
(`FinslerFiniteTilePressure.lean`): on a retained Taylor neighborhood, with the
exact seed readout of both endpoints,

`|(lengthEDist x y).toReal - u y + u x - frozenPhysicalCost z₀ x y|`
`  ≤ 2 ε * frozenPhysicalCost z₀ x y`.

The file proves:

1. the one-sided consequence
   `(1 - 2 ε) * frozenPhysicalCost ≤ actual slack`;
2. the matrix-level pointwise bound for the frozen core matrix
   `E i j = max ((1 - 2 ε) * (k * frozenPhysicalCost) + t * modelProbe i j) 0`,
   namely `E i j ≤ k * distanceSlackEdgeCost X Y φ i j + t * physicalProbe i j
   + |t| * probeError` on the mask, from the model/physical probe difference;
3. composition with `FiniteDominationCore.empiricalFrozenCore_div_le_pressure_add`
   and its masked variants, giving the deterministic frozen-core bound for every
   optimal fractional assignment;
4. the resulting `PointProcess.FiniteDominationInequality` for a stochastic
   family with almost-sure geometric, readout and optimality hypotheses.

## Constants

Two probe constants occur.  `probeError` bounds the model/physical probe
difference `|g i j - h i j|`.  `Bg` bounds the physical probe `|g i j|` and is
the constant `B_t = |t| * Bg` used in the paper's finite domination.  The
`probeError` form is stated with the explicit nonnegativity hypothesis
`0 ≤ k * slack + t * g + |t| * probeError`; the `Bg` form discharges it from
`k * slack ≥ 0`, `|g| ≤ Bg` and `probeError ≤ Bg`.  This is exactly the
nonnegativity side condition used by the core inequality.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-! ## The frozen core matrix -/

/-- The frozen core matrix of a retained tile: the clipped weighted frozen cost
plus the model probe term, restricted to a mask `Q` by the caller. -/
noncomputable def frozenCoreMatrix
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (ε : ℝ)
    {n : ℕ} (z₀ : Fin n → Fin n → Z) (X Y : Fin n → M) (k t : ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    max ((1 - 2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) +
      t * h i j) 0

/-- The frozen core matrix is entrywise nonnegative by construction. -/
theorem frozenCoreMatrix_nonneg
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (ε : ℝ)
    {n : ℕ} (z₀ : Fin n → Fin n → Z) (X Y : Fin n → M) (k t : ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) :
    ∀ i j, 0 ≤ frozenCoreMatrix C ε z₀ X Y k t h i j :=
  fun _ _ ↦ le_max_right _ _

/-- The frozen core matrix is definitionally the clipped frozen expression. -/
theorem frozenCoreMatrix_apply
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (ε : ℝ)
    {n : ℕ} (z₀ : Fin n → Fin n → Z) (X Y : Fin n → M) (k t : ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    frozenCoreMatrix C ε z₀ X Y k t h i j =
      max ((1 - 2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) +
        t * h i j) 0 := rfl

/-- The explicit geometric and exact-readout hypotheses of one frozen edge:
the reference center, source and target roots in its Taylor neighborhood, the
coordinate window, and the exact seed readout of both endpoints. -/
abbrev FrozenCoreEdgeGeometry
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {ε : ℝ}
    (D : C.TaylorRootCover ε) {n : ℕ} (z₀ : Fin n → Fin n → Z)
    (X Y : Fin n → M) (i j : Fin n) : Prop :=
  z₀ i j ∈ D.centers ∧
  a (X i) ∈ C.roots ∩ D.neighborhood (z₀ i j) ∧
  a (Y j) ∈ C.roots ∩ D.neighborhood (z₀ i j) ∧
  (u (X i), u (Y j)) ∈ C.window.region ∧
  X i = (P C.seedIndex).seed.curve
    (populationSeedRootLabelValue (P C.seedIndex).seed a (a (X i)))
    (u (X i) - (P C.seedIndex).seed.level) ∧
  Y j = (P C.seedIndex).seed.curve
    (populationSeedRootLabelValue (P C.seedIndex).seed a (a (Y j)))
    (u (Y j) - (P C.seedIndex).seed.level)

section Geometry

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenCoreMetric : MetricSpace M := F.metricSpace;
    LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

namespace OriginalPopulationCoefficientCore

/-- **One-sided Taylor domination.**  The relative Taylor comparison
`|actual - frozen| ≤ 2 ε * frozen` implies
`(1 - 2 ε) * frozen ≤ actual`.

The hypothesis `2 ε < 1` is recorded for the geometric smallness regime; the
one-sided inequality itself does not use it. -/
theorem TaylorRootCover.frozenPhysicalCost_le_slack_of_relative
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (_hε1 : 2 * ε < 1)
    {z₀ : Z} {x y : M}
    (hz₀ : z₀ ∈ D.centers)
    (hx : a x ∈ C.roots ∩ D.neighborhood z₀)
    (hy : a y ∈ C.roots ∩ D.neighborhood z₀)
    (hp : (u x, u y) ∈ C.window.region)
    (hxread : x = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a x))
      (u x - (P C.seedIndex).seed.level))
    (hyread : y = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a y))
      (u y - (P C.seedIndex).seed.level)) :
    (1 - 2 * ε) * C.frozenPhysicalCost z₀ x y ≤
      (F.lengthEDist x y).toReal - u y + u x := by
  have hb := D.physical_relative hF hcomplete hu ha hinj hε hz₀ hx hy hp hxread hyread
  have hlower : -((2 * ε) * C.frozenPhysicalCost z₀ x y) ≤
      ((F.lengthEDist x y).toReal - u y + u x) - C.frozenPhysicalCost z₀ x y :=
    (abs_le.mp hb).1
  have hfac : (1 - 2 * ε) * C.frozenPhysicalCost z₀ x y =
      C.frozenPhysicalCost z₀ x y - (2 * ε) * C.frozenPhysicalCost z₀ x y := by ring
  rw [hfac]
  linarith

end OriginalPopulationCoefficientCore

/-! ## The pointwise matrix bound -/

variable {n : ℕ}

/-- **Unclipped pointwise domination.**  On a retained edge, the frozen
expression `(1 - 2 ε) * k * frozen + t * h` is at most the physical tilted edge
cost `k * slack + t * g` plus the scaled model-probe error.

The distance is the ambient `PseudoMetricSpace` distance, assumed to agree with
the Finsler length via `hdist`; the potential `φ` agrees with `u` via `hφu`. -/
theorem frozenCoreMatrix_expression_le_slack_add_probeError
    [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    {k t probeError : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q →
      FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError) :
    ∀ i j, (i, j) ∈ Q →
      (1 - 2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) + t * h i j ≤
        k * distanceSlackEdgeCost X Y φ i j + t * g i j + |t| * probeError := by
  intro i j hij
  obtain ⟨hz₀, hx, hy, hp, hxread, hyread⟩ := hgeom i j hij
  have hrel := D.frozenPhysicalCost_le_slack_of_relative hF hcomplete hu ha hinj
    hε hε1 hz₀ hx hy hp hxread hyread
  have hslack : distanceSlackEdgeCost X Y φ i j =
      (F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i) := by
    unfold distanceSlackEdgeCost
    rw [hdist (X i) (Y j), hφu (Y j), hφu (X i)]
  have hscaled : (1 - 2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) ≤
      k * distanceSlackEdgeCost X Y φ i j := by
    rw [hslack]
    calc (1 - 2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) =
          k * ((1 - 2 * ε) * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) := by ring
      _ ≤ k * ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) :=
          mul_le_mul_of_nonneg_left hrel hk
  have hth : t * h i j ≤ t * g i j + |t| * probeError := by
    have hdiff : t * (h i j - g i j) ≤ |t| * |h i j - g i j| := by
      calc t * (h i j - g i j) ≤ |t * (h i j - g i j)| := le_abs_self _
        _ = |t| * |h i j - g i j| := abs_mul _ _
    have habs : |h i j - g i j| ≤ probeError := by
      rw [abs_sub_comm]
      exact hgh i j hij
    have hle : t * (h i j - g i j) ≤ |t| * probeError :=
      hdiff.trans (mul_le_mul_of_nonneg_left habs (abs_nonneg t))
    nlinarith
  linarith

/-- **Clipped pointwise domination with the model-probe error.**  The frozen
core matrix `max (... ) 0` is bounded by the physical tilted edge cost plus
`|t| * probeError`, provided the right-hand side is nonnegative on the mask. -/
theorem frozenCoreMatrix_le_slack_add_probeError
    [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    {k t probeError : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q →
      FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hR_nonneg : ∀ i j, (i, j) ∈ Q →
      0 ≤ k * distanceSlackEdgeCost X Y φ i j + t * g i j + |t| * probeError) :
    ∀ i j, (i, j) ∈ Q →
      frozenCoreMatrix C ε z₀ X Y k t h i j ≤
        k * distanceSlackEdgeCost X Y φ i j + t * g i j + |t| * probeError := by
  intro i j hij
  rw [frozenCoreMatrix_apply C ε z₀ X Y k t h i j]
  refine max_le ?_ (hR_nonneg i j hij)
  exact frozenCoreMatrix_expression_le_slack_add_probeError (k := k) (t := t)
    (probeError := probeError) hF hcomplete hu ha hinj
    D hε hε1 hdist hφu hk hgeom hgh i j hij

/-- The right-hand side with the probe bound `Bg` is nonnegative when
`k * slack ≥ 0` and `|g| ≤ Bg`. -/
theorem slack_add_probeBound_nonneg
    {c g : Matrix (Fin n) (Fin n) ℝ} {Bg t : ℝ}
    (hc_nonneg : ∀ i j, 0 ≤ c i j)
    (hg_bound : ∀ i j, |g i j| ≤ Bg) :
    ∀ i j, 0 ≤ c i j + t * g i j + |t| * Bg := by
  intro i j
  have habs : |t * g i j| ≤ |t| * Bg := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hg_bound i j) (abs_nonneg t)
  have hlow : -(|t| * Bg) ≤ t * g i j := by
    have h := neg_abs_le (t * g i j)
    linarith
  linarith [hc_nonneg i j]

/-- **Clipped pointwise domination with the probe bound.**  Fully discharged
form with `B = |t| * Bg`: the nonnegativity side condition follows from
`c ≥ 0` and `|g| ≤ Bg`, and the model error is dominated by `Bg`. -/
theorem frozenCoreMatrix_le_slack_add_probeBound
    [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q →
      FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hg_bound : ∀ i j, |g i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg) :
    ∀ i j, (i, j) ∈ Q →
      frozenCoreMatrix C ε z₀ X Y k t h i j ≤
        k * distanceSlackEdgeCost X Y φ i j + t * g i j + |t| * Bg := by
  intro i j hij
  have hc_nonneg : ∀ i j, 0 ≤ k * distanceSlackEdgeCost X Y φ i j :=
    fun i j ↦ mul_nonneg hk (distanceSlackEdgeCost_nonneg X Y φ hφ i j)
  have hR : ∀ i j, 0 ≤
      k * distanceSlackEdgeCost X Y φ i j + t * g i j + |t| * Bg :=
    slack_add_probeBound_nonneg hF hcomplete hu ha hinj hc_nonneg hg_bound
  have hexpr := frozenCoreMatrix_expression_le_slack_add_probeError (k := k) (t := t)
    (probeError := probeError) hF hcomplete hu ha hinj D hε hε1 hdist hφu hk hgeom hgh
    i j hij
  have herr : |t| * probeError ≤ |t| * Bg :=
    mul_le_mul_of_nonneg_left hprobeError_le (abs_nonneg t)
  have hA : (1 - 2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) + t * h i j ≤
      k * distanceSlackEdgeCost X Y φ i j + t * g i j + |t| * Bg := by
    linarith
  rw [frozenCoreMatrix_apply C ε z₀ X Y k t h i j]
  exact max_le hA (hR i j)

/-! ## Composition with the finite-domination core -/

/-- **Deterministic frozen-core bound, model-probe-error form.**

For every optimal fractional assignment `P` of the tilted physical cost, the
normalized masked frozen cost is at most the normalized empirical pressure plus
`|t| * probeError`.  The nonnegativity side condition for the masked core
inequality is explicit (`hR_nonneg`), because the frozen expression is clipped
at zero and the complement of the mask contributes zero. -/
theorem frozenCore_div_le_pressure_add_of_probeError
    [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {n : ℕ} (hn : 0 < n)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    {k t probeError : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    {Pmat : Matrix (Fin n) (Fin n) ℝ}
    (hP : OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t) Pmat)
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hR_nonneg : ∀ i j,
      0 ≤ k * distanceSlackEdgeCost X Y φ i j + t * g i j + |t| * probeError) :
    fractionalAssignmentCost
        (maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h)) Pmat / (n : ℝ) ≤
      perturbedAssignmentValue
        (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t / (n : ℝ) +
        |t| * probeError := by
  refine OTSelector.maskedFrozenCost_div_le_perturbedAssignmentValue_div_add
    (n := n) (c := fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) (g := g)
    (d := frozenCoreMatrix C ε z₀ X Y k t h) (P := Pmat) (t := t)
    (B := |t| * probeError) (Q := Q) hn ?_ hP ?_ hR_nonneg
  · exact frozenCoreMatrix_nonneg C ε z₀ X Y k t h
  · intro i j hij
    exact frozenCoreMatrix_le_slack_add_probeError (k := k) (t := t)
      (probeError := probeError) hF hcomplete hu ha hinj D hε hε1 hdist hφu hk
      hgeom hgh (fun i j _ ↦ hR_nonneg i j) i j hij

/-- **Deterministic frozen-core bound, probe-bound form.**

The nonnegativity side condition is discharged from `k * slack ≥ 0`,
`|g| ≤ Bg` and `probeError ≤ Bg`, so the bound is unconditional given the
geometric edge hypotheses and the optimality of `P`.  The constant is the
paper's `B_t = |t| * Bg`. -/
theorem frozenCore_div_le_pressure_add_of_probeBound
    [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {n : ℕ} (hn : 0 < n)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    {Pmat : Matrix (Fin n) (Fin n) ℝ}
    (hP : OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t) Pmat)
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hg_bound : ∀ i j, |g i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg) :
    fractionalAssignmentCost
        (maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h)) Pmat / (n : ℝ) ≤
      perturbedAssignmentValue
        (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t / (n : ℝ) +
        |t| * Bg := by
  have hd_bound : ∀ i j, (i, j) ∈ Q →
      frozenCoreMatrix C ε z₀ X Y k t h i j ≤
        perturbedEdgeCost
          (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) g t i j + |t| * Bg := by
    intro i j hij
    exact frozenCoreMatrix_le_slack_add_probeBound (k := k) (t := t)
      (probeError := probeError) (Bg := Bg) hF hcomplete hu ha hinj D hε hε1
      hdist hφu hφ hk hgeom hgh hg_bound hprobeError_le i j hij
  exact OTSelector.empiricalFrozenCore_div_le_pressure_add X Y φ hφ g
    (Bprobe := Bg) (B := |t| * Bg) (hB := rfl) hn hk hg_bound
    (Q := Q) (d := frozenCoreMatrix C ε z₀ X Y k t h)
    (frozenCoreMatrix_nonneg C ε z₀ X Y k t h) hP hd_bound

/-! ## The stochastic finite-domination interface -/

section Stochastic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Stochastic finite-domination from the geometric edge hypotheses
(model-probe-error form).**

If almost surely every retained edge satisfies the Taylor/readout hypotheses, the
model/physical probe difference is at most `probeError`, the tilted cost plus
`|t| * probeError` is nonnegative, and the plan is optimal for the tilted
physical cost, then the normalized masked frozen cost and the normalized
pressure satisfy `FiniteDominationInequality`. -/
theorem finiteDominationInequality_of_geometric_probeError
    [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
    (X Y : ∀ n, Ω → Fin (N n) → M)
    (z₀ : ∀ n, Ω → Fin (N n) → Fin (N n) → Z)
    (h : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (g : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    {k t probeError : ℝ} (hk : 0 ≤ k)
    {Q : ∀ n, Ω → Set (Fin (N n) × Fin (N n))}
    (Pmat : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hP : ∀ n, ∀ᵐ x ∂μ, OptimalFractionalAssignment
      (perturbedEdgeCost
        (fun i j ↦ k * distanceSlackEdgeCost (X n x) (Y n x) φ i j) (g n x) t)
      (Pmat n x))
    (hgeom : ∀ n, ∀ᵐ x ∂μ, ∀ i j, (i, j) ∈ Q n x →
      FrozenCoreEdgeGeometry C D (z₀ n x) (X n x) (Y n x) i j)
    (hgh : ∀ n, ∀ᵐ x ∂μ, ∀ i j, (i, j) ∈ Q n x →
      |g n x i j - h n x i j| ≤ probeError)
    (hR : ∀ n, ∀ᵐ x ∂μ, ∀ i j,
      0 ≤ k * distanceSlackEdgeCost (X n x) (Y n x) φ i j +
        t * g n x i j + |t| * probeError) :
    OTSelector.PointProcess.FiniteDominationInequality μ
      (fun n x ↦ fractionalAssignmentCost
        (maskedFrozenCost (Q n x)
          (frozenCoreMatrix C ε (z₀ n x) (X n x) (Y n x) k t (h n x)))
        (Pmat n x) / (N n : ℝ))
      (fun n x ↦ perturbedAssignmentValue
        (fun i j ↦ k * distanceSlackEdgeCost (X n x) (Y n x) φ i j)
        (g n x) t / (N n : ℝ))
      (|t| * probeError) := by
  refine OTSelector.PointProcess.finiteDominationInequality_of_ae_bound ?_
  intro n
  filter_upwards [hP n, hgeom n, hgh n, hR n] with x hPx hgeomx hghx hRx
  exact frozenCore_div_le_pressure_add_of_probeError (n := N n)
    (X := X n x) (Y := Y n x) (φ := φ) (hφu := hφu) (z₀ := z₀ n x)
    (h := h n x) (g := g n x) (Q := Q n x) (Pmat := Pmat n x)
    hF hcomplete hu ha hinj D hε hε1 hdist (hN n) hk hPx hgeomx hghx hRx

/-- **Stochastic finite-domination from the geometric edge hypotheses
(probe-bound form).**

The nonnegativity side condition is discharged from `k ≥ 0`, `|g| ≤ Bg` and
`probeError ≤ Bg`; the constant is `|t| * Bg`. -/
theorem finiteDominationInequality_of_geometric_probeBound
    [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : LipschitzWith 1 φ)
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
    (X Y : ∀ n, Ω → Fin (N n) → M)
    (z₀ : ∀ n, Ω → Fin (N n) → Fin (N n) → Z)
    (h : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (g : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {Q : ∀ n, Ω → Set (Fin (N n) × Fin (N n))}
    (Pmat : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (hP : ∀ n, ∀ᵐ x ∂μ, OptimalFractionalAssignment
      (perturbedEdgeCost
        (fun i j ↦ k * distanceSlackEdgeCost (X n x) (Y n x) φ i j) (g n x) t)
      (Pmat n x))
    (hgeom : ∀ n, ∀ᵐ x ∂μ, ∀ i j, (i, j) ∈ Q n x →
      FrozenCoreEdgeGeometry C D (z₀ n x) (X n x) (Y n x) i j)
    (hgh : ∀ n, ∀ᵐ x ∂μ, ∀ i j, (i, j) ∈ Q n x →
      |g n x i j - h n x i j| ≤ probeError)
    (hg_bound : ∀ n, ∀ᵐ x ∂μ, ∀ i j, |g n x i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg) :
    OTSelector.PointProcess.FiniteDominationInequality μ
      (fun n x ↦ fractionalAssignmentCost
        (maskedFrozenCost (Q n x)
          (frozenCoreMatrix C ε (z₀ n x) (X n x) (Y n x) k t (h n x)))
        (Pmat n x) / (N n : ℝ))
      (fun n x ↦ perturbedAssignmentValue
        (fun i j ↦ k * distanceSlackEdgeCost (X n x) (Y n x) φ i j)
        (g n x) t / (N n : ℝ))
      (|t| * Bg) := by
  refine OTSelector.PointProcess.finiteDominationInequality_of_ae_bound ?_
  intro n
  filter_upwards [hP n, hgeom n, hgh n, hg_bound n] with x hPx hgeomx hghx hgx
  exact frozenCore_div_le_pressure_add_of_probeBound (n := N n)
    (X := X n x) (Y := Y n x) (φ := φ) (hφu := hφu) (hφ := hφ)
    (z₀ := z₀ n x) (h := h n x) (g := g n x) (Q := Q n x) (Pmat := Pmat n x)
    hF hcomplete hu ha hinj D hε hε1 hdist (hN n) hk hPx hgeomx hghx hgx
    hprobeError_le

end Stochastic

end Geometry

end OTSelector.Reconstruction
