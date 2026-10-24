import OTSelector.Probability.FinslerTileBlockLawComparison
import OTSelector.Probability.MarkedBlockValueIntegral
import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.FinslerAtlasCoordinateLaw
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.Reconstruction.FinslerTileBlockFrozenComparison

/-!
# Instantiation of the marked kinetic kernel by a scaled quadratic matrix

`markedKineticKernel r kin markS markT x y` evaluates the model kinetic
`kin : A → B → (Fin q → ℝ) → ℝ` at the marks of `x` and `y` and at the clamped
cube displacement of their coordinates.  This module supplies the concrete
instantiation of that kernel by a scaled quadratic matrix field

`matrixQuadratic (M a b) v`,

together with the estimates needed by the frozen-comparison lane:

1. `mDisplacement_atlasSeedCoord`: on the open unit cube, the clamped
   displacement of two atlas seed coordinates is the basis image of the
   difference of the two root label vectors.
2. `scaledMatrixKineticKernel`: the model kinetic
   `fun a b v => w ^ (-(2/q)) * matrixQuadratic (M a b) v`.
3. `markedKineticKernel_scaledMatrixKineticKernel` (unfolding) and
   `abs_markedKineticKernel_scaled_le` (the uniform per-edge bound
   `r ^ (2/q) * w ^ (-(2/q)) * C * q` from the quadratic bound).
4. The floor-scale asymptotics: for `r n = ⌊(n+1) w⌋`, the factor
   `r n ^ (2/q) * w ^ (-(2/q))` divided by `(n+1) ^ (2/q)` tends to one, and
   the resulting one-sided scale error is a sequence tending to zero.
5. `abs_finslerTileKinetic_sub_markedKineticKernel_le`: the `hrel`-shaped
   relative comparison between the physical kinetic and the marked kernel,
   combining the Taylor relative bound `2 ε` with the floor scale error.  The
   geometric curve readout at the two endpoints is kept as the explicit
   hypothesis `hread`.

No `sorry`, `admit` or added axiom occurs.
-/

open MeasureTheory ProbabilityTheory Filter Set Function Matrix Manifold OTSelector.Geometry
open OTSelector.Reconstruction
open scoped BigOperators NNReal ENNReal Topology ContDiff Matrix.Norms.Operator

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Probability

/-! ## The clamped displacement of atlas seed coordinates -/

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **The clamped displacement of two atlas seed coordinates.**  On the open
unit cube the truncation is the identity, so the clamped displacement of the
coordinates of `z` and `z'` is the basis coordinate of the difference of the
two root label vectors. -/
theorem mDisplacement_atlasSeedCoord {q : ℕ} (S : F.CalibratedLevelSeedPatch u)
    (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) (a : M → Z) (z z' : Z)
    (hz : atlasSeedCoord S e a z ∈ unitCubeSet q)
    (hz' : atlasSeedCoord S e a z' ∈ unitCubeSet q) :
    mDisplacement (atlasSeedCoord S e a z) (atlasSeedCoord S e a z') =
      e (populationSeedRootLabelValue S a z' - populationSeedRootLabelValue S a z) := by
  rw [mDisplacement_eq_sub_of_mem hz hz']
  funext l
  simp only [atlasSeedCoord, map_sub, Pi.sub_apply]

/-! ## The scaled matrix kinetic kernel -/

/-- **The scaled matrix kinetic kernel.**  The model kinetic obtained from a
matrix field `M` by the quadratic form `matrixQuadratic (M a b) v`, scaled by
the inverse of the tile weight at the exponent `2 / q`. -/
noncomputable def scaledMatrixKineticKernel (q : ℕ) (w : unitInterval)
    (M : (Fin q → ℝ) → (Fin q → ℝ) → Matrix (Fin q) (Fin q) ℝ) :
    (Fin q → ℝ) → (Fin q → ℝ) → (Fin q → ℝ) → ℝ :=
  fun a b v => ((w : ℝ) ^ (-(2 / (q : ℝ)))) * matrixQuadratic (M a b) v

/-- The defining equation of the scaled matrix kinetic kernel. -/
theorem scaledMatrixKineticKernel_apply (q : ℕ) (w : unitInterval)
    (M : (Fin q → ℝ) → (Fin q → ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (a b v : Fin q → ℝ) :
    scaledMatrixKineticKernel q w M a b v =
      ((w : ℝ) ^ (-(2 / (q : ℝ)))) * matrixQuadratic (M a b) v := rfl

/-- **Unfolding of the marked kinetic kernel at a scaled matrix kernel.**  For
arbitrary coordinate and mark maps, the marked kinetic cost is the scale
`r ^ (2/q)` times the weighted quadratic form of the clamped displacement. -/
theorem markedKineticKernel_scaledMatrixKineticKernel {Xs Yt : Type*}
    [MeasurableSpace Xs] [MeasurableSpace Yt] {q : ℕ} (w : unitInterval)
    (M : (Fin q → ℝ) → (Fin q → ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (markS : Xs → (Fin q → ℝ) × (Fin q → ℝ))
    (markT : Yt → (Fin q → ℝ) × (Fin q → ℝ)) (r : ℝ) (x : Xs) (y : Yt) :
    markedKineticKernel r (scaledMatrixKineticKernel q w M) markS markT x y =
      r ^ (2 / (q : ℝ)) *
        (((w : ℝ) ^ (-(2 / (q : ℝ)))) *
          matrixQuadratic (M (markS x).2 (markT y).2)
            (mDisplacement (markS x).1 (markT y).1)) := rfl

/-- **Uniform per-edge bound for the scaled matrix kinetic kernel.**  If every
quadratic form is bounded by `C * ∑ l, v l ^ 2`, the clamped displacement has
squared sum at most `q`, and the scale is nonnegative, then the marked kinetic
cost is at most `r ^ (2/q) * w ^ (-(2/q)) * C * q`. -/
theorem abs_markedKineticKernel_scaled_le {Xs Yt : Type*}
    [MeasurableSpace Xs] [MeasurableSpace Yt] {q : ℕ} (hq : 0 < q)
    {w : unitInterval} (hw : 0 < (w : ℝ))
    (M : (Fin q → ℝ) → (Fin q → ℝ) → Matrix (Fin q) (Fin q) ℝ)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hM : ∀ a b v, |matrixQuadratic (M a b) v| ≤ C * ∑ l, v l ^ 2)
    (markS : Xs → (Fin q → ℝ) × (Fin q → ℝ))
    (markT : Yt → (Fin q → ℝ) × (Fin q → ℝ)) (x : Xs) (y : Yt) :
    |markedKineticKernel r (scaledMatrixKineticKernel q w M) markS markT x y| ≤
      r ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) * C * (q : ℝ) := by
  have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  have hwpow : 0 ≤ (w : ℝ) ^ (-(2 / (q : ℝ))) := Real.rpow_nonneg (le_of_lt hw) _
  have hsum := mDisplacement_sq_sum_le q (markS x).1 (markT y).1
  have hquad : |matrixQuadratic (M (markS x).2 (markT y).2)
      (mDisplacement (markS x).1 (markT y).1)| ≤ C * (q : ℝ) := by
    refine (hM (markS x).2 (markT y).2 _).trans ?_
    exact mul_le_mul_of_nonneg_left hsum hC
  rw [markedKineticKernel_scaledMatrixKineticKernel, abs_mul, abs_of_nonneg hrpow,
    abs_mul, abs_of_nonneg hwpow]
  calc r ^ (2 / (q : ℝ)) *
        ((w : ℝ) ^ (-(2 / (q : ℝ))) *
          |matrixQuadratic (M (markS x).2 (markT y).2)
            (mDisplacement (markS x).1 (markT y).1)|)
      ≤ r ^ (2 / (q : ℝ)) *
          ((w : ℝ) ^ (-(2 / (q : ℝ))) * (C * (q : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hquad hwpow) hrpow
    _ = r ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) * C * (q : ℝ) := by ring

/-! ## The floor scale asymptotics -/

/-- The floor radius `r n = ⌊(n + 1) w⌋` of the frozen marked kernel. -/
noncomputable def scaledFloorRadius (w : unitInterval) (n : ℕ) : ℝ :=
  ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ)

/-- The floor radius is nonnegative. -/
theorem scaledFloorRadius_nonneg (w : unitInterval) (n : ℕ) : 0 ≤ scaledFloorRadius w n :=
  Nat.cast_nonneg _

/-- The scale factor `r n ^ (2/q) * w ^ (-(2/q))` applied to a frozen cost. -/
noncomputable def floorScaleFactor (q : ℕ) (w : unitInterval) (n : ℕ) : ℝ :=
  scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ)))

/-- The physical scale factor `(n + 1) ^ (2/q)`. -/
noncomputable def sampleScaleFactor (q : ℕ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ))

/-- **The floor scale divided by the physical scale tends to one.**  If
`⌊(n+1) w⌋ / (n+1) → w` with `w > 0`, then the relative floor scale factor
`r n ^ (2/q) * w ^ (-(2/q)) / (n+1) ^ (2/q)` tends to one. -/
theorem tendsto_floorScaleFactor_div_sampleScaleFactor {q : ℕ} (hq : 0 < q)
    {w : unitInterval} (hw : 0 < (w : ℝ))
    (hr : Tendsto (fun n : ℕ => scaledFloorRadius w n / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (w : ℝ))) :
    Tendsto (fun n : ℕ => scaledFloorRadius w n ^ (2 / (q : ℝ)) *
        (w : ℝ) ^ (-(2 / (q : ℝ))) / (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))))
      atTop (𝓝 1) := by
  have hpow : Tendsto
      (fun n : ℕ => (scaledFloorRadius w n / ((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)))
      atTop (𝓝 ((w : ℝ) ^ (2 / (q : ℝ)))) :=
    hr.rpow_const (Or.inl hw.ne')
  have hconst : Tendsto (fun n : ℕ =>
      (scaledFloorRadius w n / ((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) *
        (w : ℝ) ^ (-(2 / (q : ℝ)))) atTop
      (𝓝 ((w : ℝ) ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))))) :=
    hpow.mul_const _
  have hprod : (w : ℝ) ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) = 1 := by
    rw [← Real.rpow_add hw (2 / (q : ℝ)) (-(2 / (q : ℝ))), add_neg_cancel,
      Real.rpow_zero]
  rw [hprod] at hconst
  refine hconst.congr' ?_
  filter_upwards with n
  rw [Real.div_rpow (scaledFloorRadius_nonneg w n) (by positivity)]
  ring

/-- The relative floor scale error `|r n ^ (2/q) w ^ (-(2/q)) / (n+1) ^ (2/q) - 1|`. -/
noncomputable def floorScaleError (q : ℕ) (w : unitInterval) (n : ℕ) : ℝ :=
  |scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) /
      (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) - 1|

/-- The relative floor scale error is nonnegative. -/
theorem floorScaleError_nonneg (q : ℕ) (w : unitInterval) (n : ℕ) :
    0 ≤ floorScaleError q w n := abs_nonneg _

/-- The relative floor scale error tends to zero. -/
theorem tendsto_floorScaleError {q : ℕ} (hq : 0 < q) {w : unitInterval}
    (hw : 0 < (w : ℝ))
    (hr : Tendsto (fun n : ℕ => scaledFloorRadius w n / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (w : ℝ))) :
    Tendsto (floorScaleError q w) atTop (𝓝 0) := by
  have h := tendsto_floorScaleFactor_div_sampleScaleFactor (q := q) hq hw hr
  have h' : Tendsto (fun n : ℕ =>
      scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) /
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) - 1) atTop (𝓝 (1 - 1)) :=
    h.sub_const 1
  change Tendsto (fun n : ℕ =>
    |scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) /
      (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) - 1|) atTop (𝓝 0)
  simpa only [sub_self, abs_zero] using h'.abs

/-- **The one-sided floor scale error.**  For nonnegative `X`, the difference
between the floor-scaled cost and the physical-scaled cost is at most the
relative floor scale error times the physical-scaled cost. -/
theorem floorScaleError_spec {q : ℕ} (w : unitInterval) (n : ℕ) {X : ℝ}
    (hX : 0 ≤ X) :
    |scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) * X -
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) * X| ≤
      floorScaleError q w n * (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) * X := by
  set s : ℝ := scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ)))
    with hs
  set t : ℝ := (((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have hcalc : s * X - t * X = (s / t - 1) * t * X := by
    field_simp [ht.ne']
  rw [hcalc, abs_mul, abs_mul, abs_of_nonneg (le_of_lt ht), abs_of_nonneg hX]
  simp only [floorScaleError, hs, ht_def]
  exact le_rfl

/-- **Existence of the floor scale error sequence.**  There is a nonnegative
sequence `ε` tending to zero such that, eventually, the relative difference
between the floor scale and the physical scale is at most `ε n` on every
nonnegative frozen cost. -/
theorem exists_floorScale_error {q : ℕ} (hq : 0 < q) {w : unitInterval}
    (hw : 0 < (w : ℝ))
    (hr : Tendsto (fun n : ℕ => scaledFloorRadius w n / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (w : ℝ))) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ X : ℝ, 0 ≤ X →
        |scaledFloorRadius w n ^ (2 / (q : ℝ)) *
            (w : ℝ) ^ (-(2 / (q : ℝ))) * X -
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) * X| ≤
        ε n * (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) * X :=
  ⟨floorScaleError q w, floorScaleError_nonneg q w,
    tendsto_floorScaleError hq hw hr, Filter.Eventually.of_forall fun n X hX =>
      floorScaleError_spec (q := q) w n hX⟩

/-! ## Combining the Taylor and floor scale errors -/

/-- **Relative comparison from a Taylor and a scale error.**  If `phys` is
within relative error `2 ε` of `t * Q`, and the scale `s` is within relative
error `εs < 1` of `t`, then `phys` is within relative error
`2 ε + (εs + 2 ε εs) / (1 - εs)` of `s * Q`. -/
theorem abs_sub_le_of_scale_error {phys Q s t ε εs : ℝ}
    (hε : 0 ≤ ε) (hεs0 : 0 ≤ εs) (hεs1 : εs < 1)
    (hQ : 0 ≤ Q) (ht : 0 < t) (hs : 0 ≤ s)
    (hphys : |phys - t * Q| ≤ 2 * ε * (t * Q))
    (hscale : |s * Q - t * Q| ≤ εs * (t * Q)) :
    |phys - s * Q| ≤ (2 * ε + (εs + 2 * ε * εs) / (1 - εs)) * (s * Q) := by
  have htQ : 0 ≤ t * Q := mul_nonneg (le_of_lt ht) hQ
  have hpos : 0 < 1 - εs := by linarith
  have hsQlower : (1 - εs) * (t * Q) ≤ s * Q := by
    have h := (abs_le.mp hscale).1
    nlinarith
  have hKle : t * Q ≤ s * Q / (1 - εs) := by
    rw [le_div_iff₀ hpos]
    calc t * Q * (1 - εs) = (1 - εs) * (t * Q) := by ring
      _ ≤ s * Q := hsQlower
  have htri : |phys - s * Q| ≤ |phys - t * Q| + |t * Q - s * Q| := by
    calc |phys - s * Q| = |(phys - t * Q) + (t * Q - s * Q)| := by
          congr 1
          ring
      _ ≤ |phys - t * Q| + |t * Q - s * Q| := abs_add_le _ _
  have hstep : |phys - s * Q| ≤ (2 * ε + εs) * (t * Q) := by
    refine htri.trans ?_
    have h2 : |t * Q - s * Q| = |s * Q - t * Q| := abs_sub_comm _ _
    rw [h2]
    calc |phys - t * Q| + |s * Q - t * Q| ≤ 2 * ε * (t * Q) + εs * (t * Q) :=
          add_le_add hphys hscale
      _ = (2 * ε + εs) * (t * Q) := by ring
  have hcoef : 0 ≤ 2 * ε + εs := by linarith
  calc |phys - s * Q| ≤ (2 * ε + εs) * (t * Q) := hstep
    _ ≤ (2 * ε + εs) * (s * Q / (1 - εs)) :=
        mul_le_mul_of_nonneg_left hKle hcoef
    _ = (2 * ε + (εs + 2 * ε * εs) / (1 - εs)) * (s * Q) := by
        field_simp [hpos.ne']
        ring

end OTSelector.Probability

namespace OTSelector.Reconstruction

open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]

/-- **The `hrel`-shape relative comparison against the marked kernel.**

For a retained Taylor cover of an original population coefficient core and two
physical points `X i`, `Y j` in one common tile, assume:

* the geometric Taylor data (`hcenter`, `hxroot`, `hyroot`, `hp`) and the curve
  readout at the two endpoints (`hread`), which give the relative Taylor bound
  `2 ε` of `abs_finslerTileKinetic_sub_frozenPhysical_le`;
* the atlas cube membership of the two seed coordinates (`hcubeS`, `hcubeT`)
  and the identification `hbasis` of the coordinate equivalence `e` with the
  basis used by `frozenPhysicalCost`;
* the floor scale data `w`, `hq`, `hw` and the ratio convergence `hr`, which
  give the relative floor scale error.

Then, eventually in `n`, the physical kinetic at scale `(n+1) ^ (2/q)` is
within relative error `2 ε + η n` of the marked kinetic kernel at the floor
radius `⌊(n+1) w⌋`, for some nonnegative sequence `η` tending to zero.  The
matrix field is the constant coefficient matrix of the core at the reference
root and the two heights, and the mark maps read the atlas seed coordinates.

The remaining geometric input is exactly the curve readout `hread`; it is not
proved here. -/
theorem abs_finslerTileKinetic_sub_markedKineticKernel_le
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instMarkedKernelMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u => (a x.val, u x.val)))
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε)
    {n : ℕ} (X Y : Fin (n + 1) → M) (i j : Fin (n + 1)) (z₀ : Z)
    (hcenter : z₀ ∈ D.centers)
    (hxroot : a (X i) ∈ C.roots ∩ D.neighborhood z₀)
    (hyroot : a (Y j) ∈ C.roots ∩ D.neighborhood z₀)
    (hp : (u (X i), u (Y j)) ∈ C.window.region)
    (hread : X i = (P C.seedIndex).seed.curve
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a (X i)))
        (u (X i) - (P C.seedIndex).seed.level) ∧
      Y j = (P C.seedIndex).seed.curve
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a (Y j)))
        (u (Y j) - (P C.seedIndex).seed.level))
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker)
    (w : unitInterval) (hw : 0 < (w : ℝ))
    (hr : Tendsto (fun n : ℕ => scaledFloorRadius w n / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (w : ℝ)))
    (e : (P C.seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    (hbasis : ∀ v, e v =
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun v)
    (hcubeS : atlasSeedCoord (P C.seedIndex).seed e a (a (X i)) ∈
      unitCubeSet (Module.finrank ℝ (P C.seedIndex).seed.covector.ker))
    (hcubeT : atlasSeedCoord (P C.seedIndex).seed e a (a (Y j)) ∈
      unitCubeSet (Module.finrank ℝ (P C.seedIndex).seed.covector.ker)) :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ n in atTop,
        |finslerTileKinetic F X Y u
            (((n + 1 : ℕ) : ℝ) ^
              (2 / (Module.finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ))) i j -
          markedKineticKernel (scaledFloorRadius w n)
            (scaledMatrixKineticKernel
              (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) w
              (fun _ _ => C.matrix z₀ (u (X i), u (Y j))))
            (fun x : M => (atlasSeedCoord (P C.seedIndex).seed e a (a x), 0))
            (fun y : M => (atlasSeedCoord (P C.seedIndex).seed e a (a y), 0))
            (X i) (Y j)| ≤
        (2 * ε + η n) *
          markedKineticKernel (scaledFloorRadius w n)
            (scaledMatrixKineticKernel
              (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) w
              (fun _ _ => C.matrix z₀ (u (X i), u (Y j))))
            (fun x : M => (atlasSeedCoord (P C.seedIndex).seed e a (a x), 0))
            (fun y : M => (atlasSeedCoord (P C.seedIndex).seed e a (a y), 0))
            (X i) (Y j) := by
  classical
  let q : ℕ := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  have hq' : 0 < q := hq
  -- The marked kernel is the floor scale times the frozen physical cost.
  have hmarked : ∀ n : ℕ,
      markedKineticKernel (scaledFloorRadius w n)
        (scaledMatrixKineticKernel q w
          (fun _ _ => C.matrix z₀ (u (X i), u (Y j))))
        (fun x : M => (atlasSeedCoord (P C.seedIndex).seed e a (a x), 0))
        (fun y : M => (atlasSeedCoord (P C.seedIndex).seed e a (a y), 0))
        (X i) (Y j) =
      scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))) *
        C.frozenPhysicalCost z₀ (X i) (Y j) := by
    intro n
    rw [markedKineticKernel_scaledMatrixKineticKernel]
    rw [mDisplacement_atlasSeedCoord (P C.seedIndex).seed e a (a (X i)) (a (Y j))
      hcubeS hcubeT]
    dsimp only [OriginalPopulationCoefficientCore.frozenPhysicalCost]
    simp only [hbasis]
    ring
  -- The frozen physical cost is nonnegative.
  have hQ : 0 ≤ C.frozenPhysicalCost z₀ (X i) (Y j) :=
    frozenPhysicalCost_nonneg D hcenter hp
  -- The Taylor relative bound at the physical scale.
  have hphys : ∀ n : ℕ,
      |finslerTileKinetic F X Y u (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) *
            C.frozenPhysicalCost z₀ (X i) (Y j)| ≤
        2 * ε * ((((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) *
          C.frozenPhysicalCost z₀ (X i) (Y j)) := by
    intro n
    exact abs_finslerTileKinetic_sub_frozenPhysical_le (F := F) hF hcomplete hu ha hinj
      D hε X Y (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ _ => z₀) i j
      hcenter hxroot hyroot hp hread.1 hread.2
  -- The scale error sequence.
  obtain ⟨εs, hεs0, hεslim, hscale⟩ :=
    exists_floorScale_error (q := q) hq' hw hr
  let η : ℕ → ℝ := fun n =>
    if εs n < 1 then (εs n + 2 * ε * εs n) / (1 - εs n) else 0
  have hev : ∀ᶠ n in atTop, εs n < 1 :=
    hεslim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hη0 : ∀ n, 0 ≤ η n := by
    intro n
    dsimp only [η]
    split_ifs with hn
    · have hnum : 0 ≤ εs n + 2 * ε * εs n := by
        have := hεs0 n
        nlinarith
      exact div_nonneg hnum (by linarith)
    · exact le_rfl
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => (εs n + 2 * ε * εs n) / (1 - εs n))
        atTop (𝓝 0) := by
      have hnum : Tendsto (fun n : ℕ => εs n + 2 * ε * εs n) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n : ℕ => εs n * (2 * ε)) atTop (𝓝 0) := by
          have h2' := hεslim.mul_const (2 * ε)
          simpa using h2'
        have h := hεslim.add h2
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have hden : Tendsto (fun n : ℕ => 1 - εs n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub hεslim
      have h := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
      have hfun : ((fun n : ℕ => εs n + 2 * ε * εs n) / (fun n : ℕ => 1 - εs n)) =
          fun n : ℕ => (εs n + 2 * ε * εs n) / (1 - εs n) := rfl
      rw [hfun] at h
      simpa using h
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    dsimp only [η]
    rw [ite_eq_left hn]
  have hηbound : ∀ᶠ n in atTop,
      |finslerTileKinetic F X Y u
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
        markedKineticKernel (scaledFloorRadius w n)
          (scaledMatrixKineticKernel q w
            (fun _ _ => C.matrix z₀ (u (X i), u (Y j))))
          (fun x : M => (atlasSeedCoord (P C.seedIndex).seed e a (a x), 0))
          (fun y : M => (atlasSeedCoord (P C.seedIndex).seed e a (a y), 0))
          (X i) (Y j)| ≤
      (2 * ε + η n) *
        markedKineticKernel (scaledFloorRadius w n)
          (scaledMatrixKineticKernel q w
            (fun _ _ => C.matrix z₀ (u (X i), u (Y j))))
          (fun x : M => (atlasSeedCoord (P C.seedIndex).seed e a (a x), 0))
          (fun y : M => (atlasSeedCoord (P C.seedIndex).seed e a (a y), 0))
          (X i) (Y j) := by
    filter_upwards [hscale, hev] with n hscale_n hn
    have ht : 0 < (((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hs : 0 ≤ scaledFloorRadius w n ^ (2 / (q : ℝ)) *
        (w : ℝ) ^ (-(2 / (q : ℝ))) :=
      mul_nonneg (Real.rpow_nonneg (scaledFloorRadius_nonneg w n) _)
        (Real.rpow_nonneg (le_of_lt hw) _)
    have hscale' : |scaledFloorRadius w n ^ (2 / (q : ℝ)) *
          (w : ℝ) ^ (-(2 / (q : ℝ))) * C.frozenPhysicalCost z₀ (X i) (Y j) -
        (((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) *
          C.frozenPhysicalCost z₀ (X i) (Y j)| ≤
        εs n * ((((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) *
          C.frozenPhysicalCost z₀ (X i) (Y j)) := by
      have h := hscale_n (C.frozenPhysicalCost z₀ (X i) (Y j)) hQ
      calc |scaledFloorRadius w n ^ (2 / (q : ℝ)) *
            (w : ℝ) ^ (-(2 / (q : ℝ))) * C.frozenPhysicalCost z₀ (X i) (Y j) -
          (((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) *
            C.frozenPhysicalCost z₀ (X i) (Y j)|
          ≤ εs n * (((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) *
              C.frozenPhysicalCost z₀ (X i) (Y j) := h
        _ = εs n * ((((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)) *
              C.frozenPhysicalCost z₀ (X i) (Y j)) := by ring
    have hcomb := abs_sub_le_of_scale_error (phys := finslerTileKinetic F X Y u
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j)
      (Q := C.frozenPhysicalCost z₀ (X i) (Y j))
      (s := scaledFloorRadius w n ^ (2 / (q : ℝ)) * (w : ℝ) ^ (-(2 / (q : ℝ))))
      (t := (((n + 1 : ℕ) : ℝ)) ^ (2 / (q : ℝ)))
      hε (hεs0 n) hn hQ ht hs (hphys n) hscale'
    have heta : (εs n + 2 * ε * εs n) / (1 - εs n) = η n := by
      dsimp only [η]
      rw [ite_eq_left hn]
    rw [← hmarked n, heta] at hcomb
    exact hcomb
  exact ⟨η, hη0, hηlim, hηbound⟩

end OTSelector.Reconstruction
