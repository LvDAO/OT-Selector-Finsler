import OTSelector.Reconstruction.FinslerOriginalFrozenSupportBoundWiring
import OTSelector.Reconstruction.FinslerOriginalFrozenInputsActual
import OTSelector.Reconstruction.FinslerOriginalTaylorSlackRate
import OTSelector.Reconstruction.FinslerTileBlockFrozenComparison
import OTSelector.Reconstruction.AssignmentPressureLocalization

/-!
# The frozen-core scale identification: the tile scale is dominated by the iid scale

The derived frozen support bound `frozenSupportBound_of_geometricLane` of
FinslerOriginalFrozenSupportBoundWiring couples the lane frozen core cost family
and the physical supported pressure at the paper's common iid scale
`(n + 1) ^ (2 / (finrank - 1))`.  The endgame lower bundle
(FinslerOriginalEndgameLowerLaneInputsActual / FinslerOriginalEndgameLowerFieldActual)
instead writes its frozen domination field at the concrete tile scale
`tileScale n = 1 / (n + 1)`.  This module closes that presentation gap.

## What the scale identification is

The two lane presentations do not differ by a multiplicative factor: the frozen
core matrix of one tile is the clipped affine expression in the scale

  frozenCoreMatrix C eps z0 X Y k t h i j
    = max ((1 - 2 eps) * (k * C.frozenPhysicalCost ...) + t * h i j) 0,

so it is monotone, not linear, in k.  What holds is the pointwise frozen-cost
inequality: since the frozen physical cost is nonnegative and 0 <= 1 - 2 eps,

  0 <= k1 <= k2  =>  frozenCoreMatrix ... k1 ... <= frozenCoreMatrix ... k2 ...

Consequently at `tileScale n <= (n + 1) ^ (2 / (finrank - 1))` the whole
frozen core cost family at the tile scale is dominated by the family at the iid
scale (fractional assignment cost is monotone for a doubly stochastic
assignment).  The derived iid-scale support bound therefore yields the paper's
support bound at the endgame tile scale, so the endgame lane does not have to be
restated at the iid scale.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.Reconstruction.PopulationLocalPressureCore.TaylorTiles

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-! ## 1. The frozen core entry is monotone in the frozen scale -/

/-- **Scale monotonicity of one frozen core entry.**  The clipped frozen cost is
affine in the scale with nonnegative physical coefficient, hence monotone in the
scale. -/
theorem frozenCoreMatrix_le_of_scale_le
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {n : ℕ} {z₀ : Fin n → Fin n → (ℚ → M)} {X Y : Fin n → M} {t : ℝ}
    {k₁ k₂ : ℝ} (hk : k₁ ≤ k₂) (hε0 : 0 ≤ 1 - 2 * ε)
    {i j : Fin n}
    (hphys : 0 ≤ C.frozenPhysicalCost (z₀ i j) (X i) (Y j))
    (h : Matrix (Fin n) (Fin n) ℝ) :
    frozenCoreMatrix C ε z₀ X Y k₁ t h i j ≤
      frozenCoreMatrix C ε z₀ X Y k₂ t h i j := by
  rw [frozenCoreMatrix_apply, frozenCoreMatrix_apply]
  refine max_le (le_trans ?_ (le_max_left _ _)) (le_max_right _ _)
  have h1 : k₁ * C.frozenPhysicalCost (z₀ i j) (X i) (Y j) ≤
      k₂ * C.frozenPhysicalCost (z₀ i j) (X i) (Y j) :=
    mul_le_mul_of_nonneg_right hk hphys
  have h2 : (1 - 2 * ε) *
        (k₁ * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) ≤
      (1 - 2 * ε) *
        (k₂ * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) :=
    mul_le_mul_of_nonneg_left h1 hε0
  linarith [h2]

/-! ## 2. The simultaneous frozen core matrix is monotone in the frozen scale -/

/-- **Scale monotonicity of the simultaneous frozen core matrix.**  The
finite-tile splice preserves the entrywise scale monotonicity of the frozen core
matrix on every retained tile edge event. -/
theorem originalFrozenCoreMatrix_le_of_scale_le
    {n : ℕ} {X Y : Fin n → M} {t : ℝ} {k₁ k₂ : ℝ} (hk : k₁ ≤ k₂)
    (hε0 : 0 ≤ 1 - 2 * ε)
    (hphys : ∀ (c : T.Index) (i j : Fin n),
      (i, j) ∈ T.edgeEvent X Y c →
      0 ≤ (T.core c).frozenPhysicalCost (T.reference c) (X i) (Y j))
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ) :
    ∀ i j, T.originalFrozenCoreMatrix X Y k₁ t h i j ≤
      T.originalFrozenCoreMatrix X Y k₂ t h i j := by
  intro i j
  by_cases hex : ∃ c : T.Index, (i, j) ∈ T.edgeEvent X Y c
  · obtain ⟨c, hc⟩ := hex
    rw [T.originalFrozenCoreMatrix_on X Y k₁ t h hc,
      T.originalFrozenCoreMatrix_on X Y k₂ t h hc]
    exact frozenCoreMatrix_le_of_scale_le (C := T.core c)
      (z₀ := fun _ _ ↦ T.reference c) (X := X) (Y := Y) (t := t)
      (k₁ := k₁) (k₂ := k₂) (i := i) (j := j) (h := h c) hk hε0
      (hphys c i j hc)
  · rw [T.originalFrozenCoreMatrix_outside X Y k₁ t h (fun c hc ↦ hex ⟨c, hc⟩),
      T.originalFrozenCoreMatrix_outside X Y k₂ t h (fun c hc ↦ hex ⟨c, hc⟩)]

/-! ## 3. The frozen cost family is monotone in the frozen scale -/

/-- **Scale monotonicity of the lane frozen cost family.**  A doubly stochastic
assignment has nonnegative entries, so the fractional assignment cost preserves
the entrywise scale monotonicity of the simultaneous frozen core matrix. -/
theorem hprobFrozenCostFamily_le_of_scale_le (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {scale₁ scale₂ : ℕ → ℝ} (hε0 : 0 ≤ 1 - 2 * ε)
    (hle : ∀ n, scale₁ n ≤ scale₂ n)
    (n : ℕ) (s : Ω n)
    (hAssignDS : Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hphys : ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      0 ≤ (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    hprobFrozenCostFamily (K := K) T X Y base Assign scale₁ f t n s ≤
      hprobFrozenCostFamily (K := K) T X Y base Assign scale₂ f t n s := by
  unfold hprobFrozenCostFamily
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
  apply fractionalAssignmentCost_mono_of_feasible hAssignDS
  intro i j
  by_cases hex : ∃ c : T.Index,
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · obtain ⟨c, hc⟩ := hex
    rw [T.originalFrozenCoreMatrix_on (fun i ↦ X n i s) (fun i ↦ Y n i s)
        (scale₁ n) t (fun c' ↦ normalizedProbe (K := K) base t n s c') hc,
      T.originalFrozenCoreMatrix_on (fun i ↦ X n i s) (fun i ↦ Y n i s)
        (scale₂ n) t (fun c' ↦ normalizedProbe (K := K) base t n s c') hc]
    exact frozenCoreMatrix_le_of_scale_le (C := T.core c)
      (z₀ := fun _ _ ↦ T.reference c) (X := fun i ↦ X n i s)
      (Y := fun j ↦ Y n j s) (t := t) (k₁ := scale₁ n) (k₂ := scale₂ n)
      (h := (fun c' ↦ normalizedProbe (K := K) base t n s c') c)
      (hle n) hε0 (hphys c i j hc)
  · rw [T.originalFrozenCoreMatrix_outside (fun i ↦ X n i s) (fun i ↦ Y n i s)
        (scale₁ n) t (fun c' ↦ normalizedProbe (K := K) base t n s c')
        (fun c hc ↦ hex ⟨c, hc⟩),
      T.originalFrozenCoreMatrix_outside (fun i ↦ X n i s) (fun i ↦ Y n i s)
        (scale₂ n) t (fun c' ↦ normalizedProbe (K := K) base t n s c')
        (fun c hc ↦ hex ⟨c, hc⟩)]

/-! ## 4. The tile scale is dominated by the iid scale -/

/-- **The iid scale dominates the tile scale.**  `1/(n+1) <= 1` and
`(n+1)^e >= 1` for every nonnegative exponent e. -/
theorem tileScale_le_iidScale (hdim : 1 ≤ Module.finrank ℝ E) (n : ℕ) :
    tileScale n ≤
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) := by
  have h1 : tileScale n ≤ 1 := tileScale_le_one n
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have h : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    exact_mod_cast h
  have hexp : 0 ≤ 2 / ((Module.finrank ℝ E : ℝ) - 1) := by
    have hfin : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    have hpos : 0 ≤ (Module.finrank ℝ E : ℝ) - 1 := by linarith
    exact div_nonneg (by norm_num) hpos
  have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^
      (2 / ((Module.finrank ℝ E : ℝ) - 1)) := Real.one_le_rpow hbase hexp
  linarith

/-! ## 5. The endgame lane's tile-scale frozen domination from the iid-scale bound -/

/-- **The tile-scale support bound is a theorem.**  The derived iid-scale support
bound composes with the scale monotonicity of the frozen cost family: at the
endgame tile scale the frozen core cost family is at most the iid-scale frozen
cost family, hence at most the physical supported pressure plus the probe
constant. -/
theorem frozenSupportBound_tileScale_of_geometricLane
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenScaleIdentificationMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (sample : ∀ n, Measure (Ω n))
    (hdim : 6 ≤ Module.finrank ℝ E)
    (hAssignDS : ∀ (n : ℕ) (s : Ω n),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hPopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
          distanceSlackEdgeCost (fun i ↦ X n i s) (fun i ↦ Y n i s) u i j)
        (carrierProbeMatrix μ ν K hK hμ hν (fun i ↦ X n i s)
          (fun i ↦ Y n i s) f) t) (Assign n s))
    (hgeom : ∀ (n : ℕ), ∀ᵐ s ∂sample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (fun i ↦ X n i s) (fun i ↦ Y n i s) i j)
    (hgh : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      |carrierProbeMatrix μ ν K hK hμ hν (fun i ↦ X n i s)
          (fun i ↦ Y n i s) f i j - normalizedProbe (K := K) base t n s c i j| ≤
        (‖f‖₊ : ℝ)) :
    FrozenSupportBound (T := T) (F := F) hK hμ hν u X Y base Assign
      tileScale sample := by
  have hdim1 : 1 ≤ Module.finrank ℝ E := le_trans (by norm_num) hdim
  have hε0 : 0 ≤ 1 - 2 * ε := by linarith
  have hiid := frozenSupportBound_of_geometricLane (T := T) (F := F) hF hcomplete
    hu ha hinj hε hε1 hdist hK hμ hν X Y base Assign sample hPopt hgeom hgh
  intro f t n
  filter_upwards [hiid f t n, hgeom n] with s hbound hgs
  have hphysN : ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      0 ≤ (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) := by
    intro c i j hmem
    exact frozenPhysicalCost_nonneg (T.cover c.1) (hgs c i j hmem).1
      (hgs c i j hmem).2.2.2.1
  exact le_trans
    (hprobFrozenCostFamily_le_of_scale_le (K := K) T X Y base Assign hε0
      (fun m ↦ tileScale_le_iidScale hdim1 m) n s (hAssignDS n s) hphysN f t)
    hbound

/-! ## 6. The endgame lane's two frozen inputs, derived at the tile scale -/

/-- **The endgame lane's frozen integrability and frozen domination, derived.**

The pair is exactly the one consumed by the reduced endgame bundle
`endgameLowerFields_actual_lane_reduced` (FinslerOriginalEndgameLowerLaneInputsActual)
at the concrete scene-cloud lane: the frozen cost family at `tileScale` is
integrable, and it is almost surely dominated by the physical supported pressure
at the iid scale plus the probe constant.  The tile integrability is derived from
the per-tile entry bounds (`tileCostMatrix_abs_le_of_physProbeBounds`) and the
frozen domination from the per-edge finite-domination lane via
`frozenSupportBound_tileScale_of_geometricLane`; no named frozen input
remains, only the per-edge lane data hgeom/hgh/hPopt, the clipping base bound
hbase, the physical frozen bound hphys, the doubly stochastic assignment, the
measurability hmeas and the analytic core hF/hcomplete/hu/ha/hinj/hdist. -/
theorem hprobFrozenInputs_tileScale_of_geometricLane
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenScaleIdentificationMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (sample n)]
    (hdim : 6 ≤ Module.finrank ℝ E)
    {Bp Bphys : ℝ} (hBp : 0 ≤ Bp) (hBphys : 0 ≤ Bphys)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ Bphys)
    (hAssignDS : ∀ (n : ℕ) (s : Ω n),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hmeas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s ↦
        T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := K) base t n s' c')
          (Assign n) (tileScale n) t c s))
    (hPopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
          distanceSlackEdgeCost (fun i ↦ X n i s) (fun i ↦ Y n i s) u i j)
        (carrierProbeMatrix μ ν K hK hμ hν (fun i ↦ X n i s)
          (fun i ↦ Y n i s) f) t) (Assign n s))
    (hgeom : ∀ (n : ℕ), ∀ᵐ s ∂sample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (fun i ↦ X n i s) (fun i ↦ Y n i s) i j)
    (hgh : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      |carrierProbeMatrix μ ν K hK hμ hν (fun i ↦ X n i s)
          (fun i ↦ Y n i s) f i j - normalizedProbe (K := K) base t n s c i j| ≤
        (‖f‖₊ : ℝ)) :
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
        Integrable (hprobFrozenCostFamily (K := K) T X Y base Assign tileScale f t n)
          (sample n)) ∧
      FrozenSupportBound (T := T) (F := F) hK hμ hν u X Y base Assign
        tileScale sample := by
  have hε0 : 0 ≤ 1 - 2 * ε := by linarith
  have hcostbdd : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ C0 : ℝ, ∀ s : Ω n,
        |T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := K) base t n s' c')
          (Assign n) (tileScale n) t c s| ≤ C0 := by
    intro f t n c
    refine ⟨((n + 1 : ℕ) : ℝ) *
      ((1 - 2 * ε) * (tileScale n) * Bphys +
        (|t| * Bp) / ((n + 1 : ℕ) : ℝ)), fun s ↦ ?_⟩
    rw [tileFrozenCost_eq_fractionalAssignmentCost_tileCostMatrix (T := T) (K := K)
      X Y base Assign tileScale f t n c s]
    exact fractionalAssignmentCost_abs_le_of_feasible (hAssignDS n s)
      (fun i j ↦ tileCostMatrix_abs_le_of_physProbeBounds (T := T) (K := K)
        f t X Y tileScale hBp hBphys hε0 (fun n ↦ (tileScale_pos n).le)
        hbase hphys n c s i j)
  have hintTile := integrable_tileFrozenCost_of_bounded (T := T) (K := K) X Y base
    Assign tileScale sample hmeas hcostbdd
  have hintOpaque := integrable_tileFrozenCostOpaque_of_tileFrozenCost (T := T)
    (K := K) X Y base Assign tileScale sample hintTile
  have hsupp := frozenSupportBound_tileScale_of_geometricLane (T := T) (F := F)
    hF hcomplete hu ha hinj hε hε1 hdist hK hμ hν X Y base Assign sample hdim
    hAssignDS hPopt hgeom hgh
  exact hprobFrozenInputs_familyLevel_actual T hK hμ hν u X Y base Assign
    tileScale sample hintOpaque hsupp

end OTSelector.Reconstruction