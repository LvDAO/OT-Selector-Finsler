import OTSelector.Reconstruction.FinslerOriginalFrozenInputsActual
import OTSelector.Reconstruction.FinslerFrozenCoreDomination
import OTSelector.Reconstruction.FinslerOriginalFiniteDomination
import OTSelector.Reconstruction.FinslerOriginalFrozenDominationInstantiation
import OTSelector.Reconstruction.FinslerOriginalPropagationLipschitzBridge

/-!
# The frozen support bound from the per-edge finite-domination lane

This module closes the named frozen domination input FrozenSupportBound of the
actual hprob lane (FinslerOriginalFrozenInputsActual) by the per-edge
finite-domination analytic core, i.e. it proves the paper's single frozen support
bound rather than assuming it.

## The derivation

The frozen core cost family of the lane is the fractional assignment readout of
the simultaneous original frozen core matrix T.originalFrozenCoreMatrix, which is
the disjoint finite-tile splice of the per-tile masked frozen core matrices
maskedFrozenCost (T.edgeEvent ...) (frozenCoreMatrix (T.core c) eps reference_c).
The per-edge domination frozenCoreMatrix_le_slack_add_probeBound (the analytic
core behind frozenCore_div_le_finslerSupportedPressure_add) bounds every tile
entry on its retained edge event by

  frozenCoreMatrix entry <= scale * distanceSlackEdgeCost + t * carrierProbe
    + |t| * ||f||

using the Taylor relative expansion at the tile reference point, the tile
geometry, and the clipping/probe error bound. Since the tile edge events are
disjoint, summing these entrywise bounds over the tiles with the assignment
weights gives the splice entrywise bound
originalFrozenCoreMatrix_le_slack_add_probeBound; the finite-domination core
maskedFrozenCost_div_le_perturbedAssignmentValue_div_add_of_nonneg then sums
against the doubly stochastic/optimal assignment and produces exactly

  hprobFrozenCostFamily ... <= finslerSupportedPressure ... + |t| * ||f||.

Hence the frozen support bound is a theorem, with the per-edge lemma's exact
remaining inputs isolated explicitly: the tile geometric mask/readout
identification hgeom, the clipping correction bound hgh, and the optimal-plan
wiring hPopt; the physical metric identification hdist is the ambient/Finsler
distance bridge. No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
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

/-! ## 1. The entrywise splice bound from the per-tile analytic domination -/

/-- **The simultaneous frozen core matrix is dominated edgewise by the tilted
physical cost plus the probe constant.**

Every pair either lies in exactly one retained tile event, where the per-tile
analytic domination frozenCoreMatrix_le_slack_add_probeBound applies with the
tile's own core, Taylor cover and reference point (using hgeom and the clipping
correction hgh), or lies outside all retained events, where the splice is zero
and the right-hand side is nonnegative by the probe bound. -/
theorem originalFrozenCoreMatrix_le_slack_add_probeBound
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenSupportBoundMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {n : ℕ} {X Y : Fin n → M} {scale t : ℝ} (hk : 0 ≤ scale)
    (h : T.Index → Matrix (Fin n) (Fin n) ℝ)
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ)
    (hgeom : ∀ (c : T.Index) (i j : Fin n), (i, j) ∈ T.edgeEvent X Y c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) X Y i j)
    (hgh : ∀ (c : T.Index) (i j : Fin n), (i, j) ∈ T.edgeEvent X Y c →
      |carrierProbeMatrix μ ν K hK hμ hν X Y f i j - h c i j| ≤ (‖f‖₊ : ℝ)) :
    ∀ i j, T.originalFrozenCoreMatrix X Y scale t h i j ≤
      scale * distanceSlackEdgeCost X Y u i j +
        t * carrierProbeMatrix μ ν K hK hμ hν X Y f i j + |t| * (‖f‖₊ : ℝ) := by
  intro i j
  have hφL : LipschitzWith 1 u := lipschitzWith_ambient_of_finslerMetric hdist hu
  have hg_bound : ∀ i j,
      |carrierProbeMatrix μ ν K hK hμ hν X Y f i j| ≤ (‖f‖₊ : ℝ) := by
    intro i j
    have hnorm := f.norm_coe_le_norm
      (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))
    simpa only [carrierProbeMatrix, Real.norm_eq_abs, coe_nnnorm] using hnorm
  by_cases hex : ∃ c : T.Index, (i, j) ∈ T.edgeEvent X Y c
  · obtain ⟨c, hc⟩ := hex
    rw [T.originalFrozenCoreMatrix_on X Y scale t h hc]
    exact frozenCoreMatrix_le_slack_add_probeBound hF hcomplete hu ha hinj
      (D := T.cover c.1) hε hε1 hdist (φ := u) (fun x ↦ rfl) hφL
      (k := scale) (t := t) (probeError := (‖f‖₊ : ℝ)) (Bg := (‖f‖₊ : ℝ)) hk
      (z₀ := fun _ _ ↦ T.reference c) (h := h c)
      (g := carrierProbeMatrix μ ν K hK hμ hν X Y f)
      (Q := T.edgeEvent X Y c) (hgeom := hgeom c) (hgh := hgh c)
      hg_bound le_rfl i j hc
  · rw [T.originalFrozenCoreMatrix_outside X Y scale t h
      (fun c hc ↦ hex ⟨c, hc⟩)]
    have hcn : 0 ≤ scale * distanceSlackEdgeCost X Y u i j :=
      mul_nonneg hk (distanceSlackEdgeCost_nonneg X Y u hφL i j)
    have hlow : -(|t| * (‖f‖₊ : ℝ)) ≤
        t * carrierProbeMatrix μ ν K hK hμ hν X Y f i j := by
      have habs : |t * carrierProbeMatrix μ ν K hK hμ hν X Y f i j| ≤
          |t| * (‖f‖₊ : ℝ) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hg_bound i j) (abs_nonneg t)
      have h := neg_abs_le (t * carrierProbeMatrix μ ν K hK hμ hν X Y f i j)
      linarith
    linarith

/-! ## 2. The family-level frozen domination at a fixed scale -/

/-- **The frozen domination readout of the lane at a fixed scale.**

Applying the finite-domination masked core lemma to the splice with the optimal
assignment of the tilted physical cost turns the entrywise bound of Section 1
into the normalized frozen cost bound: the frozen family is at most the physical
Finsler supported pressure plus |t| times the probe norm. The pressure and the
frozen core are evaluated at the same scale, which is the paper's common-scale
convention. -/
theorem hprobFrozenCostFamily_le_finslerSupportedPressure_of_optimal
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenSupportBoundMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {n : ℕ} {X Y : Fin (n + 1) → M} {scale t : ℝ} (hk : 0 ≤ scale)
    (h : T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ)
    {Assign : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hPopt : OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ scale * distanceSlackEdgeCost X Y u i j)
        (carrierProbeMatrix μ ν K hK hμ hν X Y f) t) Assign)
    (hgeom : ∀ (c : T.Index) (i j : Fin (n + 1)), (i, j) ∈ T.edgeEvent X Y c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) X Y i j)
    (hgh : ∀ (c : T.Index) (i j : Fin (n + 1)), (i, j) ∈ T.edgeEvent X Y c →
      |carrierProbeMatrix μ ν K hK hμ hν X Y f i j - h c i j| ≤ (‖f‖₊ : ℝ)) :
    fractionalAssignmentCost (T.originalFrozenCoreMatrix X Y scale t h) Assign /
        ((n + 1 : ℕ) : ℝ) ≤
      finslerSupportedPressure F μ ν K hK hμ hν X Y u scale f t +
        |t| * (‖f‖₊ : ℝ) := by
  have hφL : LipschitzWith 1 u := lipschitzWith_ambient_of_finslerMetric hdist hu
  have hg_bound : ∀ i j,
      |carrierProbeMatrix μ ν K hK hμ hν X Y f i j| ≤ (‖f‖₊ : ℝ) := by
    intro i j
    have hnorm := f.norm_coe_le_norm
      (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))
    simpa only [carrierProbeMatrix, Real.norm_eq_abs, coe_nnnorm] using hnorm
  have hcn : ∀ i j, 0 ≤ scale * distanceSlackEdgeCost X Y u i j :=
    fun i j ↦ mul_nonneg hk (distanceSlackEdgeCost_nonneg X Y u hφL i j)
  have hdb : ∀ i j, (i, j) ∈ (Set.univ : Set (Fin (n + 1) × Fin (n + 1))) →
      T.originalFrozenCoreMatrix X Y scale t h i j ≤
        perturbedEdgeCost (fun i j ↦ scale * distanceSlackEdgeCost X Y u i j)
          (carrierProbeMatrix μ ν K hK hμ hν X Y f) t i j + |t| * (‖f‖₊ : ℝ) := by
    intro i j _
    simpa only [perturbedEdgeCost] using
      originalFrozenCoreMatrix_le_slack_add_probeBound (T := T)
        hF hcomplete hu ha hinj hε hε1 hdist hk h hK hμ hν f hgeom hgh i j
  have hdnn : ∀ i j, 0 ≤ T.originalFrozenCoreMatrix X Y scale t h i j :=
    T.originalFrozenCoreMatrix_nonneg X Y scale t h
  have hcore := OTSelector.maskedFrozenCost_div_le_perturbedAssignmentValue_div_add_of_nonneg
    (n := n + 1)
    (c := fun i j ↦ scale * distanceSlackEdgeCost X Y u i j)
    (g := carrierProbeMatrix μ ν K hK hμ hν X Y f)
    (d := T.originalFrozenCoreMatrix X Y scale t h)
    (P := Assign) (t := t) (B := |t| * (‖f‖₊ : ℝ)) (Q := Set.univ)
    (Nat.succ_pos n) hdnn hcn hg_bound rfl hPopt hdb
  have hmask : maskedFrozenCost Set.univ (T.originalFrozenCoreMatrix X Y scale t h) =
      T.originalFrozenCoreMatrix X Y scale t h := by
    funext i j
    simp [maskedFrozenCost]
  rw [hmask] at hcore
  have hfins : finslerSupportedPressure F μ ν K hK hμ hν X Y u scale f t =
      perturbedAssignmentValue (fun i j ↦ scale * distanceSlackEdgeCost X Y u i j)
        (fun i j ↦ f (supportProjection μ K hK hμ (X i),
          supportProjection ν K hK hν (Y j))) t / ((n + 1 : ℕ) : ℝ) := by
    rw [finslerSupportedPressure_eq_supportedDistancePressure]
    have hbody : @OTSelector.Pressure.supportedDistancePressure M F.metricSpace
        inferInstance μ ν K hK hμ hν (n + 1) X Y u scale f t =
        perturbedAssignmentValue (fun i j ↦ scale * @OTSelector.distanceSlackEdgeCost
          (n + 1) M
          (OTSelector.Geometry.ContinuousFinslerNorm.metricSpace (F := F)).toPseudoMetricSpace
          X Y u i j)
          (fun i j ↦ f (supportProjection μ K hK hμ (X i),
            supportProjection ν K hK hν (Y j))) t / ((n + 1 : ℕ) : ℝ) := rfl
    rw [hbody]
    rw [distanceSlackEdgeCost_finsler_eq (F := F) (hdist := hdist) (X := X) (Y := Y)
      (φ := u) (k := scale)]
  rw [hfins]
  exact hcore

/-! ## 3. The paper's single frozen support bound, proved -/

/-- **Almost-sure frozen domination at a fixed scale.**

This is the frozen domination field of the consumer lane with the frozen core and
the physical supported pressure at the same scale `scale n`. -/
theorem hprobFrozenCostFamily_le_finslerSupportedPressure_add
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenSupportBoundMetric : MetricSpace M := F.metricSpace
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
    (sample : ∀ n, Measure (Ω n)) (scale : ℕ → ℝ) (hscale0 : ∀ n, 0 ≤ scale n)
    (hPopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ scale n * distanceSlackEdgeCost (fun i ↦ X n i s)
          (fun i ↦ Y n i s) u i j)
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
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      hprobFrozenCostFamily (K := K) T X Y base Assign scale f t n s ≤
        finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s)
          (fun i ↦ Y n i s) u (scale n) f t + |t| * (‖f‖₊ : ℝ) := by
  intro f t n
  filter_upwards [hPopt f t n, hgeom n, hgh f t n] with s hPs hgs hhs
  exact hprobFrozenCostFamily_le_finslerSupportedPressure_of_optimal (T := T)
    hF hcomplete hu ha hinj hε hε1 hdist (hk := hscale0 n)
    (h := fun c ↦ normalizedProbe (K := K) base t n s c) hK hμ hν f hPs hgs hhs

/-- **The frozen support bound FrozenSupportBound is a theorem.**

The lane frozen cost family at the iid scale (the paper's common scale, which is
also the scale of the physical supported pressure, the only scale occurrence in
the consumer support bound) is almost surely at most the physical Finsler
supported pressure plus the probe constant. The only remaining inputs are exactly
the per-edge lemma's needs: the tile geometric mask and readout identification
hgeom, the clipping/probe correction hgh, and the optimal-plan wiring hPopt; the
ambient/Finsler distance identification is hdist. -/
theorem frozenSupportBound_of_geometricLane
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenSupportBoundMetric : MetricSpace M := F.metricSpace
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
      (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
        (2 / ((Module.finrank ℝ E : ℝ) - 1)))) sample := by
  intro f t n
  exact hprobFrozenCostFamily_le_finslerSupportedPressure_add (T := T)
    hF hcomplete hu ha hinj hε hε1 hdist hK hμ hν X Y base Assign sample
    (fun n ↦ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))))
    (fun n ↦ Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) _)
    hPopt hgeom hgh f t n

/-! ## 4. The per-tile integrability from the same lane bounds -/

/-- **The tile cost entries are bounded at every sample size.**  From the uniform
physical frozen cost bound and the normalized probe decay one gets the per-n
two-sided entry bound (1 - 2 eps) * scale n * B + |t| * Bp / (n + 1); no
uniform-in-n scale normalisation is required (the constant may depend on n). -/
theorem tileCostMatrix_abs_le_of_physProbeBounds
    {K : Set M} (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    {Bp B : ℝ} (hBp : 0 ≤ Bp) (hB : 0 ≤ B)
    (hε0 : 0 ≤ 1 - 2 * ε)
    (hscale0 : ∀ n, 0 ≤ scale n)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ B)
    (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)) :
    |T.tileCostMatrix f t X Y scale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j| ≤
      (1 - 2 * ε) * (scale n) * B + (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hprobe : t * normalizedProbe (K := K) base t n s c i j ≤
      (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by
    have h := normalizedProbe_abs_le (K := K) base hBp hbase t n s c i j
    calc t * normalizedProbe (K := K) base t n s c i j
        ≤ |t * normalizedProbe (K := K) base t n s c i j| := le_abs_self _
      _ = |t| * |normalizedProbe (K := K) base t n s c i j| := abs_mul _ _
      _ ≤ |t| * (Bp / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg t)
      _ = (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by ring
  have hC : (0 : ℝ) ≤ (1 - 2 * ε) * (scale n) * B + (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by
    have h1 : 0 ≤ (1 - 2 * ε) * (scale n) * B :=
      mul_nonneg (mul_nonneg hε0 (hscale0 n)) hB
    have h2 : 0 ≤ (|t| * Bp) / ((n + 1 : ℕ) : ℝ) :=
      div_nonneg (mul_nonneg (abs_nonneg t) hBp) hm.le
    linarith
  have hnonneg : 0 ≤ T.tileCostMatrix f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j :=
    T.tileCostMatrix_nonneg f t X Y scale _ n c s i j
  have hle : T.tileCostMatrix f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j ≤
      (1 - 2 * ε) * (scale n) * B + (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by
    show maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
      (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t
        (normalizedProbe (K := K) base t n s c)) i j ≤ _
    by_cases hmem : (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
    · rw [maskedFrozenCost_apply_of_mem hmem]
      have hexpr : max ((1 - 2 * ε) *
          ((scale n) * (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)) +
          t * normalizedProbe (K := K) base t n s c i j) 0 ≤
          (1 - 2 * ε) * (scale n) * B + (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by
        refine max_le ?_ hC
        have h1 : (1 - 2 * ε) *
              ((scale n) * (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)) ≤
              (1 - 2 * ε) * (scale n * B) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hphys n c s i j) (hscale0 n)) hε0
        have h2 : t * normalizedProbe (K := K) base t n s c i j ≤
            (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := hprobe
        calc (1 - 2 * ε) *
              ((scale n) * (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)) +
              t * normalizedProbe (K := K) base t n s c i j
            ≤ (1 - 2 * ε) * (scale n * B) + (|t| * Bp) / ((n + 1 : ℕ) : ℝ) :=
              add_le_add h1 h2
          _ = (1 - 2 * ε) * (scale n) * B + (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by ring
      exact hexpr
    · rw [maskedFrozenCost_apply_of_not_mem hmem]
      exact hC
  rw [abs_of_nonneg hnonneg]
  exact hle


/-! ## 5. The consumer lane without named frozen inputs -/

/-- **The actual hprob lane, with the frozen support bound derived.**

This is the same consumer statement as hprobFrozenInputs_actual_lane
(FinslerOriginalFrozenInputsActual), but the named frozen domination hypothesis
FrozenSupportBound is replaced by its exact remaining analytic content: the tile
geometric mask/readout identification hgeom, the clipping correction bound hgh,
the optimal-plan wiring hPopt, and the physical lane inputs (physical frozen cost
bound, base bound, doubly stochastic assignment, measurability). The frozen
support bound itself is derived, by frozenSupportBound_of_geometricLane, from the
per-edge finite-domination core; the tile integrability is derived from
integrable_tileFrozenCost_of_bounded with the per-n entry bounds. The ambient
metric identification hdist and the Finsler strong convexity regularity hF are
the analytic core inputs of the per-edge Taylor domination.

The frozen core scale and the physical supported pressure scale in the derived
support bound are both the paper's common iid scale
(n + 1) ^ (2 / (finrank - 1)). -/
theorem hprobFrozenInputs_actual_lane_of_geometricLane
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenSupportBoundMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (sample n)) (hYi : ∀ n, iIndepFun (Y n) (sample n))
    (hXlaw : ∀ n i, (sample n).map (X n i) =
      (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ n i, (sample n).map (Y n i) =
      (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (sample n))
    (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp Bphys : ℝ} (hBp : 0 ≤ Bp) (hBphys : 0 ≤ Bphys)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ Bphys)
    (hAssignDS : ∀ (n : ℕ) (s : Ω n),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hmeas : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s ↦
        T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (Assign n) (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) t c s))
    (hPopt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
          distanceSlackEdgeCost (fun i ↦ X n i s) (fun i ↦ Y n i s) u i j)
        (carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) f) t) (Assign n s))
    (hgeom : ∀ (n : ℕ), ∀ᵐ s ∂sample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (fun i ↦ X n i s) (fun i ↦ Y n i s) i j)
    (hgh : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      |carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) f i j -
        normalizedProbe (K := A ∪ B) base t n s c i j| ≤ (‖f‖₊ : ℝ))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hId : RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign
        (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
          (2 / ((Module.finrank ℝ E : ℝ) - 1))))) T.Index)
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) radius := by
  have hε0 : 0 ≤ 1 - 2 * ε := by linarith
  have hscale0 : ∀ n : ℕ, 0 ≤ (((n + 1 : ℕ) : ℝ) ^
      (2 / ((Module.finrank ℝ E : ℝ) - 1))) :=
    fun n ↦ Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) _
  have hcostbdd : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ C0 : ℝ, ∀ s : Ω n,
        |T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (Assign n) (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) t c s| ≤ C0 := by
    intro f t n c
    refine ⟨((n + 1 : ℕ) : ℝ) *
      ((1 - 2 * ε) * ((((n + 1 : ℕ) : ℝ) ^
        (2 / ((Module.finrank ℝ E : ℝ) - 1)))) * Bphys +
        (|t| * Bp) / ((n + 1 : ℕ) : ℝ)), fun s ↦ ?_⟩
    rw [tileFrozenCost_eq_fractionalAssignmentCost_tileCostMatrix (T := T) (K := A ∪ B)
      X Y base Assign (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
        (2 / ((Module.finrank ℝ E : ℝ) - 1)))) f t n c s]
    exact fractionalAssignmentCost_abs_le_of_feasible (hAssignDS n s)
      (fun i j ↦ tileCostMatrix_abs_le_of_physProbeBounds (T := T) (K := A ∪ B)
        f t X Y (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
          (2 / ((Module.finrank ℝ E : ℝ) - 1)))) hBp hBphys hε0 hscale0 hbase hphys
        n c s i j)
  have hint := integrable_tileFrozenCost_of_bounded (T := T) (K := A ∪ B) X Y base
    Assign (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
      (2 / ((Module.finrank ℝ E : ℝ) - 1)))) sample hmeas hcostbdd
  exact hprobFrozenInputs_actual_composed (T := T) (F := F) hdim ωM dens₀ dens₁
    hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY radius
    (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
      (2 / ((Module.finrank ℝ E : ℝ) - 1)))) base Assign
    hint (frozenSupportBound_of_geometricLane (T := T) (F := F) hF hcomplete hu ha
      hinj hε hε1 hdist (hA.union hB).measurableSet
      (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
      X Y base Assign sample hPopt hgeom hgh)
    g hId Ψ hread hcomplete hu

end OTSelector.Reconstruction
