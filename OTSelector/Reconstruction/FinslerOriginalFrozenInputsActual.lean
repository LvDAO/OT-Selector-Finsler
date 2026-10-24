import OTSelector.Reconstruction.FinslerOriginalFrozenTransportInstantiation
import OTSelector.Reconstruction.FinslerOriginalTileEntryBound
import OTSelector.Reconstruction.FinslerOriginalTileMeanConvergence
import OTSelector.Reconstruction.AssignmentPressureLocalization
import OTSelector.Reconstruction.FinslerOriginalTileClippingConcrete

/-!
# The actual-lane frozen inputs: boundedness, support bound, derived integrability

This module eliminates the remaining frozen-lane inputs of the composed theorem
hprobFrozenInputs_actual_composed (FinslerOriginalFrozenTransportInstantiation).

## The tile boundedness lemmas that supply the integrability

The per-tile frozen integrability lane is DERIVED here, not assumed.  The chain is
the repo tile boundedness lane:

* tileFrozenCost is definitionally the fractional readout of the masked tile cost
  matrix (tileFrozenCost_eq_fractionalAssignmentCost_tileCostMatrix);
* the repo lemma tileCostMatrix_nonneg (FinslerOriginalTileEntryBound) gives entry
  nonnegativity, and tileCostMatrix_le_of_scaleBound (same file) gives the entry
  upper bound C0/(n+1) with C0 = (1 - 2 eps) * S * B + P from the uniform physical
  cost bound B, the probe normalization P and the scale normalization S;
  combining them gives tileCostMatrix_abs_le_of_scaleBound;
* the repo lemma fractionalAssignmentCost_abs_le_of_feasible
  (FinslerOriginalTileAssignmentPressureLocalization) bounds the fractional readout
  by (n+1) * (C0/(n+1)) = C0 for every doubly stochastic assignment, giving
  tileFrozenCost_abs_le_of_doublyStochastic;
* finally the Mathlib boundedness-to-integrability lemma Integrable.of_bound
  (Mathlib.MeasureTheory.Integral.IntegrableOn) gives the per-tile integrability
  from tile-frozen-cost measurability plus the uniform bound C0.

So the bound lemma that supplies the per-tile integrability is
tileCostMatrix_le_of_scaleBound (with tileCostMatrix_nonneg) and the algebraic
transfer is fractionalAssignmentCost_abs_le_of_feasible.

## The single paper frozen support bound

FrozenSupportBound is the paper's single frozen support bound: the frozen cost
family is at most the Finsler supported pressure at the iid scale plus the probe
constant |t| times the probe norm.  The theorem
frozenSupportBound_iff_consumerFrozenDomination proves that this is EXACTLY the
consumer frozen domination field (both sides are definitionally the same
proposition: no weakening and no strengthening).

## The final theorem

hprobFrozenInputs_actual_lane produces FinalProbLowerData for the actual lane with
the only frozen-lane inputs being the paper support bound (FrozenSupportBound) and
the lane data that the tile boundedness lane needs (tile-frozen-cost
measurability, the uniform physical cost bound, the probe base sup bound, the
scale normalization, and the feasibility of the lane assignment).  The per-tile
integrability itself is derived, and the previous module's
integrable_tileFrozenCostOpaque_of_tileFrozenCost converts it to the wrapper form.

No sorry, admit or added axiom occurs.
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

/-! ## 1. The tile frozen cost is the fractional readout of the tile cost matrix -/

/-- **Definitional identification.**  The concrete named lane per-tile frozen cost
is the fractional assignment readout of the repo tile cost matrix of
FinslerOriginalTileMeanConvergence at the same probe family and assignment. -/
theorem tileFrozenCost_eq_fractionalAssignmentCost_tileCostMatrix (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n) :
    T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
        (fun s' c' ↦ normalizedProbe (K := K) base t n s' c') (Assign n) (scale n) t c s =
      fractionalAssignmentCost
        (T.tileCostMatrix f t X Y scale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s)
        (Assign n s) :=
  rfl

/-! ## 2. The tile entry bound and the tile frozen cost bound -/

/-- **Two-sided tile entry bound from the scale normalization.**  Combining the
repo entry nonnegativity (tileCostMatrix_nonneg) with the repo entry upper bound
(tileCostMatrix_le_of_scaleBound) gives the absolute entry bound C0/(n+1). -/
theorem tileCostMatrix_abs_le_of_scaleBound (K : Set M)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (S Bphys P : ℝ) (hBphys : 0 ≤ Bphys)
    (hε0 : 0 ≤ 1 - 2 * ε)
    (hC₀ : 0 ≤ (1 - 2 * ε) * S * Bphys + P)
    (hscale0 : ∀ n, 0 ≤ scale n)
    (hscale : ∀ n, scale n ≤ S / ((n + 1 : ℕ) : ℝ))
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ Bphys)
    (hprobeB : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      t * hprobe f t n s c i j ≤ P / ((n + 1 : ℕ) : ℝ)) :
    ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      |T.tileCostMatrix f t X Y scale hprobe n c s i j| ≤
        ((1 - 2 * ε) * S * Bphys + P) / ((n + 1 : ℕ) : ℝ) := by
  intro n c s i j
  have hnonneg := T.tileCostMatrix_nonneg (ε := ε) f t X Y scale hprobe n c s i j
  have hle := T.tileCostMatrix_le_of_scaleBound (ε := ε) f t X Y scale hprobe S Bphys P
    hBphys hε0 hC₀ hscale0 hscale hphys hprobeB n c s i j
  rwa [abs_of_nonneg hnonneg]

/-- **The tile frozen cost is bounded by the frozen constant C0.**  For a doubly
stochastic lane assignment, the repo feasibility bound
fractionalAssignmentCost_abs_le_of_feasible turns the entry bound C0/(n+1) into the
uniform bound C0. -/
theorem tileFrozenCost_abs_le_of_doublyStochastic (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
    {C0 : ℝ}
    (hAssignDS : Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hEntry : ∀ i j : Fin (n + 1),
      |T.tileCostMatrix f t X Y scale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j| ≤
        C0 / ((n + 1 : ℕ) : ℝ)) :
    |T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
        (fun s' c' ↦ normalizedProbe (K := K) base t n s' c') (Assign n) (scale n) t c s| ≤
      C0 := by
  have hfeas := fractionalAssignmentCost_abs_le_of_feasible
    (n := n + 1) (W := Assign n s) hAssignDS
    (g := T.tileCostMatrix f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s)
    (G := C0 / ((n + 1 : ℕ) : ℝ)) hEntry
  rw [tileFrozenCost_eq_fractionalAssignmentCost_tileCostMatrix]
  have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  refine hfeas.trans (le_of_eq ?_)
  field_simp

/-- **Per-tile frozen integrability from the tile boundedness lane.**  A
measurable tile frozen cost with the uniform bound C0 is integrable against every
finite sample measure (Integrable.of_bound). -/
theorem integrable_tileFrozenCost_of_bounded (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (sample : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (sample n)]
    (hmeas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s ↦
        T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := K) base t n s' c') (Assign n) (scale n) t c s))
    (hbdd : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ C0 : ℝ, ∀ s : Ω n, |T.tileFrozenCost (fun s' i ↦ X n i s')
        (fun s' i ↦ Y n i s') (fun s' c' ↦ normalizedProbe (K := K) base t n s' c')
        (Assign n) (scale n) t c s| ≤ C0) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ T.tileFrozenCost (fun s' i ↦ X n i s')
        (fun s' i ↦ Y n i s') (fun s' c' ↦ normalizedProbe (K := K) base t n s' c')
        (Assign n) (scale n) t c s) (sample n) := by
  intro f t n c
  obtain ⟨C0, hC0⟩ := hbdd f t n c
  exact Integrable.of_bound (hmeas f t n c).aestronglyMeasurable C0
    (Filter.Eventually.of_forall fun s ↦ by
      simpa only [Real.norm_eq_abs] using hC0 s)

/-! ## 3. The paper's single frozen support bound -/

/-- **The paper's single frozen support bound.**  The lane frozen cost family is
at most the physical Finsler supported pressure plus the probe constant
|t| times the probe norm. -/
def FrozenSupportBound
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (φ : M → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (sample : ∀ n, Measure (Ω n)) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
    hprobFrozenCostFamily (K := K) T X Y base Assign scale f t n s ≤
      finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s)
        φ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
        |t| * (‖f‖₊ : ℝ)

/-- **No weakening, no strengthening.**  The paper support bound is definitionally
the consumer frozen domination field used by hprobFrozenInputs_actual_composed and
by the hprob probability lower bound. -/
theorem frozenSupportBound_iff_consumerFrozenDomination
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (φ : M → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (sample : ∀ n, Measure (Ω n)) :
    FrozenSupportBound (T := T) (F := F) hK hμ hν φ X Y base Assign scale sample ↔
      (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
        hprobFrozenCostFamily (K := K) T X Y base Assign scale f t n s ≤
          finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s)
            (fun i ↦ Y n i s) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
            |t| * (‖f‖₊ : ℝ)) :=
  Iff.rfl

/-! ## 4. The final theorem: FinalProbLowerData with derived integrability -/

/-- **The actual-lane final theorem.**

The only frozen-lane inputs are the paper support bound hsupp and the tile
boundedness lane data needed to DERIVE the per-tile frozen integrability:

* hmeas: measurability of the per-tile frozen cost in the sample;
* hphys: the uniform physical frozen cost bound B (supplied in the concrete lane
  by frozenPhysicalCost_tileBound_uniform / exists_frozenCost_bound_on_mask);
* hbase: the probe base sup bound Bp, giving the probe normalization
  |normalizedProbe| <= Bp/(n+1) through normalizedProbe_abs_le;
* hscale0, hscale: the scale normalization 0 <= scale n <= S/(n+1);
* hAssignDS: the lane assignment is doubly stochastic (uniformTilePlan is).

The per-tile integrability is derived (Sections 1-2) and fed to the composed
consumer theorem, which produces FinalProbLowerData. -/
theorem hprobFrozenInputs_actual_lane
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
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp Sscale Bphys : ℝ} (hBp : 0 ≤ Bp) (hS : 0 ≤ Sscale) (hBphys : 0 ≤ Bphys)
    (hε0 : 0 ≤ 1 - 2 * ε)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hscale0 : ∀ n, 0 ≤ scale n)
    (hscale : ∀ n, scale n ≤ Sscale / ((n + 1 : ℕ) : ℝ))
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ Bphys)
    (hAssignDS : ∀ (n : ℕ) (s : Ω n),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hmeas : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s ↦
        T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (Assign n) (scale n) t c s))
    (hsupp : FrozenSupportBound (T := T) (F := F)
      (hA.union hB).measurableSet
      (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
      u X Y base Assign scale sample)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hId : RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale) T.Index)
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenInputsActualMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) radius := by
  have hprobeb : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Ω n) (i j : Fin (n + 1)),
      t * normalizedProbe (K := A ∪ B) base t n s c i j ≤
        (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by
    intro f t n c s i j
    have h := normalizedProbe_abs_le (K := A ∪ B) base hBp hbase t n s c i j
    calc t * normalizedProbe (K := A ∪ B) base t n s c i j
        ≤ |t * normalizedProbe (K := A ∪ B) base t n s c i j| := le_abs_self _
      _ = |t| * |normalizedProbe (K := A ∪ B) base t n s c i j| := abs_mul _ _
      _ ≤ |t| * (Bp / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg t)
      _ = (|t| * Bp) / ((n + 1 : ℕ) : ℝ) := by ring
  have hentry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Ω n) (i j : Fin (n + 1)),
      |T.tileCostMatrix f t X Y scale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j| ≤
        ((1 - 2 * ε) * Sscale * Bphys + |t| * Bp) / ((n + 1 : ℕ) : ℝ) := by
    intro f t n c s i j
    have hC₀ : 0 ≤ (1 - 2 * ε) * Sscale * Bphys + |t| * Bp := by positivity
    exact tileCostMatrix_abs_le_of_scaleBound (T := T) (K := A ∪ B) f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      Sscale Bphys (|t| * Bp) hBphys hε0 hC₀ hscale0 hscale hphys (hprobeb f t) n c s i j
  have hcostbdd : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ C0 : ℝ, ∀ s : Ω n,
        |T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (Assign n) (scale n) t c s| ≤ C0 := by
    intro f t n c
    exact ⟨(1 - 2 * ε) * Sscale * Bphys + |t| * Bp,
      fun s ↦ tileFrozenCost_abs_le_of_doublyStochastic (T := T) (K := A ∪ B)
        X Y base Assign scale f t n c s (hAssignDS n s) (hentry f t n c s)⟩
  have hint := integrable_tileFrozenCost_of_bounded (T := T) (K := A ∪ B) X Y base
    Assign scale sample hmeas hcostbdd
  exact hprobFrozenInputs_actual_composed (T := T) (F := F) hdim ωM dens₀ dens₁
    hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY radius scale base Assign
    hint hsupp g hId Ψ hread hcomplete hu

end OTSelector.Reconstruction