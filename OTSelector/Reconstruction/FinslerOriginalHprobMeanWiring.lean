import OTSelector.Reconstruction.FinslerOriginalHprobWiring
import OTSelector.Reconstruction.FinslerOriginalPressureLowerAssembly

/-!
# Mean lower wiring and masked frozen-core transport for the hprob lane

This module completes the hprob lane wiring of FinslerOriginalHprobWiring on two
named fronts.

**Mean lane.**  The expectation-level lower mean bound, the hfrozen_mean input of
the paper's iid lower localization
physical_finsler_probability_lower_of_frozen_mean_lower, is produced from the
repo's named rooted tile mean lane: the per-tile Campbell mean identification
RootedTileCampbellMeanIdentification (itself furnished from the Palm sample law
fields by rootedTileCampbellMeanIdentification_of_palmSampleLaw, and from the
named per-tile mean convergence lane by
rootedTileMeanCampbellValues_of_tile_mean_convergence) gives, through
frozenMeanLower_of_rootedTileIdentification, the consumer's mean bound at the
probe-shifted readout fun f t => Psi f t - |t| ||f||.

**Transport lane.**  The hprob lane's named frozen core cost family, built from
T.originalFrozenCoreMatrix and normalizedProbe, is exactly the finite tile sum
of the finite-domination masked frozen core costs
maskedFrozenCost (T.edgeEvent ...) (frozenCoreMatrix (T.core k) eps ...): each
tile term is the object that the frozen-core finite domination lane
(FinslerFrozenCoreDomination, FinslerOriginalPropagationLipschitzBridge)
dominates.  Hence every frozen input of the hprob lane is a sum of per-tile
finite-domination masked frozen core objects.

Finally finalProbLowerData_of_rootedTileMeanIdentification assembles the
assembly's hprob clause verbatim for the actual lane, with the mean input
produced from the named tile mean lane and the two frozen inputs (domination and
integrability of the frozen core cost family) as named paper inputs whose
per-tile content is the finite-domination lane's masked frozen core family.

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

/-! ## 1. The mean lower input from the named rooted tile mean lane -/

/-- **The consumer's mean lower input from the named rooted tile Campbell mean
identification.**

This is the hfrozen_mean binder of the paper's iid lower localization
physical_finsler_probability_lower_of_frozen_mean_lower, verbatim, at the
probe-shifted readout fun f t => Psi f t - |t| ||f||: it is produced from the
named per-tile Campbell mean identification RootedTileCampbellMeanIdentification
and the named readout identification frozenPressureLower = Psi. -/
theorem hfrozenMean_of_rootedTileIdentification
    {K : Set M}
    (sample : ∀ n, Measure (Ω n))
    (frozenCost : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hId : RootedTileCampbellMeanIdentification P a κ lambda g q sample frozenCost ιt)
    {Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ}
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      (Ψ f t - |t| * (‖f‖₊ : ℝ)) + |t| * (‖f‖₊ : ℝ) - ε ≤
        ∫ s, frozenCost f t n s ∂sample n := by
  intro f t ε hε
  filter_upwards [frozenMeanLower_of_rootedTileIdentification (Seed := P) (a := a)
    (κ := κ) (lambda := lambda) (g := g) (P := sample) (frozenCost := frozenCost)
    (q := q) hId f t (ε / 2) (by positivity)] with n hn
  have hcamp : campbellAveragedFrozenCost P a κ lambda (g f t) q =
      frozenPressureLower P a κ lambda g q f t := rfl
  rw [hcamp, hread] at hn
  linarith

/-! ## 2. The hprob frozen core cost family and its masked frozen-core transport -/

/-- **The hprob lane's frozen core cost family.**

The frozen core cost of the original empirical optimal face at scale scale,
written as in FinslerOriginalHprobWiring: the fractional assignment cost of the
simultaneous original frozen core matrix (built from normalizedProbe), normalized
by the sample size n + 1. -/
noncomputable def hprobFrozenCostFamily (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) :
    ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ :=
  fun f t n s =>
    fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t
        (fun c' ↦ normalizedProbe (K := K) base t n s c')) (Assign n s) /
      ((n + 1 : ℕ) : ℝ)

/-- **Transport to the finite-domination masked frozen core objects.**

The normalized frozen core cost of the hprob lane is the finite sum, over the
retained Taylor tiles, of the masked frozen core costs
maskedFrozenCost (T.edgeEvent ...) (frozenCoreMatrix (T.core k) eps reference_k)
-- exactly the masked frozen core matrices of the finite-domination lane, each
with the tile's core, reference point and probe matrix, integrated against the
same fractional assignment. -/
theorem hprobFrozenCost_eq_maskedFrozenCoreSum
    {n : ℕ} {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (X Y : Ω₀ → Fin n → M)
    (h : Ω₀ → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (Assign : Ω₀ → Matrix (Fin n) (Fin n) ℝ) (scale t : ℝ) (s : Ω₀) :
    fractionalAssignmentCost (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s))
        (Assign s) / (n : ℝ) =
      ∑ k : T.Index,
        fractionalAssignmentCost (maskedFrozenCost (T.edgeEvent (X s) (Y s) k)
          (frozenCoreMatrix (T.core k) ε (fun _ _ ↦ T.reference k) (X s) (Y s)
            scale t (h s k))) (Assign s) / (n : ℝ) := by
  calc fractionalAssignmentCost (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s))
        (Assign s) / (n : ℝ)
      = (∑ k : T.Index,
          fractionalAssignmentCost (maskedFrozenCost (T.edgeEvent (X s) (Y s) k)
            (frozenCoreMatrix (T.core k) ε (fun _ _ ↦ T.reference k) (X s) (Y s)
              scale t (h s k))) (Assign s)) / (n : ℝ) := by
        rw [T.fractionalAssignmentCost_originalFrozenCoreMatrix_eq_sum]
    _ = ∑ k : T.Index,
        fractionalAssignmentCost (maskedFrozenCost (T.edgeEvent (X s) (Y s) k)
          (frozenCoreMatrix (T.core k) ε (fun _ _ ↦ T.reference k) (X s) (Y s)
            scale t (h s k))) (Assign s) / (n : ℝ) := by
        rw [Finset.sum_div]

/-! ## 3. The hprob clause for the actual lane -/

/-- **The assembly's hprob clause for the actual lane.**

For the actual physical population data, the original iid arrays, the fractional
assignment Assign, the sample scale and a pinned frozen probe, the lower
probability field holds at the probe-shifted scene readout
fun f t => Psi f t - |t| ||f|| provided:

* the frozen domination of the hprob frozen core cost family by the empirically
  supported physical pressure plus the probe constant, and the frozen
  integrability of that family (the two frozen inputs of the consumer, whose
  per-tile content is identified by hprobFrozenCost_eq_maskedFrozenCoreSum with
  the finite-domination lane's masked frozen core family);
* the named rooted tile Campbell mean identification and the readout
  identification frozenPressureLower = Psi, which produce the mean lower input
  by hfrozenMean_of_rootedTileIdentification;
* the physical Finsler data (complete distance, dimension, and a one-Lipschitz
  probe). -/
theorem finalProbLowerData_of_rootedTileMeanIdentification
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
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale f t n)
        (sample n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sample n,
        hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale f t n s ≤
          finslerSupportedPressure F
            (physicalSourceProbability ωM dens₀) (physicalTargetProbability ωM dens₁)
            (A ∪ B) (hA.union hB).measurableSet
            (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) u
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
            |t| * (‖f‖₊ : ℝ))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hId : RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale) T.Index)
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instHprobMeanWiringMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) radius := by
  have hfrozen_mean := hfrozenMean_of_rootedTileIdentification (K := A ∪ B)
    (sample := sample)
    (frozenCost := hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale)
    (g := g) (hId := hId) (Ψ := Ψ) (hread := hread)
  exact physical_finsler_probability_lower_of_frozen_mean_lower hcomplete hdim
    ωM dens₀ dens₁ hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
    (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) radius
    (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign scale)
    hfrozen_int hfrozen_dom hfrozen_mean

end OTSelector.Reconstruction
