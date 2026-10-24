import OTSelector.Reconstruction.FinslerOriginalHprobMeanWiring

/-!
# Opaque wrappers for the family-level frozen-core transport

The family-level transport of the hprob lane frozen core cost (identified with
the finite tile sum of the finite-domination masked frozen core costs) used to
blow up the whnf budget of the elaborator, because the defensive kernel kept
unfolding the large matrix families T.originalFrozenCoreMatrix, normalizedProbe
and the masked frozen core costs.

This module introduces irreducible wrapper definitions for exactly these three
ingredients (probeMatrixOpaque, originalFrozenMatrixOpaque, maskedFrozenCoreOpaque,
plus the per-tile scalar cost tileFrozenCostOpaque and the wrapper family
hprobFrozenCostFamilyOpaque).  Because they are irreducible, the congruence
(funext) reasoning below compares small opaque constants instead of the expanded
matrix expressions, and a single unfold inside each small lemma recovers the
concrete form.  All statements are then transferred back to the concrete hprob
family hprobFrozenCostFamily by one rfl-level identification.

Main results:

* fractionalAssignmentCost_originalFrozenMatrixOpaque_eq_sumTile: pointwise
  transport of the wrapped cost to the sum of wrapped masked frozen core costs;
* hprobFrozenCostFamilyOpaque_eq_maskedTileSum: the family-level (funext)
  transport equality, stated with the wrappers;
* hprobFrozenCostFamilyOpaque_eq_actual: the wrappers agree definitionally
  with the concrete hprob family;
* integrable_hprobFrozenCostFamilyOpaque_of_tileIntegrable: family frozen
  integrability from the named per-tile integrability lane (finite sum of
  integrable functions);
* hprobFrozenInputs_familyLevel: the hprob frozen data at the family level,
  with the sum-level frozen domination as the single named input in the
  consumer's exact shape;
* hprobFrozenInputs_familyLevel_actual: the same data for the concrete hprob
  family.

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

/-! ## 1. Irreducible wrappers -/

/-- Irreducible wrapper around the lane's normalized frozen probe matrix. -/
@[irreducible] def probeMatrixOpaque (T : D.TaylorTiles ε) (K : Set M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (t : ℝ) (n : ℕ) (s : Ω n) :
    T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun c' ↦ normalizedProbe (K := K) base t n s c'

/-- Irreducible wrapper around the lane's simultaneous original frozen core
matrix. -/
@[irreducible] def originalFrozenMatrixOpaque (T : D.TaylorTiles ε) (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (t : ℝ) (n : ℕ) (s : Ω n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t
    (probeMatrixOpaque T K base t n s)

/-- Irreducible wrapper around the masked frozen core matrix of one tile -- the
finite-domination lane's masked frozen core object. -/
@[irreducible] def maskedFrozenCoreOpaque (T : D.TaylorTiles ε) (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (k : T.Index) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) k)
    (frozenCoreMatrix (T.core k) ε (fun _ _ ↦ T.reference k)
      (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t
      ((probeMatrixOpaque T K base t n s) k))

/-- Irreducible wrapper around the scalar masked frozen core cost of one tile at
one sample. -/
@[irreducible] def tileFrozenCostOpaque (T : D.TaylorTiles ε) (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (k : T.Index) : ℝ :=
  fractionalAssignmentCost (maskedFrozenCoreOpaque T K X Y base scale t n s k)
    (Assign n s)

/-- The hprob frozen core cost family, stated with the irreducible wrappers. -/
def hprobFrozenCostFamilyOpaque (T : D.TaylorTiles ε) (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) :
    ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ :=
  fun f t n s ↦
    fractionalAssignmentCost (originalFrozenMatrixOpaque T K X Y base scale t n s)
      (Assign n s) / ((n + 1 : ℕ) : ℝ)

/-! ## 2. The pointwise and family-level transports with the wrappers -/

/-- **Pointwise transport.**  The wrapped normalized frozen core cost is the sum
of the wrapped per-tile masked frozen core costs. -/
theorem fractionalAssignmentCost_originalFrozenMatrixOpaque_eq_sumTile (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (t : ℝ) (n : ℕ) (s : Ω n) :
    fractionalAssignmentCost (originalFrozenMatrixOpaque T K X Y base scale t n s)
        (Assign n s) =
      ∑ k : T.Index, tileFrozenCostOpaque T K X Y base Assign scale t n s k := by
  unfold originalFrozenMatrixOpaque tileFrozenCostOpaque maskedFrozenCoreOpaque
    probeMatrixOpaque
  exact T.fractionalAssignmentCost_originalFrozenCoreMatrix_eq_sum
    (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t
    (fun c' ↦ normalizedProbe (K := K) base t n s c') (Assign n s)

/-- **The family-level transport equality.**  The wrapped hprob frozen core cost
family is the normalized finite tile sum of the wrapped masked frozen core costs
of the finite-domination lane (funext form). -/
theorem hprobFrozenCostFamilyOpaque_eq_maskedTileSum (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) :
    hprobFrozenCostFamilyOpaque T K X Y base Assign scale =
      fun (f : (K × K) →ᵇ ℝ) t n s ↦
        ∑ k : T.Index,
          tileFrozenCostOpaque T K X Y base Assign scale t n s k / ((n + 1 : ℕ) : ℝ) := by
  funext f t n s
  unfold hprobFrozenCostFamilyOpaque
  rw [fractionalAssignmentCost_originalFrozenMatrixOpaque_eq_sumTile T K X Y base Assign scale t n s, Finset.sum_div]

/-- **The wrappers agree with the concrete hprob family.**  One rfl-level
unfolding identifies the wrapped family with the concrete hprobFrozenCostFamily
of the hprob mean wiring. -/
theorem hprobFrozenCostFamilyOpaque_eq_actual (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) :
    hprobFrozenCostFamilyOpaque T K X Y base Assign scale =
      hprobFrozenCostFamily (K := K) T X Y base Assign scale := by
  funext f t n s
  unfold hprobFrozenCostFamilyOpaque originalFrozenMatrixOpaque probeMatrixOpaque
  rfl

/-! ## 3. Family integrability from the per-tile integrability lane -/

/-- **Family frozen integrability from the named per-tile lane.**  If every
wrapped masked frozen core cost is integrable at every sample (the named per-tile
frozen integrability lane), then the wrapped frozen core cost family is
integrable, by finiteness of the tile sum. -/
theorem integrable_hprobFrozenCostFamilyOpaque_of_tileIntegrable (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (sample : ∀ n, Measure (Ω n))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (k : T.Index),
      Integrable (fun s ↦ tileFrozenCostOpaque T K X Y base Assign scale t n s k)
        (sample n)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (hprobFrozenCostFamilyOpaque T K X Y base Assign scale f t n)
        (sample n) := by
  intro f t n
  have hfam : hprobFrozenCostFamilyOpaque T K X Y base Assign scale f t n =
      fun s ↦ ∑ k : T.Index,
        tileFrozenCostOpaque T K X Y base Assign scale t n s k / ((n + 1 : ℕ) : ℝ) := by
    funext s
    exact congrFun (congrFun (congrFun (congrFun
      (hprobFrozenCostFamilyOpaque_eq_maskedTileSum T K X Y base Assign scale) f) t) n) s
  rw [hfam]
  have hsum : Integrable (fun s ↦ ∑ k : T.Index,
      tileFrozenCostOpaque T K X Y base Assign scale t n s k) (sample n) :=
    integrable_finsetSum Finset.univ fun k _ ↦ hint f t n k
  simpa only [Finset.sum_div] using hsum.div_const (((n + 1 : ℕ) : ℝ))

/-! ## 4. The hprob frozen data at the family level -/

/-- **The hprob frozen data at the family level.**

The sum-level frozen domination of the frozen core cost family by the empirical
supported physical pressure plus the probe constant is the single named input
(in the consumer's exact shape); the frozen integrability follows from the named
per-tile integrability lane through the transport. -/
theorem hprobFrozenInputs_familyLevel
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (φ : M → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (sample : ∀ n, Measure (Ω n))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (k : T.Index),
      Integrable (fun s ↦ tileFrozenCostOpaque T K X Y base Assign scale t n s k)
        (sample n))
    (hfrozen_dom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      hprobFrozenCostFamilyOpaque T K X Y base Assign scale f t n s ≤
        finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s)
          φ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ)) :
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
        Integrable (hprobFrozenCostFamilyOpaque T K X Y base Assign scale f t n)
          (sample n)) ∧
      (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
        hprobFrozenCostFamilyOpaque T K X Y base Assign scale f t n s ≤
          finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s)
            φ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
            |t| * (‖f‖₊ : ℝ)) :=
  ⟨integrable_hprobFrozenCostFamilyOpaque_of_tileIntegrable T K X Y base Assign scale
      sample hint, hfrozen_dom⟩

/-- **The hprob frozen data for the concrete lane family.**  The same pair of
frozen inputs, transferred along the single wrapper identification to the
concrete hprobFrozenCostFamily of the hprob lane. -/
theorem hprobFrozenInputs_familyLevel_actual
    {μ ν : ProbabilityMeasure M} {K : Set M} (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (φ : M → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (sample : ∀ n, Measure (Ω n))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (k : T.Index),
      Integrable (fun s ↦ tileFrozenCostOpaque T K X Y base Assign scale t n s k)
        (sample n))
    (hfrozen_dom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      hprobFrozenCostFamily (K := K) T X Y base Assign scale f t n s ≤
        finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s)
          φ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ)) :
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
        Integrable (hprobFrozenCostFamily (K := K) T X Y base Assign scale f t n)
          (sample n)) ∧
      (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
        hprobFrozenCostFamily (K := K) T X Y base Assign scale f t n s ≤
          finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s)
            φ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
            |t| * (‖f‖₊ : ℝ)) := by
  have htransfer := hprobFrozenCostFamilyOpaque_eq_actual T K X Y base Assign scale
  have hdomOpaque : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      hprobFrozenCostFamilyOpaque T K X Y base Assign scale f t n s ≤
        finslerSupportedPressure F μ ν K hK hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s)
          φ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ) := by
    intro f t n
    filter_upwards [hfrozen_dom f t n] with s hs
    rwa [htransfer]
  obtain ⟨hintF, hdomF⟩ := hprobFrozenInputs_familyLevel T hK hμ hν
    φ X Y base Assign scale sample hint hdomOpaque
  refine ⟨?_, ?_⟩
  · intro f t n
    rw [← htransfer]
    exact hintF f t n
  · intro f t n
    filter_upwards [hdomF f t n] with s hs
    rwa [← htransfer]

end OTSelector.Reconstruction