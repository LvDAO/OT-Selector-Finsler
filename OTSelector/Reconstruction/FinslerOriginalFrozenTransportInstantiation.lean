import OTSelector.Reconstruction.FinslerOriginalFrozenTransportWrappers
import OTSelector.Reconstruction.FinslerPopulationPressureTiles

/-!
# Instantiation and composition of the frozen-core transport

This module closes the packaging of the frozen lane transport built in
FinslerOriginalFrozenTransportWrappers.

## 1. Identification with the concrete named lane

The irreducible wrapper tileFrozenCostOpaque is identified, by a single unfold
and rfl, with the concrete named lane cost T.tileFrozenCost.  The identification
is packaged both pointwise (tileFrozenCostOpaque_eq_tileFrozenCost) and as an
integrability transfer (integrable_tileFrozenCostOpaque_of_tileFrozenCost), plus
the resulting family-level concrete transport
hprobFrozenCostFamily_eq_sum_tileFrozenCost.

## 2. Instantiation of the tile family T

The repository constructs TaylorTiles only through existence: the only
construction is
PopulationLocalPressureCore.nonempty_taylorTiles
(FinslerPopulationPressureTiles.lean), which produces Nonempty (D.TaylorTiles eps)
from the smooth strongly convex Finsler core, completeness, the 1-Lipschitz
potential u, measurability of a and injectivity of x |-> (a x, u x).  There is no
canonical concrete definition of a tile family (no def taylorTiles) and no
canonical choice of covers and partitions.  We therefore package the choice
chosenTaylorTiles; every theorem below is stated for an arbitrary
T : D.TaylorTiles eps, hence can be instantiated with chosenTaylorTiles.  The
precise missing ingredients for a fully concrete instantiation are:

* a definitional construction of the Taylor covers and partitions (currently
  only Classical.choice of the two Nonempty statements);
* the lane data attached to that concrete family: the per-tile frozen
  integrability lane and the sum-level frozen domination (both remain named
  inputs below), the rooted tile mean identification hId, the read-off hread,
  and the empirical law / independence data of the sample.

## 3. Composition with the consumer

hprobFrozenInputs_actual_composed feeds the family-level frozen data derived in
FinslerOriginalFrozenTransportWrappers into
finalProbLowerData_of_rootedTileMeanIdentification, so that the only frozen-lane
inputs are the per-tile integrability lane (in the concrete named
T.tileFrozenCost form) and the sum-level frozen domination in the consumer's
exact shape.  The conclusion is the FinalProbLowerData of the hprob consumer.

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

/-! ## 1. Identification of the wrapper with the concrete named lane -/

/-- **The wrapper is the concrete named lane cost.**  One unfold of the three
irreducible wrappers reduces tileFrozenCostOpaque to exactly T.tileFrozenCost at
the same sample, probe family and assignment. -/
theorem tileFrozenCostOpaque_eq_tileFrozenCost (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (k : T.Index) :
    tileFrozenCostOpaque T K X Y base Assign scale t n s k =
      T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
        (fun s' c' ↦ normalizedProbe (K := K) base t n s' c') (Assign n) (scale n) t k s := by
  unfold tileFrozenCostOpaque maskedFrozenCoreOpaque probeMatrixOpaque
  rfl

/-- **Integrability transfer to the concrete named lane.**  The named per-tile
frozen integrability lane, stated with the concrete T.tileFrozenCost, implies
the per-tile integrability of the wrapper cost used by the family-level frozen
data theorem. -/
theorem integrable_tileFrozenCostOpaque_of_tileFrozenCost (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (sample : ∀ n, Measure (Ω n))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (k : T.Index),
      Integrable (fun s ↦
        T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := K) base t n s' c') (Assign n) (scale n) t k s)
        (sample n)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (k : T.Index),
      Integrable (fun s ↦ tileFrozenCostOpaque T K X Y base Assign scale t n s k)
        (sample n) := by
  intro f t n k
  refine (hint f t n k).congr (Filter.Eventually.of_forall fun s ↦ ?_)
  exact (tileFrozenCostOpaque_eq_tileFrozenCost T K X Y base Assign scale t n s k).symm

/-- **The family-level concrete transport.**  The lane frozen cost family is the
normalized finite sum of the concrete named per-tile frozen costs. -/
theorem hprobFrozenCostFamily_eq_sum_tileFrozenCost (K : Set M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) :
    hprobFrozenCostFamily (K := K) T X Y base Assign scale =
      fun (f : (K × K) →ᵇ ℝ) t n s ↦
        ∑ k : T.Index,
          T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
            (fun s' c' ↦ normalizedProbe (K := K) base t n s' c') (Assign n) (scale n) t k s /
            ((n + 1 : ℕ) : ℝ) := by
  rw [← hprobFrozenCostFamilyOpaque_eq_actual T K X Y base Assign scale,
    hprobFrozenCostFamilyOpaque_eq_maskedTileSum T K X Y base Assign scale]
  funext f t n s
  simp only [tileFrozenCostOpaque_eq_tileFrozenCost]

/-! ## 2. Instantiation of the tile family -/

/-- **The tile family used by the lane, chosen from the existence result.**  The
repository supplies only Nonempty (D.TaylorTiles eps); this is the resulting
choice of Taylor covers and root partitions. -/
noncomputable def chosenTaylorTiles
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (huLip : let _instTilesMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) : D.TaylorTiles ε₀ :=
  Classical.choice (D.nonempty_taylorTiles hF hcomplete huLip ha hinj hε₀)

/-- The chosen tile family is a genuine tile family of the population core. -/
theorem chosenTaylorTiles_isTaylorTiles
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (huLip : let _instTilesMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) : Nonempty (D.TaylorTiles ε₀) :=
  ⟨chosenTaylorTiles hF hcomplete huLip ha hinj hε₀⟩

/-! ## 3. Composition with the consumer -/

/-- **The composed consumer theorem.**

The only frozen-lane inputs are:

* hint: the per-tile frozen integrability lane, in the concrete named
  T.tileFrozenCost form;
* hfrozen_dom: the sum-level frozen domination of the lane frozen cost family,
  in the exact shape consumed by the hprob probability lower bound.

Everything else (physical data, laws, independence, the rooted tile mean
identification hId and the read-off hread) is a named input as in the consumer.
The conclusion is the FinalProbLowerData of the hprob consumer. -/
theorem hprobFrozenInputs_actual_composed
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
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (k : T.Index),
      Integrable (fun s ↦
        T.tileFrozenCost (fun s' i ↦ X n i s') (fun s' i ↦ Y n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c') (Assign n) (scale n) t k s)
        (sample n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
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
  have hintOpaque : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (k : T.Index),
      Integrable (fun s ↦ tileFrozenCostOpaque T (A ∪ B) X Y base Assign scale t n s k)
        (sample n) :=
    integrable_tileFrozenCostOpaque_of_tileFrozenCost T (A ∪ B) X Y base Assign scale
      sample hint
  obtain ⟨hfrozen_int, hfrozen_dom'⟩ :=
    hprobFrozenInputs_familyLevel_actual T (hA.union hB).measurableSet
      (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy) u
      X Y base Assign scale sample hintOpaque hfrozen_dom
  exact finalProbLowerData_of_rootedTileMeanIdentification T hdim ωM dens₀ dens₁
    hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY radius scale base Assign
    hfrozen_int hfrozen_dom' g hId Ψ hread hcomplete hu

end OTSelector.Reconstruction
