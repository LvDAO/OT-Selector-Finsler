import OTSelector.Reconstruction.FinslerOriginalUnshiftedHprobProducer
import OTSelector.Reconstruction.FinslerOriginalPressureLowerAssembly

/-!
# F12: the mean clipping correction and the unshifted hprob

The unshifted lower probability input needs the frozen mean lower bound at the
probe-constant shift `frozenPressureLower + |t| * ‖f‖`.  This file isolates the exact
statistical content of that requirement as the **mean clipping correction**:

* `frozenPressureLower_eq_campbellAveragedFrozenCost`: the unshifted frozen pressure is
  exactly the Campbell average of the probe-marked readout `g f t` (definitional);
* `mean_clipping_correction_of_rootedTileIdentification`: the tile Campbell
  identification already gives the *unshifted* mean lower bound
  `frozenPressureLower - ε ≤ ∫ frozenCost` (mean clipping correction ≥ -ε);
* `clipping_mean_gap_iff`: the needed shifted bound is equivalent to the mean clipping
  correction dominating the support-bound slack `|t| * ‖f‖` up to ε;
* `finalProbLowerData_unshifted_actual`: the unshifted hprob from the lane data plus
  exactly the mean clipping correction `hclipMean`.

The pointwise support bound `frozenCost ≤ finslerSupportedPressure + |t| * ‖f‖` is an
UPPER bound on the frozen cost and therefore cannot imply the lower mean inequality;
the mean clipping correction is the genuinely remaining statistical input.  No `sorry`,
`admit` or added axiom occurs.
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

variable {T : D.TaylorTiles ε}
variable {A B : Set M}

/-- The unshifted frozen pressure is definitionally the Campbell average of the
probe-marked readout. -/
theorem frozenPressureLower_eq_campbellAveragedFrozenCost
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) :
    frozenPressureLower P a κ lambda g q f t =
      campbellAveragedFrozenCost P a κ lambda (g f t) q :=
  rfl

/-- **Available mean clipping correction.**  The tile Campbell identification gives the
frozen mean lower bound at the unshifted frozen pressure: in mean the clipping
correction is at most ε. -/
theorem mean_clipping_correction_of_rootedTileIdentification
    {g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ}
    {sample : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (sample n)]
    {frozenCost : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ}
    (hId : OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.RootedTileCampbellMeanIdentification
      P a κ lambda g q sample frozenCost T.Index) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      frozenPressureLower P a κ lambda g q f t - ε ≤
        ∫ s, frozenCost f t n s ∂sample n := by
  have hmean := frozenMeanLower_of_rootedTileIdentification (Seed := P) (a := a)
    (κ := κ) (lambda := lambda) (g := g) (P := sample) (frozenCost := frozenCost)
    (q := q) (ιt := T.Index) hId
  intro f t ε hε
  filter_upwards [hmean f t ε hε] with n hn
  rwa [frozenPressureLower_eq_campbellAveragedFrozenCost g f t]

/-- **The exact gap.**  The shifted mean bound is equivalent to the mean clipping
correction covering the support-bound slack `|t| * ‖f‖`. -/
theorem clipping_mean_gap_iff
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    {sample : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (sample n)]
    (frozenCost : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ) :
    (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
        frozenPressureLower P a κ lambda g q f t + |t| * (‖f‖₊ : ℝ) - ε ≤
          ∫ s, frozenCost f t n s ∂sample n) ↔
      (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
        (∫ s, frozenCost f t n s ∂sample n) - frozenPressureLower P a κ lambda g q f t ≥
          |t| * (‖f‖₊ : ℝ) - ε) := by
  constructor
  · intro h f t ε hε
    filter_upwards [h f t ε hε] with n hn
    linarith
  · intro h f t ε hε
    filter_upwards [h f t ε hε] with n hn
    linarith

theorem finalProbLowerData_unshifted_actual
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (sample n))
    (hYi : ∀ n, iIndepFun (Y n) (sample n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)),
      (sample n).map (X n i) = (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ (n : ℕ) (i : Fin (n + 1)),
      (sample n).map (Y n i) = (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun s i ↦ X n i s) (fun s i ↦ Y n i s) (sample n))
    (u : M → ℝ)
    (hu : let _instFinslerLowerAssemblyMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (radius : FinalRadiusField A B)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (frozenCost : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hId : OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.RootedTileCampbellMeanIdentification
      P a κ lambda g q sample frozenCost T.Index)
    (hclipMean : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        (∫ s, frozenCost f t n s ∂sample n) - frozenPressureLower P a κ lambda g q f t ≥
          |t| * (‖f‖₊ : ℝ) - ε)
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (sample n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sample n,
        frozenCost f t n s ≤
          finslerSupportedPressure F
            (physicalSourceProbability ωM dens₀) (physicalTargetProbability ωM dens₁)
            (A ∪ B) (hA.union hB).measurableSet
            (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) u
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
            |t| * (‖f‖₊ : ℝ)) :
    FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ frozenPressureLower P a κ lambda g q f t) radius := by
  have hshift : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        frozenPressureLower P a κ lambda g q f t + |t| * (‖f‖₊ : ℝ) - ε ≤
          ∫ s, frozenCost f t n s ∂sample n := by
    intro f t ε hε
    filter_upwards [hclipMean f t ε hε] with n hn
    linarith
  intro f t ε ht hε
  exact physical_finsler_probability_lower_of_frozen_mean_lower hcomplete hdim ωM
    dens₀ dens₁ hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
    (fun f t ↦ frozenPressureLower P a κ lambda g q f t) radius frozenCost
    hfrozen_int hfrozen_dom hshift f t ε ht hε

end OTSelector.Reconstruction
