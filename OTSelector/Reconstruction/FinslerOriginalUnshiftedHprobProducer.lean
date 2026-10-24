import OTSelector.Reconstruction.FinslerOriginalHprobWiring
import OTSelector.Reconstruction.FinslerOriginalIIDPressureLowerLocalization
import OTSelector.Reconstruction.FinslerOriginalPressureLowerAssembly
import OTSelector.Reconstruction.FinslerOriginalEndgameLowerField

/-!
# F12: the paper's unshifted hprob at the probe-indexed frozen readout

The shifted lower probability input of `finalProbLowerData_of_palmSampleReadout` uses
the pressure `fun f t ↦ Ψ f t - |t| * ‖f‖`.  Audit F12 observes that the tile-lane
`hgt` makes the frozen readout probe-independent, so this shifted pressure is not the
paper's pressure.  The repair runs the lower localization on the frozen readout itself:

* the probe enters through the (arbitrary, probe-indexed) frozen readout
  `g : probe → ℝ → (ℚ → M) → ℝ`;
* the frozen pressure is the unshifted `frozenPressureLower P a κ lambda g q`
  (definitionally `campbellAveragedFrozenCost P a κ lambda (g f t) q`);
* the paper support bound `frozenCost ≤ finslerSupportedPressure + |t| * ‖f‖` is NOT
  weakened: shifting the FROZEN COST by the probe constant `|t| * ‖f‖` (rather than
  shifting the pressure) makes the localization theorem's frozen mean lower bound hold
  in the required `pressure + |t| * ‖f‖` form, and its domination hypothesis is still
  exactly FrozenSupportBound's shape.  Hence the probability statement is obtained at
  the UNSHIFTED pressure `frozenPressureLower` with no `hgt`, no `Ψ`, and no probe
  shift in the pressure.

The tile Campbell readout identification `hId` (probe-marked `g`) is kept as a
hypothesis but is NOT sufficient by itself: the lower-localization theorem consumes the
frozen mean lower bound at `pressure + |t| * ‖f‖`, while the palm-lane identification
only provides it at `frozenPressureLower`.  The genuinely new paper input isolated here
is therefore `hfrozen_mean_shifted`: the frozen mean lower bound at the probe-constant
shift `frozenPressureLower + |t| * ‖f‖` (equivalently, vanishing of the mean clipping
correction).  The support bound keeps exactly the paper shape
`frozenCost ≤ finslerSupportedPressure + |t| * ‖f‖` and is used unchanged.

No `sorry`, `admit` or added axiom occurs.
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

variable {A B : Set M}

/-- **The unshifted hprob.**  The paper's lower probability input
`FinalProbLowerData` at the probe-indexed unshifted frozen pressure
`fun f t ↦ frozenPressureLower P a κ lambda g q f t`, derived from the paper support
bound (shape `frozenCost ≤ finslerSupportedPressure + |t| * ‖f‖`) and the tile
Campbell mean identification `hId` for the probe-marked readout `g`.

The probe shift `|t| * ‖f‖` is absorbed into the frozen cost family inside the
lower-localization theorem; the pressure itself carries no probe shift. -/
theorem finalProbLowerData_unshifted
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
    (hfrozen_mean_shifted : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        frozenPressureLower P a κ lambda g q f t + |t| * (‖f‖₊ : ℝ) - ε ≤
          ∫ s, frozenCost f t n s ∂sample n)
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
  intro f t ε ht hε
  exact physical_finsler_probability_lower_of_frozen_mean_lower hcomplete hdim ωM
    dens₀ dens₁ hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
    (fun f t ↦ frozenPressureLower P a κ lambda g q f t) radius frozenCost
    hfrozen_int hfrozen_dom hfrozen_mean_shifted f t ε ht hε

end OTSelector.Reconstruction
