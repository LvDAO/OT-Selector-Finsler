import OTSelector.Reconstruction.FinslerOriginalScenePressureWiring
import OTSelector.Reconstruction.FinslerOriginalIIDPressureLowerLocalization
import OTSelector.Reconstruction.FinslerOriginalCampbellMeanBound

/-!
# Assembling the lower pressure localization (hprob) from the frozen-data lane

This module assembles the missing items of the hprob chain of
FinslerGeneralSelectorAssemblyFinal.lean from the frozen-data lane:

* the lower population mean bound, produced from the named tile-level Campbell
  mean identification RootedTileCampbellMeanIdentification (the limit-law
  content of the probability lane) rather than kept as an independent
  hypothesis;

* the shifted lower pressure readout frozenProbePressureLower, which is the
  frozen Campbell readout minus the probe constant |t| ||f||, i.e. exactly the
  normalization under which the frozen core cost dominates the empirical
  pressure;

* the pressure lower readout identification: the mean-limit pressureLower
  function equals the assembled Palm readout Psi once the matching upper
  population mean bound is supplied (the single remaining sub-gap).

The final hprob-shaped theorem
physical_finsler_probability_lower_of_tileIdentification has exactly the hprob
clause of FinslerSelectorFinalInputs, with pressureLower given by the frozen
readout convention.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}

/-- **The frozen lower pressure readout after paying the probe constant.**

The frozen Campbell readout of the frozen root integrand minus the probe
constant |t| ||f||.  This is the population pressure whose eventual lower bound
frozenProbePressureLower f t + |t| ||f|| - eps <= E[frozenCost] is the mean lower
bound consistent with the frozen-core finite domination
frozenCost <= V + |t| ||f|| of the empirical pressure. -/
noncomputable def frozenProbePressureLower
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ) :
    ((K × K) →ᵇ ℝ) → ℝ → ℝ :=
  fun f t ↦ frozenPressureLower Seed a κ lambda g q f t - |t| * (‖f‖₊ : ℝ)

/-- **The lower population mean bound from the named tile Campbell mean
identification.**

The named limit-law content RootedTileCampbellMeanIdentification (per-tile
Campbell values with vanishing total budget) yields the expectation-level
Campbell lower bound for the frozen core functional: eventually
campbellAveragedFrozenCost (g f t) q - eps <= E[frozenCost f t].  This
instantiates item (a) of the hprob chain from the probability lane. -/
theorem frozenMeanLower_of_rootedTileIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (hId : OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.RootedTileCampbellMeanIdentification
      Seed a κ lambda g q P frozenCost ιt) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q - ε ≤
        ∫ s, frozenCost f t n s ∂P n :=
  OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.camFrozenMeanBound_of_rootedTileIdentification
    Seed a κ lambda g (P := P) (frozenCost := frozenCost) (q := q) hId

/-- **The hprob clause of the final assembly from the tile Campbell
identification.**

This is the assembly's hprob clause verbatim: for the physical population data
(physical source/target probabilities, compact carrier A union B, original iid
arrays and a one-Lipschitz probe), frozen-core finite domination, integrability
and the expectation-level Campbell lower bound at the shifted frozen pressure
frozenProbePressureLower, the empirical supported pressure satisfies
P_n {s | V n s < frozenProbePressureLower f t - eps} -> 0 along the tilt
interval. -/
theorem physical_finsler_probability_lower_of_tileIdentification
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) =
      (physicalSourceProbability ωM ρ₀ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) =
      (physicalTargetProbability ωM ρ₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instPressureLowerAssemblyMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (frozenCost : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (hId : OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.RootedTileCampbellMeanIdentification
      Seed a κ lambda g q P frozenCost ιt)
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ)) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F
        (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          frozenProbePressureLower Seed a κ lambda g q f t - ε}) atTop (𝓝 0) := by
  intro f t ε ht hε
  refine physical_finsler_probability_lower_of_frozen_mean_lower hcomplete hdim ωM ρ₀ ρ₁
    (A := A) (B := B) hA hB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ
    (frozenProbePressureLower Seed a κ lambda g q) radius frozenCost hfrozen_int
    hfrozen_dom ?_ f t ε ht hε
  · intro f t ε hε
    filter_upwards [frozenMeanLower_of_rootedTileIdentification Seed a κ lambda g
      (P := P) (frozenCost := frozenCost) (q := q) hId f t ε hε] with n hn
    show campbellAveragedFrozenCost Seed a κ lambda (g f t) q - |t| * (‖f‖₊ : ℝ) +
      |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n
    linarith

/-- **The pressure lower readout is the assembled Palm readout.**

Item (c) of the hprob chain: if pressureLower is the limit of the empirical
frozen means (hlim) and the matching upper population mean bound hUp holds, then
pressureLower equals the assembled Palm readout Psi.  The lower mean bound is
discharged internally from the named tile Campbell mean identification, so the
upper bound hUp is the single remaining sub-gap of the readout identification. -/
theorem pressureLower_eq_sceneReadout_of_tileIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hId : OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.RootedTileCampbellMeanIdentification
      Seed a κ lambda g q P frozenCost ιt)
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, frozenCost f t n s ∂P n) atTop
        (𝓝 (pressureLower f t)))
    (hUp : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, frozenCost f t n s ∂P n ≤
        frozenPressureLower Seed a κ lambda g q f t + ε)
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower Seed a κ lambda g q = Ψ) :
    pressureLower = Ψ :=
  pressureLower_eq_sceneReadout_of_empirical_limit Seed a κ lambda g (P := P)
    (frozenCost := frozenCost) pressureLower hId hlim hUp Ψ hread

end OTSelector.Reconstruction