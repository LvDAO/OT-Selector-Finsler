import OTSelector.Reconstruction.FinslerOriginalFrozenLowerDomination

/-!
# F12: the SHIFTED lower probability data from the unshifted bare domination

The paper's shifted readout is \Psi - |t|*||f|| (the probe constant |t|*||f||_infty is
carried as the shift).  This file bridges the two presentations at the SAME frozen
cost family, so the lane's hId producers and the fast unshifted bare domination can be
consumed together:

1. \texttt{finalProbLowerData_shifted_of_unshifted}: for ANY pressure field, the
   unshifted FinalProbLowerData implies the shifted one, because
   \((P - c) - \varepsilon = P - (\varepsilon + c)\) and \(c = |t|*||f|| \ge 0\), so the
   unshifted statement at tolerance \varepsilon + c is exactly the shifted statement
   at tolerance \varepsilon.
2. \texttt{finalProbLowerData_shifted_of_bareDomination}: the shifted
   FinalProbLowerData at \Psi - |t|*||f|| from the fast unshifted bare domination, with
   the SAME frozenCost family (hence hId applies unchanged); the only inputs are the
   fast theorem's: population data, the frozen family/hId/integrability and the paper's
   bare domination.

No \texttt{sorry}, \texttt{admit} or added axiom.
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

/-- **Shift bridge**: unshifted lower probability data at a pressure field implies the
shifted data at \texttt{pressureLower - |t|*||f||}, with the same radius. -/
theorem finalProbLowerData_shifted_of_unshifted
    (μ ν : ProbabilityMeasure M) (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {sample : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (pressureLower : FinalPressureField A B) (radius : FinalRadiusField A B)
    (h : FinalProbLowerData F μ ν hA hB hμA hνB sample X Y u pressureLower radius) :
    FinalProbLowerData F μ ν hA hB hμA hνB sample X Y u
      (fun f t ↦ pressureLower f t - |t| * (‖f‖₊ : ℝ)) radius := by
  intro f t ε ht hε
  have hc : 0 ≤ |t| * (‖f‖₊ : ℝ) :=
    mul_nonneg (abs_nonneg t) (by positivity)
  have hε' : 0 < ε + |t| * (‖f‖₊ : ℝ) := by linarith
  have hshift : pressureLower f t - (ε + |t| * (‖f‖₊ : ℝ)) =
      (pressureLower f t - |t| * (‖f‖₊ : ℝ)) - ε := by ring
  simpa only [← hshift] using h f t (ε + |t| * (‖f‖₊ : ℝ)) ht hε'

theorem finalProbLowerData_shifted_of_bareDomination
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
    (hbaredom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sample n,
        frozenCost f t n s ≤
          finslerSupportedPressure F
            (physicalSourceProbability ωM dens₀) (physicalTargetProbability ωM dens₁)
            (A ∪ B) (hA.union hB).measurableSet
            (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) u
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (sample n))
 :
    FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ frozenPressureLower P a κ lambda g q f t - |t| * (‖f‖₊ : ℝ)) radius := by
  exact finalProbLowerData_shifted_of_unshifted
    (μ := physicalSourceProbability ωM dens₀)
    (ν := physicalTargetProbability ωM dens₁)
    (hA := hA) (hB := hB) (hμA := hμA) (hνB := hνB)
    (sample := sample) (X := X) (Y := Y)
    (pressureLower := fun f t ↦ frozenPressureLower P a κ lambda g q f t) (radius := radius)
    (h := finalProbLowerData_of_frozen_domination hcomplete hdim ωM dens₀ dens₁ hA hB hμA hνB
      sample X Y hX hY hXi hYi hXlaw hYlaw hXY u hu radius g frozenCost hId
      hbaredom hfrozen_int)

end OTSelector.Reconstruction
