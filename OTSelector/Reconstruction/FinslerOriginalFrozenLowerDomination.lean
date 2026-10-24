import OTSelector.Reconstruction.FinslerOriginalMeanClippingCorrection

/-!
# Frozen mean domination gives the lower pressure bound

Conditions: the same original population, iid sampling laws, integrable frozen
costs, their Campbell mean identification, and unshifted pointwise domination.
Objects: the frozen finite-cost family and its population pressure readout.
Proof: identify its mean, add the same probe constant to both sides, then apply
the existing physical pressure concentration theorem. The cost family remains
an opaque argument so this assembly does not unfold its implementation.

The shifted support-bound parameter of the earlier paper wrapper was unused.
The one implementation below supplies all lower-data consumers directly.
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

theorem finalProbLowerData_of_frozen_domination
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
      (fun f t ↦ frozenPressureLower P a κ lambda g q f t) radius := by
  have hmean := frozenMeanLower_of_rootedTileIdentification (Seed := P) (a := a)
    (κ := κ) (lambda := lambda) (g := g) (P := sample) (frozenCost := frozenCost)
    (q := q) (ιt := T.Index) hId
  have hint' : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (fun s ↦ frozenCost f t n s + |t| * (‖f‖₊ : ℝ)) (sample n) :=
    fun f t n ↦ (hfrozen_int f t n).add (integrable_const _)
  have hdom' : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sample n,
        frozenCost f t n s + |t| * (‖f‖₊ : ℝ) ≤
          finslerSupportedPressure F
            (physicalSourceProbability ωM dens₀) (physicalTargetProbability ωM dens₁)
            (A ∪ B) (hA.union hB).measurableSet
            (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
            (fun i ↦ X n i s) (fun i ↦ Y n i s) u
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
            |t| * (‖f‖₊ : ℝ) := by
    intro f t n
    filter_upwards [hbaredom f t n] with s hs
    linarith
  have hconst : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∫ s : Ω n, (|t| * (‖f‖₊ : ℝ)) ∂sample n = |t| * (‖f‖₊ : ℝ) := by
    intro f t n
    rw [integral_const, smul_eq_mul]
    simp
  have hmean' : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        frozenPressureLower P a κ lambda g q f t + |t| * (‖f‖₊ : ℝ) - ε ≤
          ∫ s, (frozenCost f t n s + |t| * (‖f‖₊ : ℝ)) ∂sample n := by
    intro f t ε hε
    filter_upwards [hmean f t ε hε] with n hn
    have hn' : campbellAveragedFrozenCost P a κ lambda (g f t) q - ε ≤
        ∫ s, frozenCost f t n s ∂sample n := hn
    have hsplit : ∫ s, (frozenCost f t n s + |t| * (‖f‖₊ : ℝ)) ∂sample n =
        (∫ s, frozenCost f t n s ∂sample n) + |t| * (‖f‖₊ : ℝ) := by
      rw [integral_add (hfrozen_int f t n) (integrable_const _), hconst f t n]
    have hlr : frozenPressureLower P a κ lambda g q f t =
        campbellAveragedFrozenCost P a κ lambda (g f t) q := rfl
    rw [hsplit, hlr]
    linarith
  intro f t ε ht hε
  exact physical_finsler_probability_lower_of_frozen_mean_lower hcomplete hdim ωM
    dens₀ dens₁ hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
    (fun f t ↦ frozenPressureLower P a κ lambda g q f t) radius
    (fun f t n s ↦ frozenCost f t n s + |t| * (‖f‖₊ : ℝ)) hint' hdom' hmean' f t ε ht hε

end OTSelector.Reconstruction
