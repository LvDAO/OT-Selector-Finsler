import OTSelector.Reconstruction.FinslerRelativeLawOriginalFixedMicrocellShapeExpectation
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelEnergyExpectation

/-! The global original frozen model is the sum of its actual seed cell
models on one unchanged cloud, with the physical dimension proved internally. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Summing actual original seed costs preserves the literal global model,
including its canonical tie choices. The apparent seed-dependent dimensions
are the same original physical dimension minus one. -/
theorem PopulationLocalPressureCore.original_model_family_eq_seed_sum
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    {Cells T : Type*} [Fintype Cells] {N : ℕ}
    (coreIndex : Cells → Fin D.haar.continuous.count)
    {range : Set ℝ} {width : ℝ} (Q : Cells → FiniteScalarBins range width)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (cell : Cells → Set (ℚ → M))
    (f : M × M →ᵇ ℝ) (tilt : ℝ)
    (sample : (Fin N → M × Option (Bool × T)) × (Fin N → M × Option (Bool × T))) :
    D.originalClockClassOldModelValue (q := Module.finrank ℝ E - 1)
      coreIndex Q reference classify cell f tilt sample =
      ∑ c, let C := D.haar.continuous.coefficient (coreIndex c)
        let S := (P C.seedIndex).seed
        let root := populationSeedRootLabelValue S a
        let e := (Module.finBasis ℝ S.covector.ker).equivFunL
        let q := Module.finrank ℝ S.covector.ker
        originalRetainedSeedClassCost a (cell c) (fun x ↦ root (a x)) e.toLinearMap
          (fun x ↦ classify c (u x)) (fun x ↦ classify c (u x)) (C.clockClassAllowed (Q c))
          ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic (Q c) (reference c).val)
          (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt sample := by
  classical
  unfold PopulationLocalPressureCore.originalClockClassOldModelValue
  apply Finset.sum_congr rfl
  intro c _
  have hq := D.original_seed_label_finrank (coreIndex c)
  have hscale : (N : ℝ) ^ (2 / (Module.finrank ℝ
      (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker : ℝ)) =
      (N : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) := by rw [hq]
  dsimp only
  rw [hscale]
  exact D.original_clockClass_canonical_cost_eq_seed coreIndex reference Q classify f cell c
    ((N : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))) tilt sample

/-- Actual seed-cell integrability gives integrability and the exact sum of
means for the global original model on any ONE unchanged cloud law. -/
theorem PopulationLocalPressureCore.original_model_family_integral_eq_seed_sum
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    {Cells T : Type*} [Fintype Cells] {N : ℕ}
    [MeasurableSpace (Option (Bool × T))]
    (coreIndex : Cells → Fin D.haar.continuous.count)
    {range : Set ℝ} {width : ℝ} (Q : Cells → FiniteScalarBins range width)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (cell : Cells → Set (ℚ → M))
    (f : M × M →ᵇ ℝ) (tilt : ℝ)
    (law : Measure ((Fin N → M × Option (Bool × T)) × (Fin N → M × Option (Bool × T))))
    (hI : ∀ c,
      let C := D.haar.continuous.coefficient (coreIndex c)
      let S := (P C.seedIndex).seed
      let root := populationSeedRootLabelValue S a
      let e := (Module.finBasis ℝ S.covector.ker).equivFunL
      let q := Module.finrank ℝ S.covector.ker
      Integrable (originalRetainedSeedClassCost a (cell c) (fun x ↦ root (a x)) e.toLinearMap
        (fun x ↦ classify c (u x)) (fun x ↦ classify c (u x)) (C.clockClassAllowed (Q c))
        ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic (Q c) (reference c).val)
        (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt) law) :
    let original := D.originalClockClassOldModelValue (q := Module.finrank ℝ E - 1)
      coreIndex Q reference classify cell f tilt (T := T) (n := N)
    Integrable original law ∧ (∫ sample, original sample ∂law) =
      ∑ c, let C := D.haar.continuous.coefficient (coreIndex c)
        let S := (P C.seedIndex).seed
        let root := populationSeedRootLabelValue S a
        let e := (Module.finBasis ℝ S.covector.ker).equivFunL
        let q := Module.finrank ℝ S.covector.ker
        ∫ sample, originalRetainedSeedClassCost a (cell c) (fun x ↦ root (a x)) e.toLinearMap
          (fun x ↦ classify c (u x)) (fun x ↦ classify c (u x)) (C.clockClassAllowed (Q c))
          ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic (Q c) (reference c).val)
          (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt sample ∂law := by
  classical
  dsimp only
  have heq : D.originalClockClassOldModelValue (q := Module.finrank ℝ E - 1)
      coreIndex Q reference classify cell f tilt (T := T) (n := N) =
      fun sample ↦ ∑ c, let C := D.haar.continuous.coefficient (coreIndex c)
        let S := (P C.seedIndex).seed
        let root := populationSeedRootLabelValue S a
        let e := (Module.finBasis ℝ S.covector.ker).equivFunL
        let q := Module.finrank ℝ S.covector.ker
        originalRetainedSeedClassCost a (cell c) (fun x ↦ root (a x)) e.toLinearMap
          (fun x ↦ classify c (u x)) (fun x ↦ classify c (u x)) (C.clockClassAllowed (Q c))
          ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic (Q c) (reference c).val)
          (C.clockClassProbe (Q c) (reference c).val (reference c).property f) tilt sample :=
    funext (D.original_model_family_eq_seed_sum coreIndex Q reference classify cell f tilt)
  rw [heq]
  exact ⟨integrable_finsetSum Finset.univ (fun c _ ↦ hI c),
    integral_finsetSum Finset.univ (fun c _ ↦ hI c)⟩

end OTSelector.Reconstruction
