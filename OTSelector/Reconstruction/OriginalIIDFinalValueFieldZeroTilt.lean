import OTSelector.Reconstruction.FinslerOriginalPhysicalRootPressure

/-! Zero-tilt original pressures are the same intrinsic kinetic field for every probe. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- At zero tilt, the literal finite legal maximum pressure retains no probe term. -/
theorem legalMarkedScalePressure_zero_probe_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g h : A → B → ℝ) (R : ℝ) :
    legalMarkedScalePressure q source target α β kin g R 0 =
      legalMarkedScalePressure q source target α β kin h R 0 := by
  simp only [legalMarkedScalePressure, legalMarkedPressure, legalMarkedTilted,
    legalMarkedFixedValue, zero_mul, add_zero]

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The thermodynamic pressure at zero tilt is independent of the bounded physical probe. -/
theorem originalSeedRootPressure_zero_probe_eq
    (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (b : Z × ℝ → M) (f g : M × M →ᵇ ℝ) (z : Z) :
    originalSeedRootPressure S a η₀ η₁ b f z 0 = originalSeedRootPressure S a η₀ η₁ b g z 0 := by
  unfold originalSeedRootPressure originalSeedRootScalePressure
  congr 1
  funext R
  exact legalMarkedScalePressure_zero_probe_eq _ _ _ _ _ _ _ _ R

/-- The unchanged selected population atlas has one common physical zero-pressure field.
Consequently its integrability budget need only be produced once, for the zero probe. -/
theorem originalPhysicalFinslerRootPressure_zero_probe_eq
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (b : Z × ℝ → M) (f g : M × M →ᵇ ℝ) :
    originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0 =
      originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b g 0 := by
  funext z
  by_cases hz : z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hz
    rw [originalPhysicalFinslerRootPressure_eq_coordinate_on_piece f j 0 hj,
      originalPhysicalFinslerRootPressure_eq_coordinate_on_piece g j 0 hj]
    simp only [zero_mul, originalSeedRootPressure_zero_probe_eq (P j).seed a η₀ η₁ b f g z]
  · exact (disjointRootPressure_eq_zero_of_notMem _ _ hz).trans
      (disjointRootPressure_eq_zero_of_notMem _ _ hz).symm

end OTSelector.Reconstruction
