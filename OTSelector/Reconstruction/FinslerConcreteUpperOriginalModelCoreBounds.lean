import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelObservable
import OTSelector.Reconstruction.FinslerConcreteUpperForwardCoreBound
/-! The physical forward-core upper estimate applies to the exact Q/U choices
already used by the original population and its canonical optimizer. -/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace OTSelector.Reconstruction.PopulationLocalPressureCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Actual endpoint restoration identifies the seed deficit with the unchanged
original physical length deficit. -/
theorem original_endpoint_seedPairDeficit_eq
    (i : Fin D.haar.continuous.count) (x y : M)
    (hx : D.corePoint i (a x, u x) = x) (hy : D.corePoint i (a y, u y) = y) :
    let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
    let R := populationSeedRootLabelValue S a
    populationSeedPairDeficit S (u x, u y) (R (a x), R (a y)) =
      (F.lengthEDist x y).toReal - u y + u x := by
  dsimp only
  dsimp only [PopulationLocalPressureCore.corePoint] at hx hy
  dsimp only [populationSeedPairDeficit]
  rw [hx, hy]

/-- The same actual raw Taylor geometry controls the literal physical model
readout on restored original endpoints, including the inverse kinetic bound. -/
theorem originalClockClassKinetic_comparison_of_geometry
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {A B : Set M} {gap ρ : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (U : Set (ℚ → M)) (hρ : ρ < 1)
    (hgeometry : ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U,
      ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed Q j k →
      ∀ s ∈ Q.cell j, ∀ t ∈ Q.cell k,
      D.corePoint i (z,s) ∈ A → D.corePoint i (z',t) ∈ B →
      let C := D.haar.continuous.coefficient i
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      |populationSeedPairDeficit S (s,t) (R z,R z') -
        C.clockClassKinetic Q ref.val j k ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z))| ≤
        ρ * C.clockClassKinetic Q ref.val j k ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z)))
    (classify : ℝ → Fin Q.count) (x y : M)
    (hx : a x ∈ (D.haar.continuous.coefficient i).roots ∩ U)
    (hy : a y ∈ (D.haar.continuous.coefficient i).roots ∩ U)
    (hs : u x ∈ Q.cell (classify (u x))) (ht : u y ∈ Q.cell (classify (u y)))
    (hlegal : D.originalClockClassAllowed i Q classify x y)
    (hrestoreS : D.corePoint i (a x,u x) = x)
    (hrestoreT : D.corePoint i (a y,u y) = y) (hA : x ∈ A) (hB : y ∈ B) :
    |((F.lengthEDist x y).toReal - u y + u x) - D.originalClockClassKinetic i Q ref classify x y| ≤
        ρ * D.originalClockClassKinetic i Q ref classify x y ∧
    D.originalClockClassKinetic i Q ref classify x y ≤
      ((F.lengthEDist x y).toReal - u y + u x) / (1-ρ) := by
  have h := hgeometry (a x) hx (a y) hy (classify (u x)) (classify (u y)) hlegal
    (u x) hs (u y) ht (hrestoreS.symm ▸ hA) (hrestoreT.symm ▸ hB)
  dsimp only at h
  rw [D.original_endpoint_seedPairDeficit_eq i x y hrestoreS hrestoreT] at h
  change |((F.lengthEDist x y).toReal - u y + u x) - D.originalClockClassKinetic i Q ref classify x y| ≤
    ρ * D.originalClockClassKinetic i Q ref classify x y at h
  refine ⟨h, (le_div_iff₀ (sub_pos.mpr hρ)).mpr ?_⟩
  have hlow := (abs_le.mp h).1
  nlinarith only [hlow]

/-- The actual compact seed labels produce every unscaled physical model edge
bound before empirical order or tilt is chosen. -/
theorem exists_originalClockClass_physical_edge_bound
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (classify : ℝ → Fin Q.count) (f : M × M →ᵇ ℝ) :
    ∃ B ≥ 0, ∀ x y, a x ∈ (D.haar.continuous.coefficient i).roots →
      a y ∈ (D.haar.continuous.coefficient i).roots → ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
      |scale * D.originalClockClassKinetic i Q ref classify x y +
        tilt * D.originalClockClassProbe i Q ref classify f x y| ≤ scale * B + |tilt| * ‖f‖ := by
  obtain ⟨B,hB,hbound⟩ := D.exists_original_clockClass_pair_bound i Q ref
  refine ⟨B,hB,?_⟩
  intro x y hx hy scale hscale tilt
  have hk := hbound (classify (u x)) (classify (u y)) (a x) hx (a y) hy
  have hp := (D.haar.continuous.coefficient i).clockClassProbe_abs_le Q ref.val ref.property f
    (classify (u x)) (classify (u y))
  calc _ ≤ |scale * D.originalClockClassKinetic i Q ref classify x y| +
      |tilt * D.originalClockClassProbe i Q ref classify f x y| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hscale, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hk hscale)
        (mul_le_mul_of_nonneg_left hp (abs_nonneg _))

end OTSelector.Reconstruction.PopulationLocalPressureCore
