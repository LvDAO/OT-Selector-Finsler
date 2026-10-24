import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelCoreBounds
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

/-- The actual SAME-choice raw coefficient and probe geometry compares
original physical tilted edges with their literal frozen model edges. -/
theorem originalClockClass_score_le_of_geometry
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {A B : Set M} {gap ρ probeError : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (U : Set (ℚ → M)) (f : M × M →ᵇ ℝ) (hρ : 0 ≤ ρ)
    (hgeometry : ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U,
      ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed Q j k →
      ∀ s ∈ Q.cell j, ∀ t ∈ Q.cell k,
      D.corePoint i (z,s) ∈ A → D.corePoint i (z',t) ∈ B →
      let C := D.haar.continuous.coefficient i
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      (s,t) ∈ C.window.region ∧
      |populationSeedPairDeficit S (s,t) (R z,R z') -
        C.clockClassKinetic Q ref.val j k ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z))| ≤
        ρ * C.clockClassKinetic Q ref.val j k ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z)) ∧
      |f (D.corePoint i (z,s),D.corePoint i (z',t)) -
        C.clockClassProbe Q ref.val ref.property f j k| ≤ 2 * probeError)
    (classify : ℝ → Fin Q.count) (x y : M)
    (hx : a x ∈ (D.haar.continuous.coefficient i).roots ∩ U)
    (hy : a y ∈ (D.haar.continuous.coefficient i).roots ∩ U)
    (hs : u x ∈ Q.cell (classify (u x))) (ht : u y ∈ Q.cell (classify (u y)))
    (hlegal : D.originalClockClassAllowed i Q classify x y)
    (hrestoreS : D.corePoint i (a x,u x) = x)
    (hrestoreT : D.corePoint i (a y,u y) = y) (hA : x ∈ A) (hB : y ∈ B)
    {scale : ℝ} (hscale : 0 ≤ scale) (tilt : ℝ) :
    scale * ((F.lengthEDist x y).toReal - u y + u x) + tilt * f (x,y) ≤
      (1+ρ) * (scale * D.originalClockClassKinetic i Q ref classify x y +
        tilt * D.originalClockClassProbe i Q ref classify f x y) +
      (|tilt| * (2 * probeError) + ρ * (|tilt| * ‖f‖)) := by
  obtain ⟨_,hk,hp⟩ := hgeometry (a x) hx (a y) hy (classify (u x)) (classify (u y)) hlegal
    (u x) hs (u y) ht (hrestoreS.symm ▸ hA) (hrestoreT.symm ▸ hB)
  rw [D.original_endpoint_seedPairDeficit_eq i x y hrestoreS hrestoreT] at hk
  rw [hrestoreS,hrestoreT] at hp
  change |((F.lengthEDist x y).toReal - u y + u x) - D.originalClockClassKinetic i Q ref classify x y| ≤
    ρ * D.originalClockClassKinetic i Q ref classify x y at hk
  change |f (x,y) - D.originalClockClassProbe i Q ref classify f x y| ≤ 2 * probeError at hp
  have hkupper := mul_le_mul_of_nonneg_left (abs_le.mp hk).2 hscale
  have hprobe : tilt * (f (x,y) - D.originalClockClassProbe i Q ref classify f x y) ≤
      |tilt| * (2 * probeError) := by
    calc _ ≤ |tilt * (f (x,y) - D.originalClockClassProbe i Q ref classify f x y)| := le_abs_self _
      _ = |tilt| * |f (x,y) - D.originalClockClassProbe i Q ref classify f x y| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  have hmodel : -tilt * D.originalClockClassProbe i Q ref classify f x y ≤ |tilt| * ‖f‖ := by
    calc _ ≤ |-tilt * D.originalClockClassProbe i Q ref classify f x y| := le_abs_self _
      _ = |tilt| * |D.originalClockClassProbe i Q ref classify f x y| := by rw [abs_mul,abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((D.haar.continuous.coefficient i).clockClassProbe_abs_le Q ref.val ref.property f _ _) (abs_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hmodel hρ
  nlinarith only [hkupper,hprobe,hscaled]

end OTSelector.Reconstruction.PopulationLocalPressureCore
