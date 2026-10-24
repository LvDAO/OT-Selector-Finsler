import OTSelector.Reconstruction.FinslerConcreteUpperForwardCoreBound
/-! The physical forward-core upper estimate applies to the exact Q/U choices
already used by the original population and its canonical optimizer. -/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
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

/-- Arbitrary retained geometry choices are consumed without reselecting the
bins, reference neighborhoods, or original population split. The unscaled edge
constant is produced internally from the original compact seed labels. -/
theorem original_endpoint_clockClass_allowed_of_geometry
    (i : Fin D.haar.continuous.count)
    {A B : Set M} {I : Set ℝ} {globalGap : ℝ}
    (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I globalGap)
    (U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (houter : ∀ ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k →
      ∀ s ∈ (Q ref).cell j, ∀ t ∈ (Q ref).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1)
    (hregion : ∀ ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient i).window.region)
    (ref : (D.haar.continuous.coefficient i).roots)
    (x y : M) (j k : Fin (Q ref).count)
    (hx : a x ∈ (D.haar.continuous.coefficient i).roots ∩ U ref)
    (hy : a y ∈ (D.haar.continuous.coefficient i).roots ∩ U ref)
    (hs : u x ∈ (Q ref).cell j) (ht : u y ∈ (Q ref).cell k)
    (hactiveS : ∃ l, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j l)
    (hactiveT : ∃ l, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) l k)
    (hrestoreS : D.corePoint i (a x, u x) = x)
    (hrestoreT : D.corePoint i (a y, u y) = y)
    (hA : x ∈ A) (hB : y ∈ B) (hforward : u x < u y) :
    (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k := by
  let C := D.haar.continuous.coefficient i
  have hSouter : u x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    obtain ⟨l, hl⟩ := hactiveS
    have hp := C.clockClassReference_mem (Q ref) hl
    exact (houter ref j l hl (u x) hs _ hp.2.2).1
  have hTouter : u y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    obtain ⟨l, hl⟩ := hactiveT
    have hp := C.clockClassReference_mem (Q ref) hl
    exact (houter ref l k hl _ hp.2.1 (u y) ht).2
  exact ⟨(u x, u y), hregion ref (a x) hx (a y) hy (u x) hSouter (u y) hTouter
    hforward (hrestoreS.symm ▸ hA) (hrestoreT.symm ▸ hB), hs, ht⟩

end OTSelector.Reconstruction.PopulationLocalPressureCore
