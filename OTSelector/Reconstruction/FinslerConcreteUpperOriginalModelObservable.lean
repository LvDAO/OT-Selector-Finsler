import OTSelector.Reconstruction.FinslerConcreteUpperClassGeometry
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

/-- The literal model graph read from unchanged original physical clocks. -/
def originalClockClassAllowed
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : FiniteScalarBins I gap) (classify : ℝ → Fin Q.count) (x y : M) : Prop :=
  (D.haar.continuous.coefficient i).clockClassAllowed Q (classify (u x)) (classify (u y))

/-- Actual fixed coefficient kinetic energy in the original seed coordinates. -/
def originalClockClassKinetic
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (classify : ℝ → Fin Q.count) (x y : M) : ℝ :=
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  C.clockClassKinetic Q ref.val (classify (u x)) (classify (u y))
    ((Module.finBasis ℝ S.covector.ker).equivFun (R (a y) - R (a x)))

/-- The original physical probe frozen at the same actual reference classes. -/
def originalClockClassProbe
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (classify : ℝ → Fin Q.count) (f : M × M →ᵇ ℝ) (x y : M) : ℝ :=
  (D.haar.continuous.coefficient i).clockClassProbe Q ref.val ref.property f
    (classify (u x)) (classify (u y))

/-- The actual graph and frozen score are measurable on original physical
pairs. Original Lipschitz clocks and seed labels discharge both coordinate
measurability inputs; the finite classifier is kept unchanged. -/
theorem measurable_originalClockClass_model
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (classify : ℝ → Fin Q.count) (hclassify : Measurable classify) (f : M × M →ᵇ ℝ) :
    MeasurableSet {p : M × M | D.originalClockClassAllowed i Q classify p.1 p.2} ∧
    Measurable (fun p : M × M ↦ D.originalClockClassKinetic i Q ref classify p.1 p.2) ∧
    Measurable (fun p : M × M ↦ D.originalClockClassProbe i Q ref classify f p.1 p.2) ∧
    ∀ scale tilt : ℝ, Measurable (fun p : M × M ↦
      scale * D.originalClockClassKinetic i Q ref classify p.1 p.2 +
      tilt * D.originalClockClassProbe i Q ref classify f p.1 p.2) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let bW := Module.finBasis ℝ S.covector.ker
  have hum : Measurable u := hu.continuous.measurable
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hpoint : Measurable (fun p : M × M ↦ (classify (u p.1), classify (u p.2))) :=
    ((hclassify.comp hum).comp measurable_fst).prodMk ((hclassify.comp hum).comp measurable_snd)
  have hvec : Measurable (fun p : M × M ↦ bW.equivFun (R (a p.2) - R (a p.1))) :=
    bW.equivFunL.continuous.measurable.comp
      ((hR.comp (ha.comp measurable_snd)).sub (hR.comp (ha.comp measurable_fst)))
  have hkin : Measurable (fun p : M × M ↦ D.originalClockClassKinetic i Q ref classify p.1 p.2) :=
    (C.measurable_clockClassKinetic Q ref.val).comp (hpoint.prodMk hvec)
  have hprobe : Measurable (fun p : M × M ↦ D.originalClockClassProbe i Q ref classify f p.1 p.2) :=
    (C.measurable_clockClassProbe Q ref.val ref.property f).comp hpoint
  refine ⟨?_, hkin, hprobe, fun scale tilt ↦ (hkin.const_mul scale).add (hprobe.const_mul tilt)⟩
  exact hpoint ((Set.toFinite {p : Fin Q.count × Fin Q.count | C.clockClassAllowed Q p.1 p.2}).measurableSet)

end OTSelector.Reconstruction.PopulationLocalPressureCore
