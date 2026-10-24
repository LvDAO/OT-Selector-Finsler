import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCellDefect
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCanonicalObservable
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelObservable

/-! The actual original frozen class-model observable has one unchanged old-RN canonical mean. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The literal original model score and canonical graph are unchanged when
compact good/bad marks are forgotten. All model measurability and complete-mark
conditions are discharged from original data. The old mean is independent of
compact colors and their loss tolerance. -/
theorem PopulationLocalPressureCore.original_clockClass_fine_model_integral
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
    {C T : Type*} [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (reference : C → (D.haar.continuous.coefficient i).roots)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (classify : ∀ c, ℝ → Fin (Q (reference c)).count)
    (hclassify : ∀ c, Measurable (classify c)) (f : M × M →ᵇ ℝ)
    {π : Measure (M × M)} [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    {q : ℕ} {cost : M → M → ℝ} (Cst : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (M × M)) (hη : η ≤ π)
    (good : T → Measure (M × M)) (bad : C → T → Measure (M × M))
    (hsplit : ∀ t, good t + ∑ c, bad c t =
      (Cst.types.rnSubplanTypes η hη).component (false,t)) (n : ℕ) (tilt : ℝ) :
    let R := Cst.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let Refined := Cst.refineSubplan η hη
    let legal := fun c ↦ D.originalClockClassAllowed i (Q (reference c)) (classify c)
    let model := fun c x y ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic i (Q (reference c)) (reference c) (classify c) x y +
      tilt * D.originalClockClassProbe i (Q (reference c)) (reference c) (classify c) f x y
    let oldModelValue := fun sample ↦ ∑ c, (originalRetainedCellOptimizer a cell
      (originalSubplanPhysicalGraph legal) (fun c sample j k ↦ model c (sample.1 j).1 (sample.2 k).1)
      c sample).cost (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)
    let fineModelValue := fun sample ↦ ∑ c, (PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph (fun j ↦ fineOriginalRetainedCellTag a cell (sample.1 j))
        (fun k ↦ fineOriginalRetainedCellTag a cell (sample.2 k)) (originalFinePhysicalGraph legal sample) c)
      (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)).cost
      (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)
    (Integrable fineModelValue P ↔ Integrable oldModelValue (Refined.markedLaw n)) ∧
      (∫ sample, fineModelValue sample ∂P) = ∫ sample, oldModelValue sample ∂Refined.markedLaw n := by
  have hm c := D.measurable_originalClockClass_model hF hcomplete hu ha hinj
    i (Q (reference c)) (reference c) (classify c) (hclassify c) f
  exact Cst.rnCellRefinedTypes_canonical_observable_integral η hη good bad hsplit hπ n
    a ha cell hcell hdisj
    (fun c ↦ D.originalClockClassAllowed i (Q (reference c)) (classify c)) (fun c ↦ (hm c).1)
    (fun c x y ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic i (Q (reference c)) (reference c) (classify c) x y +
      tilt * D.originalClockClassProbe i (Q (reference c)) (reference c) (classify c) f x y)
    (fun c ↦ (hm c).2.2.2 _ tilt)
    (fun c x y ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic i (Q (reference c)) (reference c) (classify c) x y +
      tilt * D.originalClockClassProbe i (Q (reference c)) (reference c) (classify c) f x y)
    (fun c ↦ (hm c).2.2.2 _ tilt)

end OTSelector.Reconstruction
