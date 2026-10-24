import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCellOptimizerIntegrability
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentFineModelIntegral
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelIntegrability
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelObservable

/-! Actual dependent frozen-model means are integrable on the unchanged old RN experiment. -/
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

/-- Actual compact original labels supply integrability of both canonical model means.
The fine legal value is exactly the old-RN canonical model score on average,
with no integrability or selected-cloud law premise. -/
theorem PopulationLocalPressureCore.original_dependent_clockClass_model_mean
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {I : Set ℝ} {gap : ℝ}
    {C T : Type*} [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (coreIndex : C → Fin D.haar.continuous.count)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (Q : C → FiniteScalarBins I gap)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count)
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
    let legal := fun c ↦ D.originalClockClassAllowed (coreIndex c) (Q c) (classify c)
    let model := fun c x y ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c) x y +
      tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f x y
    let oldModelValue := fun sample ↦ ∑ c, (originalRetainedCellOptimizer a cell
      (originalSubplanPhysicalGraph legal) (fun c sample j k ↦ model c (sample.1 j).1 (sample.2 k).1)
      c sample).cost (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)
    let fineLegalValue := fun (sample : (Fin n → M × Option (CellRefinedType C T)) ×
        (Fin n → M × Option (CellRefinedType C T))) ↦ ∑ c, PartialMatching.legalMaximumValue
      (Finset.univ.filter (fun e : Fin n × Fin n ↦
        fineOriginalRetainedCellTag a cell (sample.1 e.1) = some c ∧
        fineOriginalRetainedCellTag a cell (sample.2 e.2) = some c ∧
        legal c (sample.1 e.1).1 (sample.2 e.2).1))
      (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)
    Integrable oldModelValue (Refined.markedLaw n) ∧ Integrable fineLegalValue P ∧
      (∫ sample, fineLegalValue sample ∂P) = ∫ sample, oldModelValue sample ∂Refined.markedLaw n := by
  let R := Cst.types.rnCellRefinedTypes η hη good bad hsplit
  let law := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  let legal := fun c ↦ D.originalClockClassAllowed (coreIndex c) (Q c) (classify c)
  let model := fun c x y ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
    D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c) x y +
    tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f x y
  let fineLegalValue := fun (sample : (Fin n → M × Option (CellRefinedType C T)) ×
      (Fin n → M × Option (CellRefinedType C T))) ↦ ∑ c, PartialMatching.legalMaximumValue
    (Finset.univ.filter (fun e : Fin n × Fin n ↦
      fineOriginalRetainedCellTag a cell (sample.1 e.1) = some c ∧
      fineOriginalRetainedCellTag a cell (sample.2 e.2) = some c ∧
      legal c (sample.1 e.1).1 (sample.2 e.2).1))
    (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)
  have hi : Integrable fineLegalValue law := by
    apply integrable_finsetSum
    intro c _
    have hsource : ∀ᵐ sample ∂law, ∀ j,
        fineOriginalRetainedCellTag a cell (sample.1 j) = some c →
          a (sample.1 j).1 ∈ (D.haar.continuous.coefficient (coreIndex c)).roots := by
      exact Filter.Eventually.of_forall fun sample j hj ↦
        hsub c ((fineOriginalRetainedCellTag_eq_some_iff a cell hdisj _ c).mp hj).2
    have htarget : ∀ᵐ sample ∂law, ∀ k,
        fineOriginalRetainedCellTag a cell (sample.2 k) = some c →
          a (sample.2 k).1 ∈ (D.haar.continuous.coefficient (coreIndex c)).roots := by
      exact Filter.Eventually.of_forall fun sample k hk ↦
        hsub c ((fineOriginalRetainedCellTag_eq_some_iff a cell hdisj _ c).mp hk).2
    have hI := D.integrable_originalClockClass_legalValue hF hcomplete hu ha hinj
      (coreIndex c) (Q c) (reference c) (classify c) (hclassify c) f law
      (fun j sample ↦ (sample.1 j).1) (fun k sample ↦ (sample.2 k).1)
      (fun _ ↦ by fun_prop) (fun _ ↦ by fun_prop)
      (fun sample j ↦ fineOriginalRetainedCellTag a cell (sample.1 j) = some c)
      (fun sample k ↦ fineOriginalRetainedCellTag a cell (sample.2 k) = some c)
      (fun j ↦ measurableSet_fineOriginalRetainedCellTag_eq_some a ha cell hcell hdisj
        (fun sample : (Fin n → M × Option (CellRefinedType C T)) ×
          (Fin n → M × Option (CellRefinedType C T)) ↦ sample.1 j) (by fun_prop) c)
      (fun k ↦ measurableSet_fineOriginalRetainedCellTag_eq_some a ha cell hcell hdisj
        (fun sample : (Fin n → M × Option (CellRefinedType C T)) ×
          (Fin n → M × Option (CellRefinedType C T)) ↦ sample.2 k) (by fun_prop) c)
      hsource htarget (scale := (n : ℝ) ^ (2 / (q : ℝ)))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) tilt
    convert hI using 1
    · rfl
    · funext sample
      dsimp only [legal, model]
      congr 1
      ext e
      simp only [Finset.mem_filter]
  have htransfer := D.original_dependent_clockClass_fine_model_integral hF hcomplete hu ha hinj
    coreIndex reference Q cell hcell hdisj classify hclassify f hπ Cst η hη good bad hsplit n tilt
  have hvalue : (fun sample ↦ ∑ c, (PartialMatching.firstLegalOptimalMatching
        (originalAmbientCellLegalGraph (fun j ↦ fineOriginalRetainedCellTag a cell (sample.1 j))
          (fun k ↦ fineOriginalRetainedCellTag a cell (sample.2 k)) (originalFinePhysicalGraph legal sample) c)
        (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)).cost
        (fun j k ↦ model c (sample.1 j).1 (sample.2 k).1)) = fineLegalValue := by
    funext sample
    apply Finset.sum_congr rfl
    intro c _
    rw [(PartialMatching.firstLegalOptimalMatching_isLegalOptimal _ _).2.2]
    congr 1
    ext e
    simp only [originalAmbientCellLegalGraph, originalFinePhysicalGraph,
      Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  dsimp only at htransfer ⊢
  change (Integrable _ law ↔ Integrable _ _) ∧ _ at htransfer
  rw [hvalue] at htransfer
  exact ⟨htransfer.1.mp hi, hi, htransfer.2⟩

end OTSelector.Reconstruction
