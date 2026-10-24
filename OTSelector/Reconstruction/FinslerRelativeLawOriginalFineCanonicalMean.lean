import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalIntegrability
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineResidualEnergy

/-! Actual retained canonical frozen means are preserved on the same fine original experiment. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)} [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual original canonical retained cost is integrable on the fine good/bad sample,
with exactly its original residual-marked mean. All physical endpoints and indices are unchanged. -/
theorem PopulationLocalPressureCore.original_fine_canonical_seed_cost_integral
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (z₀ : (D.haar.continuous.coefficient i).roots)
    (f : M × M →ᵇ ℝ) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (classify : ℝ → Fin Q.count) (hm : Measurable classify)
    {πWhole : Measure (M × M)} [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    {T Parts : Type*} [Fintype T] [Fintype Parts] {qAtlas : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T qAtlas cost)
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType Parts T))]
    [MeasurableSingletonClass (Option (CellRefinedType Parts T))]
    (ξ : Measure (M × M)) (hξ : ξ ≤ πWhole)
    (good : T → Measure (M × M)) (bad : Parts → T → Measure (M × M))
    (hsplit : ∀ t, good t + ∑ c, bad c t =
      (Cst.types.rnSubplanTypes ξ hξ).component (false, t))
    (N : ℕ) (scale tilt : ℝ) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let score := originalRetainedSeedClassCost (T := T) (N := N) a L (fun x ↦ R (a x)) e.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      scale (C.clockClassKinetic Q z₀.val) (C.clockClassProbe Q z₀.val z₀.property f) tilt
    let Fine := Cst.types.rnCellRefinedTypes ξ hξ good bad hsplit
    let law := (Measure.pi (fun _ : Fin N ↦ Fine.sourceMarkedLaw η₀)).prod
      (Measure.pi (fun _ : Fin N ↦ Fine.targetMarkedLaw η₁))
    Integrable (fun sample ↦ score (cellRefinedSubplanObservation sample)) law ∧
      (∫ sample, score (cellRefinedSubplanObservation sample) ∂law) =
        ∫ sample, score sample ∂(Cst.refineSubplan ξ hξ).markedLaw N := by
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let R := populationSeedRootLabelValue S a
  let score := originalRetainedSeedClassCost (T := T) (N := N) a L (fun x ↦ R (a x)) e.toLinearMap
    (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
    scale (C.clockClassKinetic Q z₀.val) (C.clockClassProbe Q z₀.val z₀.property f) tilt
  let Fine := Cst.types.rnCellRefinedTypes ξ hξ good bad hsplit
  let law := (Measure.pi (fun _ : Fin N ↦ Fine.sourceMarkedLaw η₀)).prod
    (Measure.pi (fun _ : Fin N ↦ Fine.targetMarkedLaw η₁))
  have hi := D.original_canonical_seed_cost_integrable hF hcomplete hu ha hinj i Q z₀ f
    hL hsub classify hm hπWhole Cst ξ hξ N scale tilt
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
  have hlaw : law.map cellRefinedSubplanObservation = (Cst.refineSubplan ξ hξ).markedLaw N :=
    Cst.types.rnCellRefinedTypes_iid_subplan_law ξ hξ good bad hsplit η₀ η₁
  have hobs := measurable_cellRefinedSubplanObservation (X := M) (Y := M)
    (C := Parts) (T := T) (I := Fin N) (J := Fin N)
  have hmapI : Integrable score (law.map cellRefinedSubplanObservation) := by
    rw [hlaw]
    exact hi
  refine ⟨hmapI.comp_measurable hobs, ?_⟩
  rw [← integral_map hobs.aemeasurable hmapI.aestronglyMeasurable, hlaw]

end OTSelector.Reconstruction
