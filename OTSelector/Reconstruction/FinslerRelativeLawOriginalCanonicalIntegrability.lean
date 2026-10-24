import OTSelector.Reconstruction.FinslerRelativeLawActualMicrocellShapeExpectation
import OTSelector.Reconstruction.FinslerConcreteUpperForwardCoreBound

/-! Actual compact seed labels bound original canonical costs before class-law normalization. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- Only used edges need a bound to integrate the cost of a measurable finite
matching. The selected endpoints may depend on the whole sample. -/
theorem integrable_matching_cost_of_used_edge_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {m n : ℕ}
    (σ : Ω → OTSelector.PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {sample | e ∈ (σ sample).edges})
    (cost : Ω → Fin m → Fin n → ℝ) (hm : ∀ i j, Measurable (fun sample ↦ cost sample i j))
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hb : ∀ᵐ sample ∂P, ∀ e ∈ (σ sample).edges, |cost sample e.1 e.2| ≤ bound) :
    Integrable (fun sample ↦ (σ sample).cost (cost sample)) P := by
  classical
  have heq : (fun sample ↦ (σ sample).cost (cost sample)) = fun sample ↦
      ∑ e : Fin m × Fin n, if e ∈ (σ sample).edges then cost sample e.1 e.2 else 0 := by
    funext sample
    exact OTSelector.PartialMatching.cost_eq_sum_edgeIndicator _ _
  rw [heq]
  apply integrable_finsetSum
  intro e _
  have hmeas : Measurable (fun sample ↦ if e ∈ (σ sample).edges then cost sample e.1 e.2 else 0) :=
    (hm e.1 e.2).ite (hσ e) measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable bound
  filter_upwards [hb] with sample hs
  by_cases he : e ∈ (σ sample).edges
  · simpa only [ite_eq_left he, Real.norm_eq_abs] using hs e he
  · simpa only [ite_eq_right he, norm_zero] using hbound

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

/-- Actual compact original seed labels give integrability of every retained
canonical class cost. No normalized point law, positive subcell mass or iid
law for selected endpoints is needed. -/
theorem PopulationLocalPressureCore.original_canonical_seed_cost_integrable
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
    {T : Type*} [Fintype T] {qAtlas : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T qAtlas cost)
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (ξ : Measure (M × M)) (hξ : ξ ≤ πWhole) (N : ℕ) (scale tilt : ℝ) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    Integrable (originalRetainedSeedClassCost a L (fun x ↦ R (a x)) e.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      scale (C.clockClassKinetic Q z₀.val) (C.clockClassProbe Q z₀.val z₀.property f) tilt)
      ((Cst.refineSubplan ξ hξ).markedLaw N) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let R := populationSeedRootLabelValue S a
  let Refined := Cst.refineSubplan ξ hξ
  letI : IsProbabilityMeasure (Refined.markedLaw N) := (Refined.iid_facts hπWhole N).1
  let extra := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
    C.clockClassAllowed Q (classify (u (sample.1 jk.1).1)) (classify (u (sample.2 jk.2).1)))
  let score := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) j k ↦ scale * C.clockClassKinetic Q z₀.val
      (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
      (e (R (a (sample.2 k).1) - R (a (sample.1 j).1))) +
      tilt * C.clockClassProbe Q z₀.val z₀.property f
        (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
  let σ := originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra score ()
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have huM : Measurable u := hu.continuous.measurable
  have hmodel : ∀ (_c : Unit) j k, Measurable (fun sample ↦ score _c sample j k) := by
    intro _ j k
    have hs : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦ classify (u (sample.1 j).1)) := by fun_prop
    have ht : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦ classify (u (sample.2 k).1)) := by fun_prop
    have hv : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦ e (R (a (sample.2 k).1) - R (a (sample.1 j).1))) := by fun_prop
    exact (((C.measurable_clockClassKinetic Q z₀.val).comp ((hs.prodMk ht).prodMk hv)).const_mul scale).add
      (((C.measurable_clockClassProbe Q z₀.val z₀.property f).comp (hs.prodMk ht)).const_mul tilt)
  have hextra : ∀ (_c : Unit) V, MeasurableSet {sample | extra _c sample = V} := by
    intro _ V
    have hclasses : Measurable (fun sample : (Fin N → M × Option (Bool × T)) ×
        (Fin N → M × Option (Bool × T)) ↦
      ((fun j : Fin N ↦ classify (u (sample.1 j).1)), (fun k : Fin N ↦ classify (u (sample.2 k).1)))) := by fun_prop
    exact ((measurable_of_countable (fun classes : (Fin N → Fin Q.count) × (Fin N → Fin Q.count) ↦
      Finset.univ.filter (fun jk : Fin N × Fin N ↦ C.clockClassAllowed Q (classes.1 jk.1) (classes.2 jk.2)))).comp hclasses)
        (measurableSet_singleton V)
  have hσ := measurableSet_mem_originalRetainedCellOptimizer a ha (fun _ : Unit ↦ L) (fun _ ↦ hL)
    extra hextra score hmodel ()
  obtain ⟨edgeBound, hEdge, hbound⟩ := D.exists_original_clockClass_pair_bound i Q z₀
  apply integrable_matching_cost_of_used_edge_bound (Refined.markedLaw N) σ hσ (score ()) (hmodel ())
    (|scale| * edgeBound + |tilt| * ‖f‖) (by positivity)
  apply Filter.Eventually.of_forall
  intro sample jk hjk
  have hs := originalRetainedCellOptimizer_support a (fun _ : Unit ↦ L) extra score () sample jk hjk
  calc
    |score () sample jk.1 jk.2| ≤
      |scale| * |C.clockClassKinetic Q z₀.val
        (classify (u (sample.1 jk.1).1)) (classify (u (sample.2 jk.2).1))
        (e (R (a (sample.2 jk.2).1) - R (a (sample.1 jk.1).1)))| +
      |tilt| * |C.clockClassProbe Q z₀.val z₀.property f
        (classify (u (sample.1 jk.1).1)) (classify (u (sample.2 jk.2).1))| := by
      dsimp only [score]
      rw [← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    _ ≤ |scale| * edgeBound + |tilt| * ‖f‖ := add_le_add
      (mul_le_mul_of_nonneg_left (hbound _ _ _ (hsub hs.2.2.2.1) _ (hsub hs.2.2.2.2)) (abs_nonneg scale))
      (mul_le_mul_of_nonneg_left (C.clockClassProbe_abs_le Q z₀.val z₀.property f _ _) (abs_nonneg tilt))

end OTSelector.Reconstruction
