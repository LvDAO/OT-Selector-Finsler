import OTSelector.Reconstruction.FinslerPopulationWholePairTypes
import OTSelector.Reconstruction.PopulationTypedSubplanCompetitor
import OTSelector.Reconstruction.FinslerPopulationTypedCostData
import OTSelector.Reconstruction.PopulationScalarBinTypes
import OTSelector.Geometry.FinslerFiniteWholePairUpperAtlas
import OTSelector.Geometry.Finsler.DistanceLocalizationSupportBound
import OTSelector.Reconstruction.FinslerRelativeLawSelectedHierarchyMatching

/-!
# Uniform forward geometry across rebuilt calibrated couplings

The whole-pair atlas, scalar bins, type space and two physical cost constants are
chosen from the original geometry before a calibrated population coupling. This
keeps the original small-mass subplan energy constants uniform when the whole
calibrated coupling is rebuilt for a finite-class reference population.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical

noncomputable section
universe u v w
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {E : Type u} {M : Type v} {Z : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Z]
  [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
  {F : ContinuousFinslerNorm E M} {pot : M → ℝ}

/-- The finite whole-pair geometry and cost constants can be fixed before
choosing any calibrated coupling of the original physical populations. -/
theorem exists_uniform_forward_populationTypedCostData_of_calibrated_coupling
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain pot ↦ (a x.val, pot x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain pot, ∀ y ∈ F.potentialRegularDomain pot,
        (a x = a y ∧ pot x ≤ pot y) ↔ pot y - pot x = dist x y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain pot)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain pot)
    : ∃ (T : Type (max u v)) (hT : Fintype T) (C Bnd forwardGap : ℝ),
      let _inst : Fintype T := hT
      0 ≤ C ∧ 0 ≤ Bnd ∧ 0 < forwardGap ∧
      ∀ (π : Measure (M × M)) (hfinite : IsFiniteMeasure π),
        let _inst : IsFiniteMeasure π := hfinite
        Vlasov.IsCoupling π μ ν →
        (let _inst : MetricSpace M := F.metricSpace
          ∀ᵐ p ∂π, pot p.2 - pot p.1 = dist p.1 p.2) →
        ∃ D : PopulationTypedCostData π μ ν T (Module.finrank ℝ E - 1)
          (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x),
          D.quadraticConstant = C ∧ D.globalBound = Bnd ∧
          ∀ t x y, D.sourceGood t x → D.targetGood t y → forwardGap ≤ pot y - pot x := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨δ, R, C, hδ, hR, hC, hgap, J, hJ, P, Q, hQ, hcover, hupper⟩ :=
    hF.exists_finite_wholePair_upperAtlas hcomplete hu hA hB hAB
  let _instFiniteJ : Finite J := hJ
  let _instFintypeJ : Fintype J := Fintype.ofFinite J
  let _instMeasurableOptionJ : MeasurableSpace (Option J) := ⊤
  obtain ⟨Bins⟩ := exists_finiteScalarBins
    ((hA.image hu.continuous).union (hB.image hu.continuous)) hδ
  obtain ⟨Bnd, hBnd, hcost⟩ := F.exists_uniform_compact_distance_slack_bound hA hB hu
  let T := Option J × Fin Bins.count × Fin Bins.count
  refine ⟨T, inferInstance, C, Bnd, δ / 2, hC.le, hBnd.le, by positivity, ?_⟩
  intro π hfinite
  let _instPlanFinite : IsFiniteMeasure π := hfinite
  dsimp only
  intro hπ hcal
  have hpA : ∀ᵐ p ∂π, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (hπ.1.symm ▸ hμA)
  have hpB : ∀ᵐ p ∂π, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (hπ.2.symm ▸ hνB)
  have hpreg : ∀ᵐ p ∂π,
      p.1 ∈ F.potentialRegularDomain pot ∧ p.2 ∈ F.potentialRegularDomain pot := by
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable (hπ.1.symm ▸ hμreg),
      ae_of_ae_map measurable_snd.aemeasurable (hπ.2.symm ▸ hνreg)] with p hx hy
    exact ⟨hx, hy⟩
  obtain ⟨chart, hchart, hchartgood⟩ := exists_measurable_population_seed_assignment P hF
    hcomplete hu ha hinj horder π hpreg (by
      filter_upwards [hpA, hpB, hcal] with p hx hy hc
      obtain ⟨j, z, hz, hzx, hzy, _⟩ := hcover p.1 hx p.2 hy hc
      exact ⟨j, z, hz, hzx, hzy⟩)
  have hscalargap : ∀ᵐ p ∂π, δ ≤ pot p.2 - pot p.1 := by
    filter_upwards [hpA, hpB, hcal] with p hx hy hc
    rw [hc]
    exact hgap p.1 hx p.2 hy
  have hsum := scalarBinPopulationTypes_sum_eq Bins chart pot pot π hchart
    hu.continuous.measurable hu.continuous.measurable (by
      filter_upwards [hpA, hpB] with p hx hy
      exact ⟨Or.inl (mem_image_of_mem pot hx), Or.inr (mem_image_of_mem pot hy)⟩)
  have hbingap := scalarBinPopulationTypes_gap Bins chart pot pot π hchart
    hu.continuous.measurable hu.continuous.measurable hscalargap
  let Types : PopulationSubcouplingTypes π T :=
    scalarBinPopulationTypes Bins chart pot pot π hchart hu.continuous.measurable
      hu.continuous.measurable
  let coord (j : Option J) (x : M) : DyadicUnitCube (Module.finrank ℝ E - 1) :=
    j.elim (PopulationTypedCostData.cubeOrigin) (fun k ↦
      Q k (populationSeedRootLabelValue (P k) a (a x)))
  have hcoord (j : Option J) : Measurable (coord j) := by
    cases j with
    | none => exact measurable_const
    | some j =>
      exact (hQ j).1.measurable.comp
        ((measurable_populationSeedRootLabelValue (P j) hF hcomplete hu ha hinj).comp ha)
  have hcoordpair : ∀ᵐ p ∂π, coord (chart p) p.1 = coord (chart p) p.2 := by
    filter_upwards [hchartgood] with p hp
    obtain ⟨j, hj, hpair⟩ := hp
    simp only [coord, hj, Option.elim_some]
    have he : a p.1 = a p.2 := hpair.2
    rw [he]
  have hpaired (t : T) : ∀ᵐ p ∂Types.component t, coord t.1 p.1 = coord t.1 p.2 := by
    filter_upwards [ae_restrict_of_ae hcoordpair, ae_restrict_mem
      (measurableSet_scalarBinTypeSet Bins chart pot pot hchart hu.continuous.measurable
        hu.continuous.measurable t)] with p hp ht
    have he : chart p = t.1 := ht.1
    rwa [he] at hp
  let Good (K : Set M) (t : T) (bin : Fin Bins.count) (x : M) : Prop :=
    Types.component t univ ≠ 0 ∧ x ∈ K ∧ pot x ∈ Bins.cell bin ∧
      ∃ j, t.1 = some j ∧ x ∈ populationSeedEndpointSet (P j) a
  have hGoodMeas (K : Set M) (hK : MeasurableSet K) (t : T) (bin : Fin Bins.count) :
      MeasurableSet {x | Good K t bin x} := by
    have hE : MeasurableSet {x : M | ∃ j, t.1 = some j ∧
        x ∈ populationSeedEndpointSet (P j) a} := by
      rw [Set.ofPred_exists]
      apply MeasurableSet.iUnion
      intro j
      by_cases hj : t.1 = some j
      · simpa only [hj, true_and, Set.ofPred_mem_eq] using
          measurableSet_populationSeedEndpointSet (P j) hF hcomplete hu ha hinj
      · simp only [hj, false_and, Set.ofPred_false]
        exact MeasurableSet.empty
    by_cases hm : Types.component t univ ≠ 0
    · convert hK.inter ((hu.continuous.measurable (Bins.measurable_cell bin)).inter hE) using 1
      ext x
      change (Types.component t univ ≠ 0 ∧ _) ↔ _
      exact and_iff_right hm
    · simp only [Good, hm, false_and, Set.ofPred_false]
      exact MeasurableSet.empty
  have hgoodSource (t : T) : ∀ᵐ x ∂Types.source t, Good A t t.2.1 x := by
    by_cases hm : Types.component t univ = 0
    · have hz := Measure.measure_univ_eq_zero.mp hm
      simp only [PopulationSubcouplingTypes.source, hz, Measure.map_zero, ae_zero,
        Filter.eventually_bot]
    · apply (ae_map_iff measurable_fst.aemeasurable
        (hGoodMeas A hA.measurableSet t t.2.1)).mpr
      filter_upwards [ae_restrict_of_ae hpA, ae_restrict_of_ae hchartgood,
        ae_restrict_mem (measurableSet_scalarBinTypeSet Bins chart pot pot hchart
          hu.continuous.measurable hu.continuous.measurable t)] with p hpA hpc hpt
      obtain ⟨j, hj, hpj⟩ := hpc
      exact ⟨hm, hpA, hpt.2.1, j, hpt.1.symm.trans hj, hpj.1.1⟩
  have hgoodTarget (t : T) : ∀ᵐ x ∂Types.target t, Good B t t.2.2 x := by
    by_cases hm : Types.component t univ = 0
    · have hz := Measure.measure_univ_eq_zero.mp hm
      simp only [PopulationSubcouplingTypes.target, hz, Measure.map_zero, ae_zero,
        Filter.eventually_bot]
    · apply (ae_map_iff measurable_snd.aemeasurable
        (hGoodMeas B hB.measurableSet t t.2.2)).mpr
      filter_upwards [ae_restrict_of_ae hpB, ae_restrict_of_ae hchartgood,
        ae_restrict_mem (measurableSet_scalarBinTypeSet Bins chart pot pot hchart
          hu.continuous.measurable hu.continuous.measurable t)] with p hpB hpc hpt
      obtain ⟨j, hj, hpj⟩ := hpc
      exact ⟨hm, hpB, hpt.2.2, j, hpt.1.symm.trans hj, hpj.1.2⟩
  refine ⟨{
    types := Types
    sum_eq := hsum
    sourceCoordinate := fun t ↦ coord t.1
    targetCoordinate := fun t ↦ coord t.1
    measurable_sourceCoordinate := fun t ↦ hcoord t.1
    measurable_targetCoordinate := fun t ↦ hcoord t.1
    common_coordinate := scalarBinPopulationTypes_common_label Bins chart pot pot π hchart
      hu.continuous.measurable hu.continuous.measurable coord coord hcoord hcoord hcoordpair
    paired_coordinate := hpaired
    quadraticConstant := C
    globalBound := Bnd
    quadratic_nonneg := hC.le
    bound_nonneg := hBnd.le
    measurable_cost := F.measurable_distance_slack hu
    global_bounds := ?_
    sourceGood := fun t ↦ Good A t t.2.1
    targetGood := fun t ↦ Good B t t.2.2
    source_good := hgoodSource
    target_good := hgoodTarget
    quadratic := ?_ }, rfl, rfl, ?_⟩
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμA,
      Measure.quasiMeasurePreserving_snd.ae hνB] with p hx hy
    exact hcost p.1 hx p.2 hy
  · intro t x y hx hy
    obtain ⟨hm, hxA, hxbin, j, hj, hx⟩ := hx
    obtain ⟨_, hyB, hybin, k, hk, hy⟩ := hy
    have hjk : j = k := Option.some.inj (hj.symm.trans hk)
    subst k
    let wx := populationSeedRootLabelValue (P j) a (a x)
    let wy := populationSeedRootLabelValue (P j) a (a y)
    have hwx : wx ∈ (P j).labels := hx.2.1
    have hwy : wy ∈ (P j).labels := hy.2.1
    have hcx : (P j).curve wx (pot x - (P j).level) = x :=
      (populationSeedPhysicalMap_at_label (P j) ⟨wx, hwx⟩ (pot x)).symm.trans hx.2.2
    have hcy : (P j).curve wy (pot y - (P j).level) = y :=
      (populationSeedPhysicalMap_at_label (P j) ⟨wy, hwy⟩ (pot y)).symm.trans hy.2.2
    have htx := abs_le.mp ((hQ j).2.2 x (Or.inl hxA))
    have hty := abs_le.mp ((hQ j).2.2 y (Or.inr hyB))
    have hxy := hbingap t hm (pot x) hxbin (pot y) hybin
    have h := hupper j wx hwx wy hwy (pot x - (P j).level) (pot y - (P j).level)
      htx.1 hty.2 (by linarith)
    rw [hcx, hcy] at h
    convert h using 1
    · ring
    · simp only [coord, hj, Option.elim_some, wx, wy]
      rw [norm_sub_rev]
      rfl

  · intro t x y hx hy
    exact hbingap t hx.1 (pot x) hx.2.2.1 (pot y) hy.2.2.1

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction.PopulationTypedCostData
open Set Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ}
  (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]

/-- Every same-original-type sampled edge retains its actual scalar forward
gap, simultaneously for all indices, before any optimizer is chosen. -/
theorem iid_same_type_forward
    (clockS : X → ℝ) (clockT : Y → ℝ) (gap : ℝ)
    (hforward : ∀ t x y, D.sourceGood t x → D.targetGood t y → gap ≤ clockT y - clockS x)
    (n : ℕ) :
    ∀ᵐ sample ∂D.markedLaw n, ∀ i j t,
      (sample.1 i).2 = some t → (sample.2 j).2 = some t →
      gap ≤ clockT (sample.2 j).1 - clockS (sample.1 i).1 := by
  have hg := D.types.iid_marked_type_properties (μ := μ) (ν := ν)
    (I := Fin n) (J := Fin n) D.sourceGood D.targetGood D.source_good D.target_good
  filter_upwards [hg] with sample hsample
  exact fun i j t hi hj ↦ hforward t _ _ (hsample.1 i t hi) (hsample.2 j t hj)

omit [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)] in
/-- A selected same-type hierarchy piece of the prescribed original subplan
retains the original forward gap. This holds for every full assignment on the
same original sample and introduces no law for adaptive unmatched points. -/
theorem refineSubplan_selectedSameTypeMatching_forward
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (clockS : X → ℝ) (clockT : Y → ℝ) (gap : ℝ)
    (hforward : ∀ t x y, D.sourceGood t x → D.targetGood t y → gap ≤ clockT y - clockS x)
    (η : Measure (X × Y)) (hη : η ≤ π) (n : ℕ) :
    let R := D.refineSubplan η hη
    ∀ᵐ sample ∂R.markedLaw n, ∀ full : Assignment n,
      ∀ e ∈ (selectedSameTypeMatching (selectedSubplanTags (T := T))
        (fun i ↦ (R.sourceSample n i sample).1)
        (fun j ↦ (R.targetSample n j sample).1) full).edges,
      gap ≤ clockT (sample.2 e.2).1 - clockS (sample.1 e.1).1 := by
  classical
  let R := D.refineSubplan η hη
  have hforwardR : ∀ t x y, R.sourceGood t x → R.targetGood t y →
      gap ≤ clockT y - clockS x := fun t x y hx hy ↦ hforward t.2 x y hx hy
  have hg := R.iid_same_type_forward clockS clockT gap hforwardR n
  filter_upwards [hg] with sample hsample
  intro full e he
  have hmem := selectedSameTypeMatching_mem (selectedSubplanTags (T := T))
    (fun i ↦ (R.sourceSample n i sample).1) (fun j ↦ (R.targetSample n j sample).1) full he
  change (sample.1 e.1).2 ∈ selectedSubplanTags ∧
    (sample.2 e.2).2 ∈ selectedSubplanTags ∧ (sample.1 e.1).2 = (sample.2 e.2).2 at hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem.1
  exact hsample e.1 e.2 (true, t) ht.symm (hmem.2.2.symm.trans ht.symm)

end OTSelector.Reconstruction.PopulationTypedCostData
