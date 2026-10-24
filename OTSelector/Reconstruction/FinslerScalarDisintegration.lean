import OTSelector.Geometry.Finsler.Calibration.GeometricDisintegration
import OTSelector.Transport.Coupling.LabelClockCoordinates
import OTSelector.Probability.ConditionalClockSupport
import OTSelector.Probability.LabelDependentKernel
import OTSelector.Transport.CalibratedFiberIsometry
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The entire original Finsler optimal face in actual scalar conditional coordinates

The original potential and geometric labels construct a single measurable inverse coordinate.
All original optimal couplings are precisely the mixtures of increasing scalar conditional
couplings lifted through this inverse. The scalar marginals are the actual clock pushforwards
of the original conditional laws. This is an exact correspondence of whole feasible faces;
no conditional density, predetermined balance or selected optimizer is supplied.
-/

open Set MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

private theorem reconstruct_measure_of_labelClock_inverse
    {M Z : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z] [MeasurableEq Z] (μ : Measure M) [IsFiniteMeasure μ]
    {N : Set M} (hN : MeasurableSet N) (hμN : ∀ᵐ x ∂μ, x ∈ N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    {b : Z × ℝ → M} (hb : Measurable b) (hi : ∀ x ∈ N, b (a x, u x) = x) :
    mapWithLabel ((condDistrib id a μ).map u) b ∘ₘ μ.map a = μ := by
  calc
    _ = condDistrib id a μ ∘ₘ μ.map a := by
      apply Measure.comp_congr
      filter_upwards [ae_condDistrib_mem_carrier_fiber μ ha hN hμN] with z hz
      have hbz : Measurable (fun x : ℝ ↦ b (z, x)) :=
        hb.comp (measurable_const.prodMk measurable_id)
      rw [mapWithLabel_apply _ hb, Kernel.map_apply _ hu, Measure.map_map hbz hu]
      calc
        _ = (condDistrib id a μ z).map id := by
          apply Measure.map_congr
          filter_upwards [hz] with x hx
          change b (z, u x) = x
          rw [← hx.2]
          exact hi x hx.1
        _ = _ := Measure.map_id
    _ = μ := by
      simpa only [Measure.map_id] using condDistrib_comp_map ha.aemeasurable
        (measurable_id.aemeasurable : AEMeasurable (id : M → M) μ)

private theorem exists_scalar_representation_of_ordered_face
    {M Z : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : Set M} (hN : MeasurableSet N)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)))
    (hbalance : μ.map a = ν.map a) (P : Measure (M × M) → Prop)
    (hface : ∀ π, P π ↔ ∃ κ : Kernel Z (M × M), IsMarkovKernel κ ∧
      κ ∘ₘ μ.map a = π ∧ ∀ᵐ z ∂μ.map a,
        Vlasov.IsCoupling (κ z) (condDistrib id a μ z) (condDistrib id a ν z) ∧
          ∀ᵐ p ∂κ z, p.1 ∈ N ∧ p.2 ∈ N ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2) :
    ∃ b : Z × ℝ → M, Measurable b ∧ (∀ x ∈ N, b (a x, u x) = x) ∧
      ∀ π, P π ↔ ∃ κ : Kernel Z (ℝ × ℝ), IsMarkovKernel κ ∧
        mapWithLabel κ (fun p ↦ (b (p.1, p.2.1), b (p.1, p.2.2))) ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
            ((condDistrib id a μ z).map u) ((condDistrib id a ν z).map u) ∧
              ∀ᵐ p ∂κ z, p.1 ≤ p.2 := by
  obtain ⟨b, hb, hi, he⟩ := exists_labelClock_couplingEquiv hN ha hu hinj
  have hμfiber := ae_condDistrib_mem_carrier_fiber μ ha hN hμN
  have hνfiber := ae_condDistrib_mem_carrier_fiber ν ha hN hνN
  rw [← hbalance] at hνfiber
  let lift : Z × (ℝ × ℝ) → M × M := fun p ↦ (b (p.1, p.2.1), b (p.1, p.2.2))
  have hlift : Measurable lift :=
    (hb.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (hb.comp (measurable_fst.prodMk measurable_snd.snd))
  refine ⟨b, hb, hi, fun π ↦ ?_⟩
  constructor
  · intro hπ
    obtain ⟨κ, hκMarkov, hrec, hκ⟩ := (hface π).mp hπ
    let _instScalarFaceForwardKernel : IsMarkovKernel κ := hκMarkov
    let σ := κ.map (Prod.map u u)
    have hσMarkov : IsMarkovKernel σ := Kernel.IsMarkovKernel.map κ (hu.prodMap hu)
    refine ⟨σ, hσMarkov, ?_, ?_⟩
    · change mapWithLabel σ lift ∘ₘ μ.map a = π
      rw [← hrec]
      apply Measure.comp_congr
      filter_upwards [hκ, hμfiber, hνfiber] with z hz hμz hνz
      obtain ⟨e, hef, hei, _⟩ := he z _ _ hμz hνz
      let p := (⟨κ z, hz.1⟩ : {ρ // Vlasov.IsCoupling ρ
        (condDistrib id a μ z) (condDistrib id a ν z)})
      have heq := congrArg Subtype.val (e.symm_apply_apply p)
      rw [hei, hef] at heq
      rw [mapWithLabel_apply σ hlift z, Kernel.map_apply κ (hu.prodMap hu)]
      exact heq
    · filter_upwards [hκ] with z hz
      rw [Kernel.map_apply κ (hu.prodMap hu)]
      refine ⟨hz.1.map u u hu hu, ?_⟩
      apply (ae_map_iff (hu.prodMap hu).aemeasurable
        (measurableSet_le measurable_fst measurable_snd)).mpr
      exact hz.2.mono fun _ hp ↦ hp.2.2.2
  · rintro ⟨σ, hσMarkov, hrec, hσ⟩
    let _instScalarFaceBackwardKernel : IsMarkovKernel σ := hσMarkov
    let κ := mapWithLabel σ lift
    have hκMarkov : IsMarkovKernel κ := isMarkovKernel_mapWithLabel σ hlift
    apply (hface π).mpr
    refine ⟨κ, hκMarkov, hrec, ?_⟩
    filter_upwards [hσ, hμfiber, hνfiber] with z hz hμz hνz
    obtain ⟨e, hef, hei, heorder⟩ := he z _ _ hμz hνz
    let s := (⟨σ z, hz.1⟩ : {ρ // Vlasov.IsCoupling ρ
      ((condDistrib id a μ z).map u) ((condDistrib id a ν z).map u)})
    have heq : (e.symm s).val = κ z := by
      rw [hei, mapWithLabel_apply σ hlift z]
      rfl
    have hκz : Vlasov.IsCoupling (κ z)
        (condDistrib id a μ z) (condDistrib id a ν z) := heq ▸ (e.symm s).property
    have horder : ∀ᵐ p ∂κ z, u p.1 ≤ u p.2 := by
      rw [← heq]
      apply (heorder (e.symm s)).mpr
      simpa only [e.apply_symm_apply] using hz.2
    have hleft : ∀ᵐ p ∂κ z, p.1 ∈ N ∧ a p.1 = z :=
      ae_of_ae_map measurable_fst.aemeasurable (by rwa [hκz.1])
    have hright : ∀ᵐ p ∂κ z, p.2 ∈ N ∧ a p.2 = z :=
      ae_of_ae_map measurable_snd.aemeasurable (by rwa [hκz.2])
    refine ⟨hκz, ?_⟩
    filter_upwards [hleft, hright, horder] with p hp hq ho
    exact ⟨hp.1, hq.1, hp.2.trans hq.2.symm, ho⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original Finsler data construct measurable inverse scalar coordinates and an exact
scalar conditional-kernel representation of every original distance-optimal coupling. -/
theorem exists_finsler_scalar_disintegration (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instFinslerScalarStatementMetric : MetricSpace M := F.metricSpace
    let _instFinslerScalarStatementProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instFinslerScalarStatementBorel : StandardBorelSpace M := inferInstance
    let _instFinslerScalarStatementNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
    ∃ (u : M → ℝ) (a : M → (ℚ → M)) (b : (ℚ → M) × ℝ → M),
      LipschitzWith 1 u ∧ Measurable a ∧ Measurable b ∧
      (∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x) ∧
      (∀ z, Isometry (fun x : {x : M // x ∈ F.potentialRegularDomain u ∧ a x = z} ↦
        u x.val)) ∧ μ.map a = ν.map a ∧
      mapWithLabel ((condDistrib id a μ).map u) b ∘ₘ μ.map a = μ ∧
      mapWithLabel ((condDistrib id a ν).map u) b ∘ₘ μ.map a = ν ∧
      ∃ δ : ℝ, 0 < δ ∧
        (∀ᵐ z ∂μ.map a,
          IsCompact ((condDistrib id a μ z).map u).support ∧
          IsCompact ((condDistrib id a ν z).map u).support ∧
          (∀ r ∈ ((condDistrib id a μ z).map u).support,
            ∀ s ∈ ((condDistrib id a ν z).map u).support, δ ≤ dist r s) ∧
          ∀ r ∈ ((condDistrib id a μ z).map u).support ∪
              ((condDistrib id a ν z).map u).support,
            ∀ s ∈ ((condDistrib id a μ z).map u).support ∪
              ((condDistrib id a ν z).map u).support, dist r s ≤ Metric.diam (A ∪ B)) ∧
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ κ : Kernel (ℚ → M) (ℝ × ℝ), IsMarkovKernel κ ∧
          mapWithLabel κ (fun p ↦ (b (p.1, p.2.1), b (p.1, p.2.2))) ∘ₘ μ.map a = π ∧
            ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
              ((condDistrib id a μ z).map u) ((condDistrib id a ν z).map u) ∧
                ∀ᵐ p ∂κ z, p.1 ≤ p.2 := by
  let _instFinslerScalarMetric : MetricSpace M := F.metricSpace
  let _instFinslerScalarProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFinslerScalarNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  let _instFinslerScalarBorel : StandardBorelSpace M := inferInstance
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface⟩ :=
    exists_finsler_geometric_disintegration hF hcomplete m μ ν
      hμchart hνchart hA hB hAB hμ hν
  obtain ⟨b, hb, hi, hscalar⟩ := exists_scalar_representation_of_ordered_face μ ν
    hN hμN hνN ha hu.continuous.measurable hinj hbalance
    (IsOptimalCoupling edist μ ν) hface
  have hμrec := reconstruct_measure_of_labelClock_inverse μ hN hμN
    ha hu.continuous.measurable hb hi
  have hνrec := reconstruct_measure_of_labelClock_inverse ν hN hνN
    ha hu.continuous.measurable hb hi
  rw [← hbalance] at hνrec
  obtain ⟨δ, hδ, hgap⟩ := Metric.exists_pos_forall_lt_edist hA hB.isClosed hAB
  have hgap' (x : M) (hx : x ∈ A) (y : M) (hy : y ∈ B) : (δ : ℝ) ≤ dist x y := by
    have h := hgap x hx y hy
    rw [edist_nndist, ENNReal.coe_lt_coe] at h
    exact_mod_cast h.le
  have hbounds := ae_conditional_clock_support_bounds μ ν ha hbalance hu.continuous
    hA hB hN hμ hν hμN hνN
    (fun x hx y hy heq ↦ dist_eq_clock_dist_of_ordered_calibration horder hx hy heq)
    hgap' (fun _ hx _ hy ↦ Metric.dist_le_diam_of_mem (hA.union hB).isBounded hx hy)
  refine ⟨u, a, b, hu, ha, hb, hi, isometry_clock_on_label horder,
    hbalance, hμrec, hνrec, δ, hδ, ?_, hscalar⟩
  filter_upwards [hbounds] with z hz
  exact hz.2.2

end OTSelector.Reconstruction
