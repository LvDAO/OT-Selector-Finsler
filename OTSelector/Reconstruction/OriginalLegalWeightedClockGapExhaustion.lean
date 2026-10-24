import OTSelector.Reconstruction.OriginalLegalWeightedReserveUniformClockBudget

/-!
# Almost-full original clock carriers with genuine positive reserve gap

The same strictly forward original Palm and atomless original clocks make
the original Hall tail surplus positive at almost every source clock.
Compact positive-gap carriers are then selected from that original law.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- The actual original strict/closed Hall surplus equals the crossing mass
of the SAME original Palm, with no moment or coupling replacement. -/
theorem LegalWeightedStationaryPoissonMatching.clockSurplus_eq_palm_crossing
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) (a : ℝ) :
    legalOriginalClockSurplus α β a =
      (legalMarkedJointPalm q N.law {m | m.1.1 ≤ a ∧ a < m.1.2}).toReal := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have hcross := measure_forward_clock_crossing_add_target_prefix q
    (legalMarkedJointPalm q N.law) α β N.source_clock N.target_clock
    (N.ae_palm_forward.mono fun _ h ↦ h.le) a
  have hr := congrArg ENNReal.toReal hcross
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hr
  rw [N.clockSurplus_eq_prefix_difference]
  change _ + β.real (Iic a) = α.real (Iic a) at hr
  linarith

/-- A finite original clock law gives nearly full compact carriers on which
an almost-everywhere positive continuous quantity has a genuine uniform
positive lower bound. No relation between gap size and omitted mass is assumed. -/
theorem exists_compact_uniform_positive_carrier_of_ae
    (α : Measure ℝ) [IsFiniteMeasure α] (g : ℝ → ℝ) (hg : Continuous g)
    (hpos : ∀ᵐ a ∂α, 0 < g a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∃ D : Set ℝ, IsCompact D ∧ α Dᶜ < ENNReal.ofReal δ ∧
      ∀ a ∈ D, η ≤ g a := by
  let S := {a : ℝ | 0 < g a}
  have hS : MeasurableSet S := (isOpen_lt continuous_const hg).measurableSet
  obtain ⟨D, hDS, hD, hsmall⟩ := hS.exists_isCompact_sdiff_lt
    (measure_ne_top α S) (ENNReal.ofReal_pos.mpr hδ).ne'
  have heq : α Dᶜ = α (S \ D) := by
    apply measure_congr
    filter_upwards [hpos] with a ha
    change (a ∉ D) = ((0 < g a) ∧ a ∉ D)
    exact propext (by simp only [ha, true_and])
  have hb : α Dᶜ < ENNReal.ofReal δ := heq ▸ hsmall
  by_cases hne : D.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hD.exists_isMinOn hne hg.continuousOn
    exact ⟨g a, hDS ha, D, hD, hb, hmin⟩
  · exact ⟨1, zero_lt_one, D, hD, hb, fun a ha ↦ False.elim (hne ⟨a, ha⟩)⟩

/-- Every scalar measure gives positive cumulative mass at almost every point.
No finiteness or atomlessness assumption is needed. -/
theorem ae_pos_measure_Iic (ν : Measure ℝ) : ∀ᵐ a ∂ν, 0 < ν (Iic a) := by
  classical
  let B : Set ℝ := {a | ν (Iic a) = 0} ∩ ν.support
  have hB : B.Subsingleton := by
    intro a ha b hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hp : 0 < ν (Iio b) :=
        (Measure.mem_support_iff_forall a).mp ha.2 _ (Iio_mem_nhds hab)
      have hz : ν (Iio b) = 0 := measure_mono_null Iio_subset_Iic_self hb.1
      exact (ne_of_gt hp) hz
    · have hp : 0 < ν (Iio a) :=
        (Measure.mem_support_iff_forall b).mp hb.2 _ (Iio_mem_nhds hba)
      have hz : ν (Iio a) = 0 := measure_mono_null Iio_subset_Iic_self ha.1
      exact (ne_of_gt hp) hz
  have hBzero : ν B = 0 := by
    rcases B.eq_empty_or_nonempty with hEmpty | ⟨b, hb⟩
    · rw [hEmpty, measure_empty]
    · exact measure_mono_null
        (fun a ha ↦ (hB ha hb).le) hb.1
  have hBad : ∀ᵐ a ∂ν, a ∉ B := by
    rw [ae_iff]
    have heq : {a : ℝ | ¬ a ∉ B} = B := by
      ext a
      simp
    rw [heq]
    exact hBzero
  filter_upwards [ν.support_mem_ae, hBad] with a ha hnot
  apply pos_iff_ne_zero.mpr
  intro hz
  exact hnot ⟨hz, ha⟩

/-- For a finite scalar measure, the real-valued cumulative mass is positive
at almost every point of that same measure. -/
theorem ae_pos_measureReal_Iic (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∀ᵐ a ∂ν, 0 < ν.real (Iic a) := by
  filter_upwards [ae_pos_measure_Iic ν] with a ha
  exact ENNReal.toReal_pos ha.ne' (measure_ne_top ν (Iic a))


/-- A finite strictly forward original joint law has positive crossing mass
at its own source almost everywhere. The law, both readouts and all pairing
correlations are retained; no atomlessness assumption is needed here. -/
theorem ae_pos_measureReal_forward_crossing
    {Ω : Type*} [MeasurableSpace Ω] (η : Measure Ω) [IsFiniteMeasure η]
    (source target : Ω → ℝ) (hs : Measurable source) (ht : Measurable target)
    (hforward : ∀ᵐ w ∂η, source w < target w) :
    ∀ᵐ w ∂η, 0 < η.real {v | source v ≤ source w ∧ source w < target v} := by
  let ν : ℚ → Measure ℝ := fun r ↦
    (η.restrict {w | (r : ℝ) < target w}).map source
  have hcut (r : ℚ) : ∀ᵐ w ∂η, (r : ℝ) < target w → 0 < (ν r).real (Iic (source w)) := by
    have : IsFiniteMeasure (ν r) := by dsimp only [ν]; infer_instance
    have ha := ae_pos_measureReal_Iic (ν r)
    have hback : ∀ᵐ w ∂η.restrict {w | (r : ℝ) < target w},
        0 < (ν r).real (Iic (source w)) := ae_of_ae_map hs.aemeasurable ha
    exact (ae_restrict_iff' (measurableSet_lt measurable_const ht)).mp hback
  have hall : ∀ᵐ w ∂η, ∀ r : ℚ, (r : ℝ) < target w → 0 < (ν r).real (Iic (source w)) :=
    ae_all_iff.mpr hcut
  filter_upwards [hforward, hall] with w hf hm
  obtain ⟨r, hsr, hrt⟩ := exists_rat_btwn hf
  have hrpos := hm r hrt
  have hle : ν r (Iic (source w)) ≤ η {v | source v ≤ source w ∧ source w < target v} := by
    rw [show ν r = (η.restrict {w | (r : ℝ) < target w}).map source from rfl,
      Measure.map_apply hs measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage hs)]
    exact measure_mono fun v hv ↦ ⟨hv.1, hsr.trans hv.2⟩
  exact hrpos.trans_le (ENNReal.toReal_mono (measure_ne_top η _) hle)

/-- The SAME original strictly forward Palm makes its original Hall surplus
positive at almost every original source clock. Atomlessness is applied to
the supplied original clocks, never to a selected endpoint distribution. -/
theorem LegalWeightedStationaryPoissonMatching.ae_pos_originalClockSurplus
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ a ∂α, 0 < legalOriginalClockSurplus α β a := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  have hp := ae_pos_measureReal_forward_crossing (legalMarkedJointPalm q N.law)
    (fun m ↦ m.1.1) (fun m ↦ m.1.2) measurable_fst.fst measurable_fst.snd N.ae_palm_forward
  have hpalm : ∀ᵐ m ∂legalMarkedJointPalm q N.law,
      0 < legalOriginalClockSurplus α β m.1.1 := by
    filter_upwards [hp] with m hm
    rwa [N.clockSurplus_eq_palm_crossing]
  have hmap : ∀ᵐ a ∂(legalMarkedJointPalm q N.law).map (fun m ↦ m.1.1),
      0 < legalOriginalClockSurplus α β a :=
    (ae_map_iff measurable_fst.fst.aemeasurable
      (isOpen_lt continuous_const N.continuous_originalClockSurplus).measurableSet).mpr hpalm
  simpa only [N.source_clock] using hmap

/-- The original source law admits arbitrarily full compact positive-gap
carriers. The omitted source mass and the resulting gap are separately
produced; no quantitative relation between them is imposed. -/
theorem LegalWeightedStationaryPoissonMatching.exists_compact_originalClockGapCarrier_ae_full
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∃ D : Set ℝ, IsCompact D ∧
      α (legalOriginalClockGapCarrier α β D η)ᶜ < ENNReal.ofReal δ ∧
      IsCompact (legalOriginalClockGapCarrier α β D η) ∧
      ∀ a ∈ legalOriginalClockGapCarrier α β D η,
        α.real (Ici a) + η ≤ β.real (Ioi a) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  obtain ⟨η, hη, D, hD, hsmall, hgap⟩ := exists_compact_uniform_positive_carrier_of_ae
    α (legalOriginalClockSurplus α β) N.continuous_originalClockSurplus
      N.ae_pos_originalClockSurplus hδ
  have heq : legalOriginalClockGapCarrier α β D η = D := by
    apply Set.inter_eq_left.mpr
    exact fun a ha ↦ hgap a ha
  refine ⟨η, hη, D, hD, heq.symm ▸ hsmall, heq.symm ▸ hD, ?_⟩
  intro a ha
  have hh := ha.2
  change η ≤ β.real (Ioi a) - α.real (Ici a) at hh
  linarith

/-- Compact genuine positive-gap carriers exhaust the original source law
in measure. Their actual gaps are not tied to their omitted masses. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalClockGapCarriers_exhaust_source
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∃ (η : ℕ → ℝ) (D : ℕ → Set ℝ), (∀ n, 0 < η n) ∧ (∀ n, IsCompact (D n)) ∧
      (∀ n, IsCompact (legalOriginalClockGapCarrier α β (D n) (η n))) ∧
      (∀ n, α (legalOriginalClockGapCarrier α β (D n) (η n))ᶜ <
        ENNReal.ofReal (((n : ℝ) + 1)⁻¹)) ∧
      Tendsto (fun n ↦ α (legalOriginalClockGapCarrier α β (D n) (η n))ᶜ) atTop (𝓝 0) := by
  have h (n : ℕ) := N.exists_compact_originalClockGapCarrier_ae_full
    (by positivity : 0 < ((n : ℝ) + 1)⁻¹)
  choose η hη D hD hsmall hK hgap using h
  refine ⟨η, D, hη, hD, hK, hsmall, ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have htenn : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htenn
    (fun _ ↦ bot_le) (fun n ↦ (hsmall n).le)

/-- An arbitrarily full original source gap carrier supplies genuine uniform
Hall slack. The actual symmetric clock cutoff contains that whole carrier
and has sufficiently small original target loss, both proved internally. -/
theorem LegalWeightedStationaryPoissonMatching.exists_original_law_uniformClockSlack_ae_full
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∃ (D : Set ℝ) (L : ℝ), 0 < L ∧ IsCompact D ∧
      IsCompact (legalOriginalClockGapCarrier α β D η) ∧
      legalOriginalClockGapCarrier α β D η ⊆ Icc (-L) L ∧
      α (legalOriginalClockGapCarrier α β D η)ᶜ < ENNReal.ofReal δ ∧
      (β (Icc (-L) L)ᶜ).toReal ≤ η / 4 ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (hd : d ≠ 0)
        (V : Set (Fin q → ℝ)) (_hV : IsCompact V),
        0 < legalOriginalReserveSpatialRate q d V →
        ∃ E : Set (LegalMarkedOptimalInputScene q), MeasurableSet E ∧
          (legalOriginalReserveUniformClockSlackEvent q d hd V (Icc (-L) L)
            (legalOriginalClockGapCarrier α β D η) η)ᶜ ⊆ E ∧
          (N.law : Measure (LegalMarkedOptimalInputScene q)).real E ≤
            C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  obtain ⟨η, hη, D, hD, hsmall, hK, hgap⟩ :=
    N.exists_compact_originalClockGapCarrier_ae_full hδ
  obtain ⟨A, hA, htail⟩ := N.exists_compact_clock_truncation (by positivity : 0 < η / 4)
  obtain ⟨L, hL, hbound⟩ := (hA.union hD).isBounded.exists_pos_norm_lt
  have hsubset : A ∪ D ⊆ Icc (-L) L := by
    intro a ha
    have hh := hbound a ha
    rw [Real.norm_eq_abs] at hh
    exact ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩
  have hβtail : (β (Icc (-L) L)ᶜ).toReal ≤ η / 4 := by
    let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
    let : IsProbabilityMeasure β := by
      rw [← N.target_clock]
      exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
    exact (measureReal_mono (compl_subset_compl.mpr (subset_union_left.trans hsubset))).trans htail
  obtain ⟨C, hC, hh⟩ := N.exists_reserveUniformClockSlack_measurable_cover hη
  exact ⟨η, hη, D, L, hL, hD, hK,
    inter_subset_left.trans (subset_union_right.trans hsubset), hsmall, hβtail, C, hC,
      fun d hd V hV hr ↦ hh d hd V hV (Icc (-L) L) isCompact_Icc hr hβtail D⟩

/-- Arbitrarily full original source gap carriers support actual uniform
Hall reserve slack in the SAME original M×N/Poisson-array experiment and
SAME retained core. All gaps, carriers and clock cutoffs are constructed. -/
theorem exists_original_labelled_reserve_windowCore_with_ae_full_uniformClockSlack
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 0 < q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∃ (D : Set ℝ) (L : ℝ), 0 < L ∧ IsCompact D ∧
      IsCompact (legalOriginalClockGapCarrier α β D η) ∧
      legalOriginalClockGapCarrier α β D η ⊆ Icc (-L) L ∧
      α (legalOriginalClockGapCarrier α β D η)ᶜ < ENNReal.ofReal δ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0),
        |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1 →
        ∀ (V : Set (Fin q → ℝ)) (_hV : IsCompact V),
        0 < legalOriginalReserveSpatialRate q d V → ∀ cost : LegalMarkedPhysicalEdge q → ℝ,
        ∃ S > 0, ∃ P : ProbabilityMeasure (LegalOriginalReserveWindowExperiment q),
        ∃ E : Set (LegalMarkedOptimalInputScene q),
          (P : Measure (LegalOriginalReserveWindowExperiment q)).map Prod.fst =
            (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
              (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
          (P : Measure (LegalOriginalReserveWindowExperiment q)).map Prod.snd =
            legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
          (∀ᵐ p ∂(P : Measure (LegalOriginalReserveWindowExperiment q)),
            IsOriginalReserveWindowCore q (V ×ˢ Icc (-L) L) cost
              (legalMarkedInputSceneDilation q c hc p.1.1)
              (legalMarkedInputSceneDilation q d hd p.1.2) p.2) ∧
          MeasurableSet E ∧
          (legalOriginalReserveUniformClockSlackEvent q d hd V (Icc (-L) L)
            (legalOriginalClockGapCarrier α β D η) η)ᶜ ⊆ E ∧
          (P : Measure (LegalOriginalReserveWindowExperiment q)).real
            ((fun p ↦ p.1.2) ⁻¹' E) ≤ C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  obtain ⟨η, hη, D, L, hL, hD, hK, hKA, hsmall, htail, C, hC, hh⟩ :=
    N.exists_original_law_uniformClockSlack_ae_full hδ
  refine ⟨η, hη, D, L, hL, hD, hK, hKA, hsmall, C, hC, ?_⟩
  intro c d hc hd hunit V hV hr cost
  obtain ⟨S, hS, P, hl, ht, hcore⟩ := exists_original_labelled_reserve_windowCore
    M N hq c d hc hd hunit (hV.prod isCompact_Icc) cost
  obtain ⟨E, hE, hsub, hb⟩ := hh d hd V hV hr
  refine ⟨S, hS, P, E, hl, ht, hcore, hE, hsub, ?_⟩
  rw [original_labelled_reserve_coordinate_real_preimage M N _ hl hE]
  exact hb

section OriginalConditionalClockGap

open Manifold OTSelector.Geometry
open scoped ContDiff

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Both unchanged original conditional Finsler clock laws consume their
existing geometric atomlessness producer at the SAME label, yielding actual
source-almost-everywhere positive gap and arbitrarily full compact carriers. -/
theorem ae_originalConditionalClock_positiveGap_and_full_carriers_of_windowLaws
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ρs ρt : M → ℝ} {vs vt : ℕ → E → ℝ}
    (hs : PopulationConditionalWindowLaw P a κ lambda μ ρs vs)
    (ht : PopulationConditionalWindowLaw P a κ lambda ν ρt vt)
    (ha : Measurable a)
    (hu : let _instOriginalGapClockMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {As At : Set M} (hAs : IsCompact As) (hAt : IsCompact At)
    (hμ : ∀ᵐ x ∂μ, x ∈ As) (hν : ∀ᵐ x ∂ν, x ∈ At)
    (q : ℕ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) :
    ∀ᵐ z ∂lambda,
      ∀ _N : LegalWeightedStationaryPoissonMatching q (condDistrib u a μ z)
        (condDistrib u a ν z) kin g,
      (∀ᵐ c ∂condDistrib u a μ z, 0 <
        legalOriginalClockSurplus (condDistrib u a μ z) (condDistrib u a ν z) c) ∧
      ∀ δ : ℝ, 0 < δ → ∃ η > 0, ∃ D : Set ℝ, IsCompact D ∧
        (condDistrib u a μ z)
          (legalOriginalClockGapCarrier (condDistrib u a μ z) (condDistrib u a ν z) D η)ᶜ <
            ENNReal.ofReal δ ∧
        IsCompact (legalOriginalClockGapCarrier (condDistrib u a μ z) (condDistrib u a ν z) D η) ∧
        ∀ c ∈ legalOriginalClockGapCarrier (condDistrib u a μ z) (condDistrib u a ν z) D η,
          (condDistrib u a μ z).real (Ici c) + η ≤ (condDistrib u a ν z).real (Ioi c) := by
  filter_upwards [ae_atomless_clock_of_windowLaw hs ha hu hAs hμ,
    ae_atomless_clock_of_windowLaw ht ha hu hAt hν] with z hsz htz
  let : NullSingletonClass (condDistrib u a μ z) := hsz.1
  let : NullSingletonClass (condDistrib u a ν z) := htz.1
  intro N
  exact ⟨N.ae_pos_originalClockSurplus,
    fun δ hδ ↦ N.exists_compact_originalClockGapCarrier_ae_full hδ⟩

end OriginalConditionalClockGap

end OTSelector.Reconstruction
