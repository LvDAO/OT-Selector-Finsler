import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenLocal
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockCollar
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation
import OTSelector.MeasureTheory.CompactTVNullCollar
import Mathlib.Topology.UrysohnsLemma

/-! Uniform compactly supported clock cutoffs use the original conditional
clock densities and their original total-variation continuity. Original
geometric separation is consumed almost everywhere; it is not an implicit
property of an arbitrary retained Good predicate. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- Inside the original outer interval, avoiding the two endpoint collars
places the unchanged clock inside the corresponding inner compact interval. -/
theorem mem_inner_clock_interval_of_notMem_endpoint_collar
    {lower upper width t : ℝ} (ht : t ∈ Icc lower upper)
    (hnot : t ∉ originalClockEndpointCollar id {lower,upper} width) :
    t ∈ Icc (lower+width) (upper-width) := by
  classical
  have hl : ¬dist t lower ≤ width := by
    intro h
    apply hnot
    exact Metric.mem_cthickening_of_dist_le t lower width (↑({lower,upper} : Finset ℝ))
      (by simp) h
  have hr : ¬dist t upper ≤ width := by
    intro h
    apply hnot
    exact Metric.mem_cthickening_of_dist_le t upper width (↑({lower,upper} : Finset ℝ))
      (by simp) h
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1)] at hl
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr ht.2)] at hr
  constructor <;> linarith

/-- One Urysohn cutoff misses only the original pair-window complement and
the actual two marginal endpoint collars. Its clocks and coupling stay fixed. -/
theorem exists_original_clock_cutoff_of_collar_width
    (window : RationalScalarPairWindow) {gap width : ℝ}
    (hgap : 0 < gap) (hwindow : (window.val.2.2 : ℝ) ≤ gap/2)
    (hwidth : 0 < width) :
    ∃ ψ : C(ℝ × ℝ,ℝ), IsCompact (tsupport ψ) ∧
      tsupport ψ ⊆ window.region ∧ (∀ p, ψ p ∈ Icc 0 1) ∧
      ∀ (α β : Measure ℝ) (π : Measure (ℝ × ℝ)), Vlasov.IsCoupling π α β →
        (∀ᵐ p ∂π, gap ≤ p.2-p.1) →
      (∫⁻ p, ENNReal.ofReal (1-ψ p) ∂π) ≤
        π window.regionᶜ +
        α (originalClockEndpointCollar id {(window.val.1 : ℝ),(window.val.2.1 : ℝ)} width) +
        β (originalClockEndpointCollar id {(window.val.1 : ℝ),(window.val.2.1 : ℝ)} width) := by
  classical
  let lower : ℝ := window.val.1
  let upper : ℝ := window.val.2.1
  let K : Set (ℝ × ℝ) := (Icc (lower+width) (upper-width) ×ˢ
      Icc (lower+width) (upper-width)) ∩ {p | gap ≤ p.2-p.1}
  let V : Set (ℝ × ℝ) := (Ioo lower upper ×ˢ Ioo lower upper) ∩
    {p | (window.val.2.2 : ℝ) < p.2-p.1}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_fst))
  have hV : IsOpen V := (isOpen_Ioo.prod isOpen_Ioo).inter
    (isOpen_lt continuous_const (continuous_snd.sub continuous_fst))
  have hKV : K ⊆ V := by
    intro p hp
    change (p.1 ∈ Ioo lower upper ∧ p.2 ∈ Ioo lower upper) ∧
      (window.val.2.2 : ℝ) < p.2-p.1
    have hpgap : gap ≤ p.2-p.1 := hp.2
    refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩ <;>
      linarith [hp.1.1.1,hp.1.1.2,hp.1.2.1,hp.1.2.2]
  obtain ⟨ψ,hψK,hψcompact,hψsub,hψrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  have hVsub : V ⊆ window.region := by
    intro p hp
    exact ⟨⟨⟨hp.1.1.1.le,hp.1.1.2.le⟩,⟨hp.1.2.1.le,hp.1.2.2.le⟩⟩,
      (show (window.val.2.2 : ℝ) < p.2-p.1 from hp.2).le⟩
  refine ⟨ψ,hψcompact,hψsub.trans hVsub,hψrange,?_⟩
  intro α β π hπ hπgap
  let collar : Set ℝ := originalClockEndpointCollar id {lower,upper} width
  let bad : Set (ℝ × ℝ) := (collar ×ˢ univ) ∪ (univ ×ˢ collar)
  have hcollar : MeasurableSet collar :=
    measurableSet_originalClockEndpointCollar measurable_id _ _
  have hmiss : (∫⁻ p, ENNReal.ofReal (1-ψ p) ∂π) ≤ π Kᶜ := by
    calc
      _ ≤ ∫⁻ p, Kᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)) p ∂π := by
        apply lintegral_mono
        intro p
        by_cases hp : p ∈ K
        · change ENNReal.ofReal (1-ψ p) ≤ _
          have he : ψ p = 1 := hψK hp
          simp [he]
        · rw [indicator_of_mem hp]
          change ENNReal.ofReal (1-ψ p) ≤ 1
          exact ENNReal.ofReal_le_one.mpr (by linarith [(hψrange p).1])
      _ = _ := lintegral_indicator_one hK.isClosed.measurableSet.compl
  have hcover : ∀ᵐ p ∂π, p ∈ Kᶜ → p ∈ window.regionᶜ ∪ bad := by
    filter_upwards [hπgap] with p hpgap
    intro hp
    by_cases hw : p ∈ window.region
    · apply Or.inr
      by_cases hs : p.1 ∈ collar
      · exact Or.inl ⟨hs,mem_univ _⟩
      · apply Or.inr
        refine ⟨mem_univ _,?_⟩
        by_contra ht
        have hleft := mem_inner_clock_interval_of_notMem_endpoint_collar hw.1.1 hs
        have hright := mem_inner_clock_interval_of_notMem_endpoint_collar hw.1.2 ht
        exact hp ⟨⟨hleft,hright⟩,hpgap⟩
    · exact Or.inl hw
  have hsource : π (collar ×ˢ (univ : Set ℝ)) = α collar := by
    have he : collar ×ˢ (univ : Set ℝ) = Prod.fst ⁻¹' collar := by ext p; simp
    rw [he,← Measure.map_apply measurable_fst hcollar,hπ.1]
  have htarget : π ((univ : Set ℝ) ×ˢ collar) = β collar := by
    have he : (univ : Set ℝ) ×ˢ collar = Prod.snd ⁻¹' collar := by ext p; simp
    rw [he,← Measure.map_apply measurable_snd hcollar,hπ.2]
  calc
    _ ≤ π Kᶜ := hmiss
    _ ≤ π (window.regionᶜ ∪ bad) := measure_mono_ae hcover
    _ ≤ π window.regionᶜ + π bad := measure_union_le _ _
    _ ≤ π window.regionᶜ + (α collar+β collar) := by
      apply add_le_add_right
      exact (measure_union_le _ _).trans_eq (by rw [hsource,htarget])
    _ = _ := (add_assoc _ _ _).symm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The full original L1 densities and their compact-root TV continuity produce
one clock cutoff for every original forward coupling on the retained piece.
Only the actual endpoint collar loss is added to the original coupling loss. -/
theorem PopulationLocalPressureCore.exists_uniform_original_clock_cutoff
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ ε)
    (i : Fin D.haar.continuous.count) {gap η : ℝ} (hgap : 0 < gap)
    (hwindow : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    (hη : 0 < η) :
    ∃ ψ : C(ℝ × ℝ, ℝ), IsCompact (tsupport ψ) ∧
      tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region ∧
      (∀ p, ψ p ∈ Icc 0 1) ∧
      ∀ z ∈ (D.haar.continuous.coefficient i).roots, ∀ diam : ℝ,
        ConditionalClockSupportBounds (condDistrib u a μ z) (condDistrib u a ν z)
          gap diam →
        ∀ π : Measure (ℝ × ℝ),
          Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) →
          (∀ᵐ p ∂π, p.1 ≤ p.2) →
          (∫⁻ p, ENNReal.ofReal (1 - ψ p) ∂π) ≤ δ + ENNReal.ofReal η := by
  classical
  let B := D.haar.continuous.population
  let C := D.haar.continuous.coefficient i
  have hsub : C.roots ⊆ B.roots := by
    intro z hz
    rw [← D.haar.continuous.union_eq]
    exact mem_iUnion.mpr ⟨i,hz⟩
  have hcontinuous (color : Fin 2) : ContinuousOn (B.densityClass color) C.roots :=
    (continuous_apply color).comp_continuousOn (B.continuous_class.mono hsub)
  have htv (color : Fin 2) (z : ℚ → M) (hz : z ∈ C.roots)
      (w : ℚ → M) (hw : w ∈ C.roots) :
      ((populationTwoColorClockKernel u a μ ν color z).toSignedMeasure -
        (populationTwoColorClockKernel u a μ ν color w).toSignedMeasure).totalVariation
        univ ≤ ENNReal.ofReal ‖B.densityClass color z-B.densityClass color w‖ :=
    (B.variation color z (hsub hz) w (hsub hw)).le
  let thresholds : Finset ℝ := {(C.window.val.1 : ℝ),(C.window.val.2.1 : ℝ)}
  have hnull (color : Fin 2) (z : ℚ → M) (hz : z ∈ C.roots)
      (t : ℝ) (_ht : t ∈ thresholds) :
      populationTwoColorClockKernel u a μ ν color z {t} = 0 := by
    rw [← (B.density z (hsub hz) color).2.1]
    exact measure_singleton t
  obtain ⟨width,hwidth,hcollars⟩ := exists_uniform_twoColor_clock_collar_measure_add_lt
    (fun color z ↦ populationTwoColorClockKernel u a μ ν color z)
    B.densityClass C.roots_compact hcontinuous htv thresholds hnull hη
  obtain ⟨ψ,hcompact,hψsub,hrange,hbound⟩ :=
    exists_original_clock_cutoff_of_collar_width C.window hgap hwindow hwidth
  refine ⟨ψ,hcompact,hψsub,hrange,?_⟩
  intro z hz diam hsep π hπ horder
  have hcollars' :
      (condDistrib u a μ z) (originalClockEndpointCollar id thresholds width) +
      (condDistrib u a ν z) (originalClockEndpointCollar id thresholds width) <
      ENNReal.ofReal η := by
    simpa only [populationTwoColorClockKernel, Fin.zero_eta, Fin.isValue, reduceIte,
      Fin.reduceEq, originalClockEndpointCollar, preimage_id_eq, id_eq] using hcollars z hz
  calc
    _ ≤ π C.window.regionᶜ +
        (condDistrib u a μ z) (originalClockEndpointCollar id thresholds width) +
        (condDistrib u a ν z) (originalClockEndpointCollar id thresholds width) :=
      hbound _ _ π hπ (hsep.ae_clock_gap_of_coupling hπ horder)
    _ = π C.window.regionᶜ +
        ((condDistrib u a μ z) (originalClockEndpointCollar id thresholds width) +
          (condDistrib u a ν z) (originalClockEndpointCollar id thresholds width)) :=
      add_assoc _ _ _
    _ ≤ δ + ENNReal.ofReal η :=
      add_le_add (C.coupling_loss z hz π hπ horder).le hcollars'.le

/-- Compact disjoint original carriers produce the true gap almost everywhere
for the original label law. The resulting common cutoff therefore applies to
that same law on every retained core, without a separation premise in Good. -/
theorem exists_original_uniform_clock_cutoff_of_compact_carriers
    [Nonempty M]
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker}
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hbalance : μ.map a = ν.map a) (hu : Continuous u)
    {A B N : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hN : MeasurableSet N) (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : let _instClockCutoffMetric : MetricSpace M := F.metricSpace;
      ∀ x ∈ N, ∀ y ∈ N, (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ ε)
        (i : Fin D.haar.continuous.count),
        ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2 →
        ∀ η > 0, ∃ ψ : C(ℝ × ℝ, ℝ), IsCompact (tsupport ψ) ∧
          tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region ∧
          (∀ p, ψ p ∈ Icc 0 1) ∧
          ∀ᵐ z ∂(μ.map a).restrict (D.haar.continuous.coefficient i).roots,
            ∀ π : Measure (ℝ × ℝ),
              Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) →
              (∀ᵐ p ∂π, p.1 ≤ p.2) →
              (∫⁻ p, ENNReal.ofReal (1-ψ p) ∂π) ≤ δ + ENNReal.ofReal η := by
  let _instClockCutoffMetric : MetricSpace M := F.metricSpace
  let _instClockCutoffProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instClockCutoffPolish : PolishSpace M := inferInstance
  let _instClockCutoffBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨gap,hgap,hseparation⟩ := exists_population_conditional_separation μ ν ha hbalance
    hu hA hB hAB hN hμA hνB hμN hνN horder
  refine ⟨gap,hgap,?_⟩
  intro D i hwindow η hη
  obtain ⟨ψ,hcompact,hsub,hrange,hbound⟩ :=
    D.exists_uniform_original_clock_cutoff i hgap hwindow hη
  refine ⟨ψ,hcompact,hsub,hrange,?_⟩
  have hsep : ∀ᵐ z ∂(μ.map a).restrict (D.haar.continuous.coefficient i).roots,
      ConditionalClockSupportBounds (condDistrib u a μ z) (condDistrib u a ν z)
        gap (Metric.diam (A ∪ B)) := ae_restrict_of_ae hseparation
  filter_upwards [hsep,
    ae_restrict_mem (D.haar.continuous.coefficient i).roots_compact.measurableSet]
    with z hz hmem
  exact hbound z hmem _ hz

/-- The existing original Haar producer and the actual compact-carrier gap
construct an auxiliary core and all of its uniform clock cutoffs at arbitrary
original root and coupling accuracies. No conditional separation is assumed
inside the user-selected retained predicate. -/
theorem exists_original_population_core_uniform_clock_cutoffs
    [Nonempty M]
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker}
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instClockCutoffMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hbalance : μ.map a = ν.map a) (hGood : ∀ᵐ z ∂μ.map a, Good z)
    {A B N : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hN : MeasurableSet N) (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : let _instClockCutoffMetric : MetricSpace M := F.metricSpace;
      ∀ x ∈ N, ∀ y ∈ N, (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (hδ : δ ≠ 0) (hloss : loss ≠ 0) :
    ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss,
      ∀ i : Fin D.haar.continuous.count, ∀ η > 0,
        ∃ ψ : C(ℝ × ℝ, ℝ), IsCompact (tsupport ψ) ∧
          tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region ∧
          (∀ p, ψ p ∈ Icc 0 1) ∧
          ∀ᵐ z ∂(μ.map a).restrict (D.haar.continuous.coefficient i).roots,
            ∀ π : Measure (ℝ × ℝ),
              Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) →
              (∀ᵐ p ∂π, p.1 ≤ p.2) →
              (∫⁻ p, ENNReal.ofReal (1-ψ p) ∂π) ≤ δ + ENNReal.ofReal η := by
  let _instClockCutoffMetric : MetricSpace M := F.metricSpace
  let _instClockCutoffProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instClockCutoffPolish : PolishSpace M := inferInstance
  let _instClockCutoffBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨gap,hgap,hcutoff⟩ :=
    exists_original_uniform_clock_cutoff_of_compact_carriers (P := P) (κ := κ)
      (ρ₀ := ρ₀) (ρ₁ := ρ₁) (v := v) (b := b) (Good := Good) (r := r)
      (δ := δ) (ε := loss) hcomplete ha hbalance hu.continuous
      hA hB hAB hN hμA hνB hμN hνN horder
  obtain ⟨D,hscreen⟩ := hcore.exists_local_core_small_clock_screen hrecovery hF hcomplete
    hu ha hinj hκ hGood (half_pos hgap) hδ hloss
  exact ⟨D,fun i η hη ↦ hcutoff D i (hscreen i) η hη⟩

end OTSelector.Reconstruction
