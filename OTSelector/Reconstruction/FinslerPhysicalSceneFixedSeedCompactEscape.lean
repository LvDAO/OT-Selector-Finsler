import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedTailTightness
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetNonproper

/-!
# Actual compact escapes of the same fixed original seed scene

The actual four long-edge tails produce compact source and target cutoffs using
the unchanged original compact clock carriers.  The same cutoffs work for every
tilt after one common sample bound.  The source-restricted physical plans and
all their realized restricted target columns remain unchanged.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Geometry
variable {ι M : Type*} [Fintype ι] [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- A real radius dominating one finite squared threshold gives both actual
compact escape rectangles, using the original source and target clock images. -/
theorem physicalSceneRootedPlan_compact_test_escapes_le_longTails
    (Γ : Measure (M × M)) {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hcarried : ∀ᵐ p ∂Γ, p.1 ∈ A ∧ p.2 ∈ B)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Continuous u) (H : Set M) (N : ℝ) (z : ι → ℝ)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (W R : ℝ)
    (hW : ∀ y ∈ tsupport f, ‖y.1‖ ≤ W) (hR : 0 ≤ R)
    (threshold : ℝ≥0∞) (hthreshold : threshold ≤ ENNReal.ofReal (R ^ 2)) :
    (physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      (tsupport f ×ˢ (physicalSceneSpatialClockCutoff W R (u '' B))ᶜ) ≤
      physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
        (physicalSceneLongEdgeWindow (physicalSceneTestSpatialWindow f) threshold)) ∧
    (physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      ((physicalSceneSpatialClockCutoff W R (u '' A))ᶜ ×ˢ tsupport f) ≤
      physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
        (physicalSceneTargetLongEdgeWindow (physicalSceneTestSpatialWindow f) threshold)) := by
  have hUW : ∀ x ∈ physicalSceneTestSpatialWindow f, ‖x‖ ≤ W := by
    rintro x ⟨y, hy, rfl⟩
    exact hW y hy
  constructor
  · apply (measure_mono (show tsupport f ×ˢ (physicalSceneSpatialClockCutoff W R (u '' B))ᶜ ⊆
        ((physicalSceneTestSpatialWindow f ×ˢ (univ : Set ℝ)) ×ˢ
          (physicalSceneSpatialClockCutoff W R (u '' B))ᶜ) from by
        intro e he
        exact ⟨⟨mem_image_of_mem Prod.fst he.1, mem_univ _⟩, he.2⟩)).trans
    apply (physicalSceneRootedPlan_escape_compact_le_full_longTail Γ coord hcoord u hu.measurable
      (hB.image hu).measurableSet (hcarried.mono fun p hp ↦ mem_image_of_mem u hp.2)
      H N z hUW hR).trans
    exact measure_mono (fun e he ↦ ⟨he.1, hthreshold.trans he.2⟩)
  · apply (measure_mono (show (physicalSceneSpatialClockCutoff W R (u '' A))ᶜ ×ˢ tsupport f ⊆
        ((physicalSceneSpatialClockCutoff W R (u '' A))ᶜ ×ˢ
          (physicalSceneTestSpatialWindow f ×ˢ (univ : Set ℝ))) from by
        intro e he
        exact ⟨he.1, mem_image_of_mem Prod.fst he.2, mem_univ _⟩)).trans
    apply (physicalSceneRootedPlan_target_escape_compact_le_full_longTail Γ coord hcoord u hu.measurable
      (hA.image hu).measurableSet (hcarried.mono fun p hp ↦ mem_image_of_mem u hp.1)
      H N z hUW hR).trans
    exact measure_mono (fun e he ↦ ⟨he.1, hthreshold.trans he.2⟩)

/-- The actual compact escape inequalities pass through both original
integrals from the actual original clock carriers. -/
theorem lintegral_physicalSceneRootedPlan_compact_test_escapes_le_longTails
    {Ω : Type*} [MeasurableSpace Ω] (Penv : Measure Ω) (Γ : Ω → Measure (M × M))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hcarried : ∀ᵐ w ∂Penv, ∀ᵐ p ∂Γ w, p.1 ∈ A ∧ p.2 ∈ B)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Continuous u) (H : Set M) (N : ℝ) (rootDomain : Set (ι → ℝ))
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (W R : ℝ)
    (hW : ∀ y ∈ tsupport f, ‖y.1‖ ≤ W) (hR : 0 ≤ R)
    (threshold : ℝ≥0∞) (hthreshold : threshold ≤ ENNReal.ofReal (R ^ 2)) :
    ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
      (tsupport f ×ˢ (physicalSceneSpatialClockCutoff W R (u '' B))ᶜ)
      ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
        (physicalSceneLongEdgeWindow (physicalSceneTestSpatialWindow f) threshold)
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ∧
    ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
      ((physicalSceneSpatialClockCutoff W R (u '' A))ᶜ ×ˢ tsupport f)
      ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
        (physicalSceneTargetLongEdgeWindow (physicalSceneTestSpatialWindow f) threshold)
        ∂cavityRootMeasure volume rootDomain N ∂Penv) := by
  constructor
  · apply lintegral_mono_ae
    filter_upwards [hcarried] with w hw
    exact lintegral_mono fun z ↦
      (physicalSceneRootedPlan_compact_test_escapes_le_longTails (Γ w) hA hB hw
        coord hcoord u hu H N z f W R hW hR threshold hthreshold).1
  · apply lintegral_mono_ae
    filter_upwards [hcarried] with w hw
    exact lintegral_mono fun z ↦
      (physicalSceneRootedPlan_compact_test_escapes_le_longTails (Γ w) hA hB hw
        coord hcoord u hu H N z f W R hW hR threshold hthreshold).2

end Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}


/-- The original physical hypotheses produce compact source and target cutoffs
whose actual four escape masses are eventually small, uniformly in the tilt.
The fixed original source piece and its realized restricted columns are retained. -/
theorem exists_original_fixed_seed_uniform_compact_escape
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (j : ℕ)
    (aplus aminus : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hplus : ∀ ℓ n k, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aplus ℓ n z.1 z.2 k))
    (hminus : ∀ ℓ n k, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aminus ℓ n z.1 z.2 k))
    (hfp : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aplus ℓ n z))
    (hfm : ∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (aminus ℓ n z))
    (spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (rootMass : ℕ → ℝ) (hN : ∀ n, 0 < rootMass n)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hRoot : ∀ n, volume (rootDomain n) = ENNReal.ofReal (rootMass n))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hEp : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (hEm : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (fun z ↦ z.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)
    (f : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
    let sourceEscape := fun (n : ℕ)
      (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
      (Ktarget : Set ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)) ↦
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) w).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z (tsupport f ×ˢ Ktargetᶜ)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    let targetEscape := fun (n : ℕ)
      (allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
      (Ksource : Set ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)) ↦
      ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ allocation (fun z ↦ z.1) w).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z (Ksourceᶜ ×ˢ tsupport f)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ Ksource Ktarget : Set ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ),
        IsCompact Ksource ∧ IsCompact Ktarget ∧ ∀ᶠ n in atTop, ∀ ℓ,
          (sourceEscape n (aplus ℓ n) Ktarget ≤ ε ∧ targetEscape n (aplus ℓ n) Ksource ≤ ε) ∧
          (sourceEscape n (aminus ℓ n) Ktarget ≤ ε ∧ targetEscape n (aminus ℓ n) Ksource ≤ ε) := by
  let _inst : MetricSpace M := F.metricSpace
  let U := physicalSceneTestSpatialWindow f
  have hU := isCompact_physicalSceneTestSpatialWindow f
  obtain ⟨W, hUW⟩ := hU.isBounded.exists_norm_le
  have hW : ∀ y ∈ tsupport f, ‖y.1‖ ≤ W := fun y hy ↦
    hUW y.1 (mem_image_of_mem Prod.fst hy)
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (spatialScale n)
  have htight := exists_original_fixed_seed_uniform_both_tail_tightness
    hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
    hgap hdist j aplus aminus hplus hminus hfp hfm spatialScale hsp hscale
    rootMass hN rootDomain hRoot C hC hEp hEm U hU.measurableSet hU.measure_ne_top
  have hYB (n : ℕ) : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      ∀ k, w.1 k ∈ B := by
    apply ae_all_iff.mpr
    intro k
    have hm : Measurable (fun w : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) ↦ w.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    apply ae_of_ae_map (p := fun y : M ↦ y ∈ B) hm.aemeasurable
    rw [physicalSceneOriginalDirichlet_target_law ν n k]
    exact hν
  have hcarriedplus (ℓ n : ℕ) := ae_physicalSceneGlobalAllocationFamily_carried
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ (aplus ℓ n)
    (fun z ↦ z.1) (fun z ↦ z.2) (hfp ℓ n) hA.measurableSet hB.measurableSet hμ (hYB n)
  have hcarriedminus (ℓ n : ℕ) := ae_physicalSceneGlobalAllocationFamily_carried
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ (aminus ℓ n)
    (fun z ↦ z.1) (fun z ↦ z.2) (hfm ℓ n) hA.measurableSet hB.measurableSet hμ (hYB n)
  dsimp only
  intro ε hε
  obtain ⟨threshold, _htpos, htt, htail⟩ := htight ε hε
  let R := Real.sqrt threshold.toReal + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hthreshold : threshold ≤ ENNReal.ofReal (R ^ 2) := by
    rw [ENNReal.le_ofReal_iff_toReal_le htt (sq_nonneg R)]
    have hsqrt := Real.sqrt_nonneg threshold.toReal
    have hsquare := Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ threshold.toReal)
    dsimp only [R]
    nlinarith
  let Ksource : Set ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) :=
    physicalSceneSpatialClockCutoff W R (u '' A)
  let Ktarget : Set ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) :=
    physicalSceneSpatialClockCutoff W R (u '' B)
  refine ⟨Ksource, Ktarget,
    isCompact_physicalSceneSpatialClockCutoff W R (hA.image hu.continuous),
    isCompact_physicalSceneSpatialClockCutoff W R (hB.image hu.continuous), ?_⟩
  filter_upwards [htail] with n hn ℓ
  have hp := lintegral_physicalSceneRootedPlan_compact_test_escapes_le_longTails
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    (physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (fun z ↦ z.1)) hA hB (hcarriedplus ℓ n)
    (coord n) (hcoord n) u hu.continuous H (rootMass n) (rootDomain n) f W R hW hR.le
    threshold hthreshold
  have hm := lintegral_physicalSceneRootedPlan_compact_test_escapes_le_longTails
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    (physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (fun z ↦ z.1)) hA hB (hcarriedminus ℓ n)
    (coord n) (hcoord n) u hu.continuous H (rootMass n) (rootDomain n) f W R hW hR.le
    threshold hthreshold
  exact ⟨⟨hp.1.trans (hn ℓ).1.1, hp.2.trans (hn ℓ).1.2⟩,
    ⟨hm.1.trans (hn ℓ).2.1, hm.2.trans (hn ℓ).2.2⟩⟩

end OTSelector.Reconstruction
