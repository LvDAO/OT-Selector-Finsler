import OTSelector.Reconstruction.OriginalIIDFixedSeedTargetDefect
import OTSelector.Reconstruction.OriginalIIDFixedSeedCompactPartnerTails
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale

/-! Exact and asymptotic endpoint guards for the same original iid optimizer.
Source restriction is literal, regularity is inherited from the original
populations, and nonnegative physical seed crossing mass is removed using the
actual energy and original auxiliary-core producer. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section ExactGuards
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The original source restriction already makes the outside-source guard
identically zero, before any limit or energy argument. -/
theorem sourceRestriction_outside_source_eq_zero (Γ : Measure (X × Y))
    {H : Set X} (hH : MeasurableSet H) :
    (Γ.restrict (H ×ˢ univ)).restrict (Hᶜ ×ˢ univ) = 0 := by
  rw [Measure.restrict_restrict ((hH.compl).prod MeasurableSet.univ)]
  have he : (Hᶜ ×ˢ (univ : Set Y)) ∩ (H ×ˢ univ) = ∅ := by
    ext p; simp
  rw [he,Measure.restrict_empty]

/-- The unchanged actual iid arrays already carry both original endpoint
support properties. The same source-restricted optimizer has exactly zero bad
support measure; in particular this removes the original regularity guards. -/
theorem ae_originalIID_sourceRestriction_bad_support_eq_zero
    {n : ℕ} [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) (selectionScale : ℝ)
    {A : Set X} {B : Set Y} (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (H : Set X) :
    ∀ᵐ ξ ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)),
      ((originalIIDOptimalPhysicalPlan cost selectionScale ξ).restrict (H ×ˢ univ)).restrict
        (A ×ˢ B)ᶜ = 0 := by
  filter_upwards [ae_originalIIDOptimalPhysicalPlan_carried μ ν cost hcost selectionScale hμ hν]
    with ξ hξ
  apply Measure.restrict_eq_zero.mpr
  exact ae_iff.mp (ae_restrict_of_ae hξ)

end ExactGuards

section RootedSeedEscape
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]

/-- Taking the bad target part of the SAME source-restricted optimizer is
exactly its physical H×Hᶜ restriction. This is a readout identity, not a new plan. -/
theorem sourceRestriction_outside_target_eq_crossing_restriction
    (Γ : Measure (M × M)) {H : Set M} (hH : MeasurableSet H) :
    (Γ.restrict (H ×ˢ univ)).restrict (univ ×ˢ Hᶜ) = Γ.restrict (H ×ˢ Hᶜ) := by
  rw [Measure.restrict_restrict (MeasurableSet.univ.prod hH.compl)]
  congr 1
  ext p
  simp [and_comm]

/-- Genuine target points outside H are counted in the same physical plan.
The source or target spatial window is selected by color; no coordinate fallback
is used to replace a physical endpoint or to change its seed membership. -/
def rootedPhysicalSeedTargetEscapeMass
    (Γ : Measure (M × M)) (H : Set M) (coord : M → (ι → ℝ))
    (N : ℝ) (U : Set (ι → ℝ)) (color : Fin 2) (root : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal N * cavityRootWindowReadout (Γ.restrict (H ×ˢ Hᶜ))
    (fun p ↦ coord (if color = 0 then p.1 else p.2)) (fun _ ↦ 1) U root

/-- Exact Haar averaging pays real target seed escape by the same original
crossing mass, for either bounded endpoint window and the same root law. -/
theorem lintegral_rootedPhysicalSeedTargetEscapeMass_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ] (H : Set M)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (N : ℝ) (hN : 0 < N) (rootDomain U : Set (ι → ℝ))
    (hU : MeasurableSet U) (color : Fin 2) :
    (∫⁻ root, rootedPhysicalSeedTargetEscapeMass Γ H coord N U color root
      ∂cavityRootMeasure volume rootDomain N) ≤ volume U * Γ (physicalSceneCoreCrossing H) := by
  have hloc : Measurable (fun p : M × M ↦ coord (if color = 0 then p.1 else p.2)) := by
    by_cases hc : color = 0
    · simpa only [ite_eq_left hc,Function.comp_def] using hcoord.comp measurable_fst
    · simpa only [ite_eq_right hc,Function.comp_def] using hcoord.comp measurable_snd
  have h := lintegral_cavityRoot_scaled_window_le volume (Γ.restrict (H ×ˢ Hᶜ))
    _ hloc (fun _ ↦ 1) measurable_const U hU rootDomain N hN
  change (∫⁻ root, rootedPhysicalSeedTargetEscapeMass Γ H coord N U color root
    ∂cavityRootMeasure volume rootDomain N) ≤ _ at h
  refine h.trans ?_
  simp only [lintegral_const,one_mul,Measure.restrict_apply_univ]
  exact mul_le_mul_of_nonneg_left (measure_mono (fun p hp ↦ Or.inl hp)) bot_le

end RootedSeedEscape

section OriginalSeedCrossing
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- True nonnegative crossing mass of the actual original iid optimizer
vanishes. The original finite energy budget and original face/core producer are
used internally; no target-defect cancellation or desired retention is assumed. -/
theorem tendsto_originalIID_fixed_seed_crossing_mass_zero
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
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
    (j : ℕ) (cost : ℕ → M → M → ℝ)
    (hcost : ∀ n, Measurable (Function.uncurry (cost n))) (selectionScale spatialScale : ℕ → ℝ)
    (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ C) :
    let H := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    Tendsto (fun n ↦ ∫⁻ ξ, (originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ)
      (physicalSceneCoreCrossing H)
      ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ ν))) atTop (𝓝 0) := by
  letI : MetricSpace M := F.metricSpace
  let H := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let defect := fun n ↦ ∫⁻ ξ, (originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ)
    (physicalSceneCoreCrossing H)
    ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp henergy
  let mass := fun n ↦ if N₀ ≤ n then defect n else 0
  have hvanish : Tendsto mass atTop (𝓝 0) := by
    apply tendsto_zero_of_auxiliary_small_mass_energy_bounds mass
      (fun n ↦ spatialScale n ^ 2) hscale 1 C (by simp) hC
    intro δ hδ
    let d : ℝ≥0∞ := (δ : ℝ≥0∞) / 4
    have hd : 0 < d := ENNReal.div_pos (by exact_mod_cast hδ.ne') (by norm_num)
    obtain ⟨D,hscreen,hμtail,hνtail⟩ :=
      exists_original_small_clock_screen_population_core_of_face hcore hrecovery
        hF hcomplete hu ha hinj hκ hbalance hA hB hμ hν hreg hμreg hface
        (half_pos hgap) hd.ne' hd.ne'
    have htails : μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤
        (δ : ℝ≥0∞) := by
      apply (add_le_add hμtail hνtail).trans_eq
      calc
        _ = 4 * ((δ : ℝ≥0∞) / 4) := by dsimp only [d]; ring
        _ = _ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
    obtain ⟨c,hc,hmass⟩ := D.exists_originalIID_fullNonNear_mass_bound
      hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμ hν
      hgap hdist (show (0 : ℝ) < 1 by norm_num) hscreen
    refine ⟨c,hc,?_⟩
    intro n
    by_cases hn : N₀ ≤ n
    · have hcover : physicalSceneCoreCrossing H ⊆
          (((⋃ i, D.nearDisplacementEvent i 1) ∩ (A ×ˢ B))ᶜ) := by
        intro p hp hpnear
        have hc := D.fixed_seed_crossing_subset_global_nonNear j A B 1 ⟨hp,hpnear.2⟩
        exact hc.2 hpnear.1
      have hb := (lintegral_mono (fun ξ ↦ measure_mono (μ :=
          originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ) hcover)).trans
        (hmass (n+1) (Nat.succ_pos n) (cost n) (hcost n) (selectionScale n)
          (spatialScale n ^ 2) (sq_pos_of_pos (hsp n)) C (hN₀ n hn))
      change (if N₀ ≤ n then defect n else 0) ≤ _
      rw [ite_eq_left hn,one_mul]
      exact hb.trans (add_le_add htails le_rfl)
    · simp only [mass,ite_eq_right hn]
      exact zero_le
  have heq : mass =ᶠ[atTop] defect := by
    filter_upwards [eventually_ge_atTop N₀] with n hn
    simp only [mass,ite_eq_left hn]
  exact hvanish.congr' heq


/-- Real target points outside the original fixed source seed have vanishing
bounded-window Haar-averaged mass in the SAME full iid optimizer restricted to
H×univ. The integer prefactor and canonical root mass remain exactly n+1. -/
theorem tendsto_originalIID_fixed_seed_target_escape_windows_zero
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
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
    (j : ℕ) (cost : ℕ → M → M → ℝ)
    (hcost : ∀ n, Measurable (Function.uncurry (cost n))) (selectionScale spatialScale : ℕ → ℝ)
    (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ C)
    (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤) (color : Fin 2) :
    let H := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
    let q := finrank ℝ (P j).seed.covector.ker
    let N := fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)
    let roots := fun n ↦ haarRootCube (Fin q) (haarRootRadius q (N n))
    Tendsto (fun n ↦ ∫⁻ ξ, ∫⁻ root,
      rootedPhysicalSeedTargetEscapeMass
        (originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ)
        H (coord n) (N n) U color root
      ∂cavityRootMeasure volume (roots n) (N n)
      ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ ν))) atTop (𝓝 0) := by
  letI : MetricSpace M := F.metricSpace
  intro H coord q N roots
  have hcross := tendsto_originalIID_fixed_seed_crossing_mass_zero hcore hrecovery
    hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
    hgap hdist j cost hcost selectionScale spatialScale hsp hscale C hC henergy
  have hupper := ENNReal.Tendsto.const_mul hcross (Or.inr hUf)
  simp only [mul_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ ↦ bot_le)
  intro n
  calc
    _ ≤ ∫⁻ ξ, volume U *
        (originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ)
          (physicalSceneCoreCrossing H)
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν)) := by
      apply lintegral_mono
      intro ξ
      exact lintegral_rootedPhysicalSeedTargetEscapeMass_le _ H (coord n)
        (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (spatialScale n))
        (N n) (by dsimp [N]; positivity) (roots n) U hU color
    _ = _ := lintegral_const_mul' _ _ hUf

end OriginalSeedCrossing
end OTSelector.Reconstruction
