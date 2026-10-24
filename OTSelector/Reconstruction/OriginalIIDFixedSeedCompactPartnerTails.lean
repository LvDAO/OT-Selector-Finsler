import OTSelector.Reconstruction.OriginalIIDFixedSeedTailTightness
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedCompactEscape

/-!
# Compact partner tails of the unchanged original iid optimizer

The actual two-color finite-array experiment retains its deterministic original
seed source restriction. Its original population supports give the true compact
clock carriers, and the proved full spatial tails give compact partner cutoffs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

section Carriers
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}

/-- The unchanged actual iid optimizer is almost surely carried by the original
population supports. This follows from its exact mean marginals, before any
seed restriction or rooted observation. -/
theorem ae_originalIIDOptimalPhysicalPlan_carried [NeZero n]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) (scale : ℝ)
    {A : Set X} {B : Set Y} (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    ∀ᵐ w ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))),
      ∀ᵐ p ∂originalIIDOptimalPhysicalPlan cost scale w, p.1 ∈ A ∧ p.2 ∈ B := by
  have hsource : ∀ᵐ p ∂originalIIDOptimalMeanPlan μ ν cost scale n, p.1 ∈ A := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [originalIIDOptimalMeanPlan_source μ ν cost hcost scale]
    exact hμ
  have htarget : ∀ᵐ p ∂originalIIDOptimalMeanPlan μ ν cost scale n, p.2 ∈ B := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [originalIIDOptimalMeanPlan_target μ ν cost hcost scale]
    exact hν
  apply Measure.ae_ae_of_ae_bind
    (measurable_originalIIDOptimalPhysicalPlan cost hcost scale).aemeasurable
  exact hsource.and htarget

end Carriers

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}


/-- The same original iid optimizer has eventually small compact partner
escapes over every actual compact test, uniformly over the selected cost index.
The compact partner windows include the unchanged original clock carriers. -/
theorem exists_originalIID_fixed_seed_uniform_compact_escape
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
    (j : ℕ) {I : Type*}
    (cost : I → ℕ → M → M → ℝ)
    (hcost : ∀ ℓ n, Measurable (Function.uncurry (cost ℓ n)))
    (selectionScale : I → ℕ → ℝ)
    (spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (rootMass : ℕ → ℝ) (hN : ∀ n, 0 < rootMass n)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hRoot : ∀ n, volume (rootDomain n) = ENNReal.ofReal (rootMass n))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop, ∀ ℓ : I,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n + 1) (cost ℓ n) (selectionScale ℓ n) w
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C)
    (f : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ)) :
    let H := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition
      (P := P) (a := a) j (spatialScale n)
    let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun ℓ n ↦ originalIIDOptimalPhysicalPlan
      (n := n + 1) (cost ℓ n) (selectionScale ℓ n)
    let sourceEscape := fun ℓ n Ktarget ↦ ∫⁻ w, ∫⁻ z,
      physicalSceneRootedPlan ((Γ ℓ n w).restrict (H ×ˢ univ)) (coord n) u
        (rootMass n) z (tsupport f ×ˢ Ktargetᶜ)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
    let targetEscape := fun ℓ n Ksource ↦ ∫⁻ w, ∫⁻ z,
      physicalSceneRootedPlan ((Γ ℓ n w).restrict (H ×ˢ univ)) (coord n) u
        (rootMass n) z (Ksourceᶜ ×ˢ tsupport f)
        ∂cavityRootMeasure volume (rootDomain n) (rootMass n) ∂Penv n
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ Ksource Ktarget : Set ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ),
        IsCompact Ksource ∧ IsCompact Ktarget ∧ ∀ᶠ n in atTop, ∀ ℓ : I,
          sourceEscape ℓ n Ktarget ≤ ε ∧ targetEscape ℓ n Ksource ≤ ε := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  let U := physicalSceneTestSpatialWindow f
  have hU := isCompact_physicalSceneTestSpatialWindow f
  obtain ⟨W, hUW⟩ := hU.isBounded.exists_norm_le
  have hW : ∀ y ∈ tsupport f, ‖y.1‖ ≤ W := fun y hy ↦
    hUW y.1 (mem_image_of_mem Prod.fst hy)
  let H := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition
    (P := P) (a := a) j (spatialScale n)
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let Γ := fun ℓ n ↦ originalIIDOptimalPhysicalPlan
    (n := n + 1) (cost ℓ n) (selectionScale ℓ n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (spatialScale n)
  have htight := exists_originalIID_fixed_seed_uniform_both_tail_tightness
    hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
    hgap hdist j cost hcost selectionScale spatialScale hsp hscale
    rootMass hN rootDomain hRoot C hC henergy U hU.measurableSet hU.measure_ne_top
  have hcarried (ℓ : I) (n : ℕ) : ∀ᵐ w ∂Penv n,
      ∀ᵐ p ∂Γ ℓ n w, p.1 ∈ A ∧ p.2 ∈ B :=
    ae_originalIIDOptimalPhysicalPlan_carried μ ν (cost ℓ n) (hcost ℓ n)
      (selectionScale ℓ n) hμ hν
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
    (Penv n) (Γ ℓ n) hA hB (hcarried ℓ n)
    (coord n) (hcoord n) u hu.continuous H (rootMass n) (rootDomain n) f W R hW hR.le
    threshold hthreshold
  exact ⟨hp.1.trans (hn ℓ).1, hp.2.trans (hn ℓ).2⟩

end OTSelector.Reconstruction


