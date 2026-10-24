import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedCompactEscape
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitCompactEscapeExhaustion

/-!
# One compact exhaustion for the actual fixed seed scene

Auxiliary cores only estimate the same original scene. Their actual four escape
bounds give one genuine compact exhaustion with a null tolerance sequence,
uniformly in the tilt and eventually in the original sample size.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}


/-- Actual original four escape masses vanish along one fixed compact exhaustion. -/
theorem exists_original_fixed_seed_uniform_compact_escape_exhaustion
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
    ∃ K : CompactExhaustion ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ), ∀ m : ℕ, ∀ᶠ n in atTop, ∀ ℓ,
      (sourceEscape n (aplus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ ∧
        targetEscape n (aplus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) ∧
      (sourceEscape n (aminus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ ∧
        targetEscape n (aminus ℓ n) (K m) ≤ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) := by
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
  have hsmall := exists_original_fixed_seed_uniform_compact_escape
    hcore hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg hface
    hgap hdist j aplus aminus hplus hminus hfp hfm spatialScale hsp hscale
    rootMass hN rootDomain hRoot C hC hEp hEm f
  let tail := fun (ℓ n : ℕ) K ↦ max
    (max (sourceEscape n (aplus ℓ n) K) (targetEscape n (aplus ℓ n) K))
    (max (sourceEscape n (aminus ℓ n) K) (targetEscape n (aminus ℓ n) K))
  have hmonoSource (n : ℕ) allocation : Antitone (sourceEscape n allocation) := by
    intro K L hKL
    apply lintegral_mono
    intro w
    apply lintegral_mono
    intro z
    exact measure_mono (Set.prod_mono_right (Set.compl_subset_compl.mpr hKL))
  have hmonoTarget (n : ℕ) allocation : Antitone (targetEscape n allocation) := by
    intro K L hKL
    apply lintegral_mono
    intro w
    apply lintegral_mono
    intro z
    exact measure_mono (Set.prod_mono_left (Set.compl_subset_compl.mpr hKL))
  have hmono (ℓ n : ℕ) : Antitone (tail ℓ n) := by
    intro K L hKL
    exact max_le_max (max_le_max (hmonoSource n (aplus ℓ n) hKL)
      (hmonoTarget n (aplus ℓ n) hKL))
      (max_le_max (hmonoSource n (aminus ℓ n) hKL)
        (hmonoTarget n (aminus ℓ n) hKL))
  have hsmall' : ∀ ε : ℝ≥0∞, 0 < ε → ∃ L, IsCompact L ∧
      ∀ᶠ n in atTop, ∀ ℓ, tail ℓ n L ≤ ε := by
    intro ε hε
    obtain ⟨Ks, Kt, hKs, hKt, hb⟩ := hsmall ε hε
    refine ⟨Ks ∪ Kt, hKs.union hKt, ?_⟩
    filter_upwards [hb] with n hn ℓ
    exact max_le (max_le
      ((hmonoSource n (aplus ℓ n) subset_union_right).trans (hn ℓ).1.1)
      ((hmonoTarget n (aplus ℓ n) subset_union_left).trans (hn ℓ).1.2))
      (max_le
        ((hmonoSource n (aminus ℓ n) subset_union_right).trans (hn ℓ).2.1)
        ((hmonoTarget n (aminus ℓ n) subset_union_left).trans (hn ℓ).2.2))
  obtain ⟨K, hb⟩ := exists_physicalScene_compact_exhaustion_escape_bounds
    (physicalSceneSpatialClockExhaustion 0 0) tail hmono hsmall'
  refine ⟨K, ?_⟩
  intro m
  filter_upwards [hb m] with n hn ℓ
  exact ⟨⟨(le_max_left _ _).trans ((le_max_left _ _).trans (hn ℓ)),
    (le_max_right _ _).trans ((le_max_left _ _).trans (hn ℓ))⟩,
    ⟨(le_max_left _ _).trans ((le_max_right _ _).trans (hn ℓ)),
      (le_max_right _ _).trans ((le_max_right _ _).trans (hn ℓ))⟩⟩

end OTSelector.Reconstruction
