import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedTargetDefect
import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenOriginal

/-!
# Vanishing actual target-test defects in the same original seed scene

For each requested accuracy, the original optimal face and original Haar
recovery supply an auxiliary core with small population losses.  The fixed-seed
crossing estimate then leaves only that chosen loss and a true energy term that
vanishes with the original spatial scale.  The physical scene does not change
when the auxiliary accuracy changes; the tilt and sample indices stay separate.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Choosing an auxiliary physical accuracy before the original sample size
forces the same actual readout to vanish.  The auxiliary constant may depend on
the requested accuracy, and its energy scale diverges only afterward. -/
theorem tendsto_zero_of_auxiliary_small_mass_energy_bounds
    (mass : ℕ → ℝ≥0∞) (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (A C : ℝ≥0∞) (hA : A ≠ ⊤) (hC : C ≠ ⊤)
    (hbound : ∀ δ : ℝ≥0, 0 < δ → ∃ c > 0, ∀ n,
      mass n ≤ A * ((δ : ℝ≥0∞) + C / ENNReal.ofReal (scale n * c))) :
    Tendsto mass atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨δ, hδ, hδA⟩ := ENNReal.exists_nnreal_pos_mul_lt hA hhalf.ne'
  obtain ⟨c, hc, hb⟩ := hbound δ hδ
  have hden : Tendsto (fun n ↦ ENNReal.ofReal (scale n * c)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr (hscale.atTop_mul_const hc)
  have hdiv : Tendsto (fun n ↦ C / ENNReal.ofReal (scale n * c)) atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      (ENNReal.Tendsto.div tendsto_const_nhds (Or.inr (by simp)) hden (Or.inr hC))
  have hterm : Tendsto (fun n ↦ A * (C / ENNReal.ofReal (scale n * c))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (ENNReal.continuousAt_const_mul (Or.inl hA)).tendsto.comp hdiv
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hterm) (ε / 2) hhalf] with n hn
  calc
    mass n ≤ A * ((δ : ℝ≥0∞) + C / ENNReal.ofReal (scale n * c)) := hb n
    _ = A * (δ : ℝ≥0∞) + A * (C / ENNReal.ofReal (scale n * c)) := mul_add _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (by simpa only [mul_comm] using hδA.le) hn
    _ = ε := ENNReal.add_halves ε

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- The same original optimal face, original Haar/recovery laws, original
physical support and actual global energy produce vanishing untruncated target
test defects for every fixed tilt index.  Auxiliary cores are estimates only. -/
theorem tendsto_original_fixed_seed_target_test_defect_zero
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
    ∀ ℓ, Tendsto (fun n ↦ ∫⁻ w, ∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ (aplus ℓ n) (fun z ↦ z.1) w).restrict (H ×ˢ univ))
          (coord n) u (rootMass n) z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan
          ((physicalSceneGlobalAllocationFamily μ (aminus ℓ n) (fun z ↦ z.1) w).restrict (H ×ˢ univ))
          (coord n) u (rootMass n) z|
      ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) atTop (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let U := physicalSceneTestSpatialWindow f
  have hU := isCompact_physicalSceneTestSpatialWindow f
  let coeff := 2 * ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U
  have hcoeff : coeff ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hU.measure_ne_top
  dsimp only
  intro ℓ
  have _hroot (n : ℕ) : IsProbabilityMeasure (cavityRootMeasure volume (rootDomain n) (rootMass n)) :=
    isProbabilityMeasure_cavityRootMeasure volume _ _ (hN n) (hRoot n)
  apply tendsto_zero_of_auxiliary_small_mass_energy_bounds _
    (fun n ↦ spatialScale n ^ 2) hscale coeff C hcoeff hC
  intro δ hδ
  let d : ℝ≥0∞ := (δ : ℝ≥0∞) / 4
  have hd : 0 < d := ENNReal.div_pos (by exact_mod_cast hδ.ne') (by norm_num)
  obtain ⟨D, hscreen, hμtail, hνtail⟩ :=
    exists_original_small_clock_screen_population_core_of_face hcore hrecovery
      hF hcomplete hu ha hinj hκ hbalance hA hB hμ hν hreg hμreg hface
      (half_pos hgap) hd.ne' hd.ne'
  have htails : μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤
      (δ : ℝ≥0∞) := by
    apply (add_le_add hμtail hνtail).trans_eq
    calc
      _ = 4 * ((δ : ℝ≥0∞) / 4) := by dsimp only [d]; ring
      _ = _ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  obtain ⟨c, hc, hb⟩ := D.exists_original_fixed_seed_target_test_defect_bounds
    hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμ hν hgap hdist hscreen
  refine ⟨c, hc, ?_⟩
  intro n
  have hbN := hb j n (aplus ℓ n) (aminus ℓ n) (hplus ℓ n) (hminus ℓ n)
    (hfp ℓ n) (hfm ℓ n) (spatialScale n) (rootMass n) (hsp n) (hN n)
    (rootDomain n) U hU.measurableSet f (fun y hy ↦ mem_image_of_mem Prod.fst hy) C
    (hEp ℓ n) (hEm ℓ n)
  refine hbN.trans ?_
  change coeff * (_ + _) ≤ coeff * (_ + _)
  exact mul_le_mul_right (add_le_add htails le_rfl) _

end OTSelector.Reconstruction
