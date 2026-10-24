import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedProbeCutoffBudget
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedCutoffErrorAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockScreenAccuracy

/-!
# Accuracy-last cutoff of the entire original fixed-seed clock probe

The original face constructs a small-screen core with small population loss.
Its finite number of near pieces and coercivity are fixed before choosing the
radius. One target cutoff then works for every tilt and sample size, with only
an actual true-energy error tending to zero as sample size grows.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

local instance originalFixedSeedCutoffAccuracyStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFixedSeedCutoffAccuracyConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalFixedSeedCutoffAccuracyConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFixedSeedCutoffAccuracyConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFixedSeedCutoffAccuracyPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ}

variable (j : ℕ)
set_option quotPrecheck false
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Entire original fixed-seed probes admit one fixed target cutoff at each
accuracy, uniformly over both global allocation families and all tilt indices. -/
theorem exists_original_fixed_seed_macro_clock_probe_cutoff_accuracy_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ i, (κ i).IsAddHaarMeasure)
    (hbalance : μ.map a = ν.map a)
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
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
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 k))
    (hfp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap ℓ n w))
    (hfm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am ℓ n w))
    (Energy : ℝ≥0∞) (hEnergy : Energy ≠ ⊤)
    (hEp : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (hEm : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (η : C_c(Fin (finrank ℝ (P j).seed.covector.ker) → ℝ, ℝ))
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ))
    (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let Γ := fun ℓ n (plus : Bool) ↦ physicalSceneGlobalAllocationFamily μ
      (if plus then ap ℓ n else am ℓ n) (fun w ↦ w.1)
    ∃ χ : C_c(Point, ℝ), (∀ y, χ y ∈ Icc 0 1) ∧
      ∃ sample : ℕ → ℝ≥0∞, Tendsto sample atTop (𝓝 0) ∧
      ∀ rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ),
      (∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1)) →
      ∀ (ℓ n : ℕ) (plus : Bool) (rootTag :
        (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) →
          (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      (∫⁻ w, ∫⁻ z, ∫⁻ e, ENNReal.ofReal
        |η e.1.1 * g (rootTag z, (e.1.2, e.2.2)) -
          (η e.1.1 * g (rootTag z, (e.1.2, e.2.2))) * χ e.2|
          ∂physicalSceneRootedPlan ((Γ ℓ n plus w).restrict (H ×ˢ univ))
            (coord n) u ((n : ℝ) + 1) z
          ∂cavityRootMeasure volume (rootDomain n) ((n : ℝ) + 1)
          ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
        ENNReal.ofReal accuracy + sample n := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H coord Γ
  obtain ⟨W, hW⟩ := η.hasCompactSupport.isBounded.exists_norm_le
  let U := Metric.ball (0 : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) (|W| + 1)
  have hU : IsOpen U := Metric.isOpen_ball
  have hUf : volume U ≠ ⊤ := measure_ball_lt_top.ne
  have hηU : tsupport η ⊆ U := by
    intro x hx
    change dist x 0 < |W| + 1
    rw [dist_zero_right]
    linarith [(hW x hx).trans (le_abs_self W)]
  have hUW : ∀ x ∈ U, ‖x‖ ≤ |W| + 1 := by
    intro x hx
    exact (by simpa only [U, Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < |W| + 1).le
  let L : ℝ≥0∞ := ENNReal.ofReal
    (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖)
  have hL : L ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμAs : ∀ᵐ x ∂μ, x ∈ A := hμA
  have hνBs : ∀ᵐ y ∂ν, y ∈ B := hνB
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hA hB hAB
  obtain ⟨Dseq, hscreen, _hμtail, _hνtail, hpopulation⟩ :=
    exists_original_small_clock_screen_core_sequence_of_face hcore hrecovery hF hcomplete hu ha hinj
      hκ hbalance hA hB hμAs hνBs hνreg hμreg hface (by positivity : 0 < gap / 2)
  have hpopulationError : Tendsto (fun k ↦ L * (volume U *
      (μ (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ + ν (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ)))
      atTop (𝓝 0) := by
    have hv := ENNReal.Tendsto.const_mul hpopulation (Or.inr hUf)
    have hLmul := ENNReal.Tendsto.const_mul hv (Or.inr hL)
    simpa only [mul_zero] using hLmul
  obtain ⟨k, hk⟩ := ((tendsto_order.mp hpopulationError).2
    (ENNReal.ofReal (accuracy / 2)) (ENNReal.ofReal_pos.mpr (by positivity))).exists
  obtain ⟨q, hq, c, hc, hbudget⟩ :=
    (Dseq k).exists_original_fixed_seed_macro_clock_probe_cutoff_budget
      hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hB
      hμAs hνBs hgap hdist (hscreen k)
  obtain ⟨R, hR, sample, hsample, hnumeric⟩ := exists_fixed_seed_cutoff_error_accuracy
    L (volume U) Energy
    (μ (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ + ν (⋃ i, (Dseq k).physicalCoreDomain i)ᶜ)
    hL hUf hEnergy (Dseq k).haar.continuous.count q c hq hc
    scale hscalePos hscale accuracy haccuracy hk.le
  obtain ⟨χ, hχ, _hχK, hcutoff⟩ :=
    hbudget j U hU.measurableSet hUf R (|W| + 1) hR hUW η g hηU
  refine ⟨χ, hχ, sample, hsample, ?_⟩
  intro rootDomain hrootDomain ℓ n plus rootTag
  have halloc : ∀ k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦
        (if plus then ap ℓ n else am ℓ n) z.1 z.2 k) := by
    cases plus
    · exact hmm ℓ n
    · exact hpm ℓ n
  have hfeas : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ w.2 ((if plus then ap ℓ n else am ℓ n) w) := by
    cases plus
    · exact hfm ℓ n
    · exact hfp ℓ n
  have henergy : (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂physicalSceneGlobalAllocationFamily μ (if plus then ap ℓ n else am ℓ n) (fun w ↦ w.1) w
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy := by
    cases plus
    · exact hEm ℓ n
    · exact hEp ℓ n
  have hh := hcutoff n (if plus then ap ℓ n else am ℓ n) halloc hfeas
    (scale n) ((n : ℝ) + 1) (hscalePos n) (by positivity)
    (rootDomain n) (hrootDomain n) Energy henergy rootTag
  exact hh.trans (by simpa only [L] using hnumeric n)

end OTSelector.Reconstruction
