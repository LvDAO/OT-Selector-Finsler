import OTSelector.Reconstruction.FinslerPhysicalSceneSignedExpectedConvolutionGapLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneSignedOriginalProbeGapLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneCommonGridRefining
import OTSelector.MeasureTheory.NormalizedCompactHaarProbe
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalUncutMacroClockGap

/-!
# Original fixed-seed signed probe gaps vanish

Common original root laws, uncut compact probe gaps and uniform real freezing
recover the original finite-plan readouts without new population restrictions.
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

local instance originalSeedProbeRefinementStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalSeedProbeRefinementConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalSeedProbeRefinementConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalSeedProbeRefinementConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalSeedProbeRefinementPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


variable (j : ℕ)
set_option quotPrecheck false
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The original opposite-tilt allocations admit common sample/tilt
subsequences on which every compact seed-coordinate probe has vanishing
expected absolute gap. The extraction is independent of the probe. -/
theorem exists_original_seed_macro_clock_probe_gap_curry_zero_refining_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M}
    (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (n : ℝ) + 1)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobeBound : ∀ x y, |probe x y| ≤ G)
    (t : ℕ → ℝ) (ht0 : ∀ ℓ, 0 ≤ t ℓ) (ht0lim : Tendsto t atTop (𝓝 0))
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j))
    (hp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            t ℓ * probe x (w.1 j)) (ap ℓ n w))
    (hm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            (-t ℓ) * probe x (w.1 j)) (am ℓ n w))
    (hμlaw : PopulationConditionalWindowLaw P a κ (μ.map a) μ ρ₀ v)
    (hνlaw : PopulationConditionalWindowLaw P a κ (μ.map a) ν ρ₁ v)
    (hAsupport : IsCompact A) (hBsupport : IsCompact B) (hAB : Disjoint A B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hbalance : μ.map a = ν.map a)
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
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hnearRadius : 0 < nearRadius)
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
    (φ₀ : ℕ → ℕ → ℕ) (hφ₀ : ∀ ℓ, StrictMono (φ₀ ℓ))
    (ψ₀ : ℕ → ℕ) (hψ₀ : StrictMono ψ₀)
    :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let Γp := fun ℓ n w ↦ (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w).restrict (H ×ˢ univ)
    let Γm := fun ℓ n w ↦ (physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w).restrict (H ×ˢ univ)
    ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ),
          Tendsto (fun p : ℕ × ℕ ↦ ∫⁻ w, ENNReal.ofReal
            |(∫ e, g (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1,
                  (u e.1, u e.2)) ∂Γp (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)) w) -
              ∫ e, g (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1,
                  (u e.1, u e.2)) ∂Γm (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)) w|
            ∂((Measure.pi (fun _ : Fin (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2) + 1) ↦ ν)).prod
              (dirichletOne (φ₀ (ψ₀ (ψ p.1)) (φ (ψ₀ (ψ p.1)) p.2)))))
            ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H Γp Γm
  let V := Fin (finrank ℝ (P j).seed.covector.ker) → ℝ
  let base : V × ℝ := 0
  let Penv := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n)
  have huM : Measurable u := hu.continuous.measurable
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  have hfp (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ w.2 (ap ℓ n w) :=
    (hp ℓ n).mono fun _ hw ↦ hw.1
  have hfm (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ w.2 (am ℓ n w) :=
    (hm ℓ n).mono fun _ hw ↦ hw.1
  have hΓp (ℓ n : ℕ) : Measurable (Γp ℓ n) :=
    measurable_physicalPlan_sourceRestriction _
      (measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hpm ℓ n)
        (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)) H hH
  have hΓm (ℓ n : ℕ) : Measurable (Γm ℓ n) :=
    measurable_physicalPlan_sourceRestriction _
      (measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hmm ℓ n)
        (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)) H hH
  have hmass (alloc : ∀ ℓ n, ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
      (hf : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ w.2 (alloc ℓ n w))
      (ℓ n : ℕ) : ∀ᵐ w ∂Penv n,
        ((physicalSceneGlobalAllocationFamily μ (alloc ℓ n) (fun w ↦ w.1) w).restrict
          (H ×ˢ univ)) univ ≤ 1 := by
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq (Penv n) μ (alloc ℓ n)
      (fun w ↦ w.1) (fun w ↦ w.2) (hf ℓ n), hf ℓ n] with w heq hw
    calc
      _ ≤ physicalSceneGlobalAllocationFamily μ (alloc ℓ n) (fun w ↦ w.1) w univ :=
        Measure.restrict_le_self _
      _ = μ univ := by
        rw [heq, ← Measure.fst_univ, physicalSceneAllocationPlan_fst hw (w.1)]
      _ = 1 := measure_univ
  obtain ⟨Q, φnew, hφnew, hinner, R, ψnew, hψnew, houter⟩ :=
    exists_common_refining_grid_actualAllocationRootedMacroscopicSceneLaw base
      id Penv μ ap am hpm hmm (fun n w ↦ w.1)
      (fun n k ↦ (measurable_pi_apply k).comp measurable_fst) (fun n w ↦ w.2)
      hfp hfm (fun _ ↦ H) (fun _ ↦ hH) coord hcoord u huM scale hscalePos (fun n ↦ by simpa only [Fintype.card_fin, id_eq] using hnormalization n) φ₀ ψ₀
  let φ : ℕ → ℕ → ℕ := fun ℓ n ↦ φ₀ ℓ (φnew ℓ n)
  let ψ : ℕ → ℕ := fun ℓ ↦ ψ₀ (ψnew ℓ)
  have hφ (ℓ : ℕ) : StrictMono (φ ℓ) := (hφ₀ ℓ).comp (hφnew ℓ)
  have hψ : StrictMono ψ := hψ₀.comp hψnew
  obtain ⟨η, hη, hηmass⟩ := exists_nonnegative_normalized_compact_Haar_probe (ι := Fin (finrank ℝ (P j).seed.covector.ker))
  refine ⟨φnew, hφnew, ψnew, hψnew, ?_⟩
  intro g
  let sample : ℕ × ℕ → ℕ := fun p ↦ φ (ψ p.1) p.2
  have hsample : Tendsto sample ((atTop : Filter ℕ).curry atTop) atTop :=
    Filter.Tendsto.curry (Eventually.of_forall fun ℓ ↦ (hφ (ψ ℓ)).tendsto_atTop)
  have hmacro (s : ℝ) (z : V) : physicalSceneMacroscopicRoot s z = s⁻¹ • z := by
    ext k
    change z k / s = s⁻¹ * z k
    simp only [div_eq_mul_inv, mul_comm]
  have hgap (idx : Fin (finrank ℝ (P j).seed.covector.ker) → ℤ) :=
    tendsto_original_full_macro_clock_probe_abs_gap_curry_zero_of_face j base
      hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
      scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
      ap am hpm hmm hp hm
      (fun n ↦ physicalSceneRootGridDomain (scale n) idx)
      (fun n ↦ (volume_physicalSceneRootGridDomain (scale n) (hscalePos n) idx).trans
        (congrArg ENNReal.ofReal (by simpa only [Fintype.card_fin] using hnormalization n)))
      hμlaw hνlaw hAsupport hBsupport hAB hμreg hνreg hκ hbalance hcore hrecovery hface
      hμA hνB hnearRadius Energy hEnergy hEp hEm
      (BoxIntegral.Box.Icc (BoxIntegral.unitPartition.box 1 idx))
      (BoxIntegral.unitPartition.box 1 idx).isCompact_Icc
      (fun n z hz ↦ by rw [hmacro]; exact physicalSceneRootGridDomain_macro_mem_compact (scale n) idx hz)
      η g (Q idx) (R idx) φ hφ ψ hψ (hinner idx) (houter idx)
  have hconv := tendsto_expected_real_macroProbe_convolution_gap_zero_of_root_gaps
    (fun p ↦ Penv (sample p))
    (fun p ↦ Γp (ψ p.1) (sample p)) (fun p ↦ Γm (ψ p.1) (sample p))
    (fun p ↦ hΓp (ψ p.1) (sample p)) (fun p ↦ hΓm (ψ p.1) (sample p))
    (fun p ↦ coord (sample p)) (fun p ↦ hcoord (sample p)) u huM
    (fun p ↦ scale (sample p)) (fun p ↦ (sample p : ℝ) + 1)
    (fun p ↦ hscalePos (sample p)) (fun p ↦ by positivity)
    (fun p ↦ by simpa only [Fintype.card_fin] using hnormalization (sample p)) η hη g
    (fun idx ↦ by
      simpa only [physicalSceneRealMacroClockProbe, hmacro] using hgap idx)
  have hfinal := tendsto_expected_original_real_macroProbe_gap_zero_of_convolution_gap
    (fun p ↦ Penv (sample p)) (fun p ↦ by simp [Penv])
    (fun p ↦ Γp (ψ p.1) (sample p)) (fun p ↦ Γm (ψ p.1) (sample p))
    (fun p ↦ hmass ap hfp (ψ p.1) (sample p))
    (fun p ↦ hmass am hfm (ψ p.1) (sample p))
    (fun p ↦ coord (sample p)) (fun p ↦ hcoord (sample p)) u huM
    scale hscalePos hscale sample hsample η hη hηmass g hconv
  simpa only [coord, physicalSceneOriginalSeedScaledPosition, smul_smul,
    inv_mul_cancel₀ (hscalePos _).ne', one_smul] using hfinal

end OTSelector.Reconstruction
