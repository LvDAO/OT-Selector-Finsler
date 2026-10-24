import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalOptimalProbeDetermination
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeIteratedWeakExpectation
import OTSelector.Topology.CurriedIteratedLimit

/-!
# Agreement on one original weak law from the actual iterated probe gaps

The two original probability-plan weak stages are kept fixed. The actual
curried seed gaps force zero expectation on that same limiting law. Original
face geometry and the fixed countable probes then identify its full plans.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ : M → ℝ} {v : ℕ → E → ℝ}
variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (hlaw : PopulationConditionalWindowLaw P a κ lambda μ ρ v)
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hκ : ∀ j, SigmaFinite (κ j))
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
include hF hcomplete hu ha hinj hlaw horder hκ hface

/-- The actual seed gap bounds and both original weak stages imply full plan
agreement on the same original limiting law. All probe continuity, integrability,
limit source, regular same-ray support and countable-test steps are internal. -/
theorem ae_original_plans_eq_of_iterated_seed_probe_gaps_of_face :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPolish : PolishSpace M := inferInstance
    ∀ {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
      [OpensMeasurableSpace S] [HasOuterApproxClosed S]
      (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
      (R : ProbabilityMeasure S) (ψ : ℕ → ℕ)
      (_hinner : ∀ ℓ, Tendsto (Pn ℓ) atTop (𝓝 (Q ℓ)))
      (_houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
      (π₀ π₁ : S → ProbabilityMeasure (M × M))
      (_hπ₀ : Continuous π₀) (_hπ₁ : Continuous π₁)
      (_hsource₀ : ∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₀ s : Measure (M × M)).fst = μ)
      (_hsource₁ : ∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₁ s : Measure (M × M)).fst = μ)
      (_hopt₀ : ∀ᵐ s ∂(R : Measure S), IsOptimalCoupling edist μ ν (π₀ s : Measure (M × M)))
      (_hopt₁ : ∀ᵐ s ∂(R : Measure S), IsOptimalCoupling edist μ ν (π₁ s : Measure (M × M)))
      (_hgap : ∀ j : ℕ, ∀ i : ℕ ⊕ (ℕ × ℕ),
        Tendsto (fun p : ℕ × ℕ ↦ ∫⁻ s, ENNReal.ofReal
          |(∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
              (lambda := lambda) j (physicalSceneOriginalSeedSeparatingProbe (P := P) j i)
              e.1 e.2 ∂(π₀ s : Measure (M × M))) -
            ∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
              (lambda := lambda) j (physicalSceneOriginalSeedSeparatingProbe (P := P) j i)
              e.1 e.2 ∂(π₁ s : Measure (M × M))| ∂(Pn (ψ p.1) p.2 : Measure S))
          ((atTop : Filter ℕ).curry atTop) (𝓝 0)),
      ∀ᵐ s ∂(R : Measure S), (π₀ s : Measure (M × M)) = (π₁ s : Measure (M × M)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instFinite : IsFiniteMeasure lambda := hlaw.label_law ▸ inferInstance
  let _instSigma : ∀ j, SigmaFinite (κ j) := hκ
  dsimp only
  intro S instS instM instO instH Pn Q R ψ hinner houter π₀ π₁ hπ₀ hπ₁
    hsource₀ hsource₁ hopt₀ hopt₁ hgap
  apply ae_original_optimal_plans_eq_of_original_seed_probe_ae_eq_of_face
    hF hcomplete hu ha hinj hlaw horder hκ hface (R : Measure S)
    (fun s ↦ (π₀ s : Measure (M × M))) (fun s ↦ (π₁ s : Measure (M × M))) hopt₀ hopt₁
  intro j i
  let g := physicalSceneOriginalSeedSeparatingProbe (P := P) j i
  let obs : S → ℝ := fun s ↦
    |(∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
        (lambda := lambda) j g e.1 e.2 ∂(π₀ s : Measure (M × M))) -
      ∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
        (lambda := lambda) j g e.1 e.2 ∂(π₁ s : Measure (M × M))|
  obtain ⟨_, _, _, hIntR, _, _, hennI, hennO⟩ :=
    original_seed_probe_gap_expectation_limits_of_iterated_weak
      (P := P) (a := a) (κ := κ) (lambda := lambda)
      hF hcomplete hu ha hinj μ j g Pn Q R ψ hinner houter π₀ π₁ hπ₀ hπ₁ hsource₀ hsource₁
  have hzero : (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S)) = 0 :=
    ennreal_iterated_readout_eq_zero_of_curry_tendsto_zero
      (fun ℓ n ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Pn ℓ n : Measure S))
      (fun ℓ ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Q ℓ : Measure S))
      (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S)) ψ hennI hennO (hgap j i)
  have hmeas : AEMeasurable (fun s ↦ ENNReal.ofReal (obs s)) (R : Measure S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hIntR.aestronglyMeasurable.aemeasurable
  have hzAE := (lintegral_eq_zero_iff' hmeas).mp hzero
  filter_upwards [hzAE] with s hs
  have habs : obs s = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hs) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- Local scene extractions may depend on the original seed, provided each
preserves the same original limiting law. No all-seed extraction is required. -/
theorem ae_original_plans_eq_of_seedwise_iterated_probe_gaps_of_face :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPolish : PolishSpace M := inferInstance
    ∀ {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
      [OpensMeasurableSpace S] [HasOuterApproxClosed S]
      (R : ProbabilityMeasure S) (π₀ π₁ : S → ProbabilityMeasure (M × M))
      (_hπ₀ : Continuous π₀) (_hπ₁ : Continuous π₁)
      (_hopt₀ : ∀ᵐ s ∂(R : Measure S), IsOptimalCoupling edist μ ν (π₀ s : Measure (M × M)))
      (_hopt₁ : ∀ᵐ s ∂(R : Measure S), IsOptimalCoupling edist μ ν (π₁ s : Measure (M × M)))
      (_hwitness : ∀ j : ℕ,
        ∃ (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S) (ψ : ℕ → ℕ),
          (∀ ℓ, Tendsto (Pn ℓ) atTop (𝓝 (Q ℓ))) ∧
          Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) ∧
          (∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₀ s : Measure (M × M)).fst = μ) ∧
          (∀ ℓ n, ∀ᵐ s ∂(Pn ℓ n : Measure S), (π₁ s : Measure (M × M)).fst = μ) ∧
          ∀ g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ),
            Tendsto (fun p : ℕ × ℕ ↦ ∫⁻ s, ENNReal.ofReal
              |(∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
                  (lambda := lambda) j g e.1 e.2 ∂(π₀ s : Measure (M × M))) -
                ∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
                  (lambda := lambda) j g e.1 e.2 ∂(π₁ s : Measure (M × M))|
              ∂(Pn (ψ p.1) p.2 : Measure S))
              ((atTop : Filter ℕ).curry atTop) (𝓝 0)),
      ∀ᵐ s ∂(R : Measure S), (π₀ s : Measure (M × M)) = (π₁ s : Measure (M × M)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instFinite : IsFiniteMeasure lambda := hlaw.label_law ▸ inferInstance
  let _instSigma : ∀ j, SigmaFinite (κ j) := hκ
  dsimp only
  intro S instS instM instO instH R π₀ π₁ hπ₀ hπ₁ hopt₀ hopt₁ hwitness
  apply ae_original_optimal_plans_eq_of_original_seed_probe_ae_eq_of_face
    hF hcomplete hu ha hinj hlaw horder hκ hface (R : Measure S)
    (fun s ↦ (π₀ s : Measure (M × M))) (fun s ↦ (π₁ s : Measure (M × M))) hopt₀ hopt₁
  intro j i
  obtain ⟨Pn, Q, ψ, hinner, houter, hsource₀, hsource₁, hgap⟩ := hwitness j
  let g := physicalSceneOriginalSeedSeparatingProbe (P := P) j i
  let obs : S → ℝ := fun s ↦
    |(∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
        (lambda := lambda) j g e.1 e.2 ∂(π₀ s : Measure (M × M))) -
      ∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
        (lambda := lambda) j g e.1 e.2 ∂(π₁ s : Measure (M × M))|
  obtain ⟨_, _, _, hIntR, _, _, hennI, hennO⟩ :=
    original_seed_probe_gap_expectation_limits_of_iterated_weak
      (P := P) (a := a) (κ := κ) (lambda := lambda)
      hF hcomplete hu ha hinj μ j g Pn Q R ψ hinner houter π₀ π₁ hπ₀ hπ₁ hsource₀ hsource₁
  have hzero : (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S)) = 0 :=
    ennreal_iterated_readout_eq_zero_of_curry_tendsto_zero
      (fun ℓ n ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Pn ℓ n : Measure S))
      (fun ℓ ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Q ℓ : Measure S))
      (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S)) ψ hennI hennO (hgap g)
  have hmeas : AEMeasurable (fun s ↦ ENNReal.ofReal (obs s)) (R : Measure S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hIntR.aestronglyMeasurable.aemeasurable
  have hzAE := (lintegral_eq_zero_iff' hmeas).mp hzero
  filter_upwards [hzAE] with s hs
  have habs : obs s = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hs) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)


end OTSelector.Reconstruction
