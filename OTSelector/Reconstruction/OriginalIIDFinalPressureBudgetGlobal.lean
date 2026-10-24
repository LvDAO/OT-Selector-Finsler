import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetActualZeroCore
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetHaarCore
import OTSelector.Reconstruction.OriginalIIDFinalValueFieldZeroTilt
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetCommonFrames
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetNormalizedRoot

/-! Global original pressure integrability from actual iid energy and the precise pending local reverse comparison. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish

/-- A single actual iid physical energy budget gives the genuine global
zero-pressure budget and all signed tilted pressures of the SAME original atlas.
The only mathematical frontier named here is pointwise focal reverse pressure;
no hp0, hprob, hvalue, candidate, weak law or global pressure budget is supplied. -/
theorem original_global_pressure_integrable_of_actual_iid_energy_and_focal_reverse
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
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
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
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



    (hdim : 6 ≤ finrank ℝ E)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    {diameter : ℝ} (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ]
    (hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
      ∀ᵐ p ∂γ z, p.1 ≤ p.2) (hb : Measurable b)
    (hreverse : ∀ᵐ z ∂μ.map a, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ (μ.map a) j,
      ∀ data : OriginalSeedConditionalMoments (P j).seed
        (populationSeedPieceLabel P a κ (μ.map a) j ⟨z,hz⟩)
        (condDistrib u a μ z) (condDistrib u a ν z),
      ∀ Qf : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
        (condDistrib u a μ z) (condDistrib u a ν z) (data.originalFocalKinetic gap)
        (originalPhysicalRootProbe b (0 : M × M →ᵇ ℝ) z),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ (P j).seed.covector.ker)
        id id (condDistrib u a μ z) (condDistrib u a ν z) (data.originalFocalKinetic gap)
        (originalPhysicalRootProbe b (0 : M × M →ᵇ ℝ) z) R t) ≤ Qf.value t) :
    (∫⁻ z, ENNReal.ofReal (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b
      (0 : M × M →ᵇ ℝ) 0 z) ∂μ.map a) ≤ budget ∧
    ∀ (g : M × M →ᵇ ℝ) (t : ℝ),
      Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t) (μ.map a) ∧
      |populationAtlasPressure P a κ (μ.map a)
        (fun j ↦ originalSeedHaarPressure (P j).seed a (κ j) μ ν b g)
        ((finrank ℝ E-1 : ℕ) : ℝ) t| ≤ budget.toReal+|t| * ‖g‖ := by
  classical
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : BorelSpace (ℚ → M) := inferInstance
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  let seq := fun n : ℕ ↦ (((n+1 : ℕ) : ℝ≥0∞))⁻¹
  have hseq (n) : seq n ≠ 0 := by simp only [seq,ne_eq,ENNReal.inv_eq_zero]; simp
  have hseqLim : Tendsto seq atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hlocal := hpopulation.local_core hrecovery hF hcomplete hu ha hinj hκ
  let D := fun n : ℕ ↦ Classical.choice
    (hlocal (fun _ ↦ True) (Eventually.of_forall fun _ ↦ trivial) (seq n) (hseq n) (seq n) (hseq n))
  have hvalues (n : ℕ) := (D n).original_actual_zero_pressure_core_budget_of_focal_reverse
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist (Eventually.of_forall fun _ ↦ trivial) (by omega : 2 ≤ finrank ℝ E)
    cost hcost k budget hbudget henergy hsep hreverse
  choose candidate hcandidate hsum using hvalues
  have hread := originalPhysicalFinslerRootPressure_measurable_nonneg (0 : M × M →ᵇ ℝ)
    hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb 0
  have hglobal := original_haar_core_pressure_budget_of_candidates hcomplete (fun n ↦ (D n).haar)
    hseqLim (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b (0 : M × M →ᵇ ℝ) 0)
    hread.1 hread.2 candidate (fun n i ↦ (hcandidate n i).2.1)
    (fun n i ↦ (hcandidate n i).2.2) budget hbudget hsum
  refine ⟨?_,?_⟩
  · rw [← ofReal_integral_eq_lintegral_ofReal hglobal.1 hread.2]
    exact (ENNReal.ofReal_le_ofReal hglobal.2).trans_eq (ENNReal.ofReal_toReal hbudget)
  · intro g t
    have hzero := originalPhysicalFinslerRootPressure_zero_probe_eq P a κ (μ.map a) μ ν b
      g (0 : M × M →ᵇ ℝ)
    have hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g 0) (μ.map a) := by
      rw [hzero]
      exact hglobal.1
    obtain ⟨hi,hbound⟩ := integrable_originalPhysicalFinslerRootPressure_of_zero g hlaw hF hcomplete
      hu ha hinj hdim hgap hsep γ hγ hb hp0 t
    refine ⟨hi,?_⟩
    rw [hzero] at hbound
    have hmass : (μ.map a).real univ = 1 := by
      simp only [Measure.real,Measure.map_apply_of_aemeasurable ha.aemeasurable MeasurableSet.univ,
        preimage_univ,measure_univ,ENNReal.toReal_one]
    simp only [hmass,mul_one] at hbound
    linarith only [hbound,hglobal.2]

end OTSelector.Reconstruction
