import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldActualLimit
import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldMeanBounds
import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldSubsequence
import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldSignedRoot
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetHaarCore
import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.OriginalIIDActualTiltRootRefinement
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetCommonFrames
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetNormalizedRoot

/-! A genuine original iid energy budget pays the actual zero-pressure field on every finite core. -/
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

/-- The SAME original atlas pressure is the eventual lower bound of the true
particle-indexed iid optimizer mean. Its own whole-face energy and actual
core refinements supply compactness; no hmean-lower, hp0 or hprob is supplied. -/
theorem eventually_original_actual_iid_signed_mean_ge_same_atlas_of_focal_reverse
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
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
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
    {diameter : ℝ} (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ]
    (hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
      ∀ᵐ p ∂γ z, p.1 ≤ p.2) (hb : Measurable b)
    (hreverse : ∀ᵐ z ∂μ.map a, ∀ f : M × M →ᵇ ℝ, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ (μ.map a) j,
      ∀ data : OriginalSeedConditionalMoments (P j).seed
        (populationSeedPieceLabel P a κ (μ.map a) j ⟨z,hz⟩)
        (condDistrib u a μ z) (condDistrib u a ν z),
      ∀ Qf : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
        (condDistrib u a μ z) (condDistrib u a ν z) (data.originalFocalKinetic gap)
        (originalPhysicalRootProbe b f z),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ (P j).seed.covector.ker)
        id id (condDistrib u a μ z) (condDistrib u a ν z) (data.originalFocalKinetic gap)
        (originalPhysicalRootProbe b f z) R t) ≤ Qf.value t) 
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (g : M × M →ᵇ ℝ) (t ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t z ∂μ.map a)-ε ≤
      ∫ p, (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
        ∂originalIIDOptimalMeanPlan μ ν (fun x y ↦
          (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
            ((F.lengthEDist x y).toReal-u y+u x)+t*g (x,y)) 1 (n+1) := by
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
  obtain ⟨Cenergy,_hCenergy,_hwhole,henergy⟩ := exists_original_iid_physical_energy_of_same_face
    hF hcomplete hdim hu ha hinj horder hA hB hAB hμ hν hμreg hreg hface
  let budget := ENNReal.ofReal (Cenergy+2 * |t| * ‖g‖)
  let cost := fun n x y ↦ (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
    ((F.lengthEDist x y).toReal-u y+u x)+t*g (x,y)
  have hcost (n) : Measurable (Function.uncurry (cost n)) :=
    ((F.measurable_distance_slack hu).const_mul _).add (g.continuous.measurable.const_mul t)
  let mean := fun n ↦ ∫ p, (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
    ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
      ∂originalIIDOptimalMeanPlan μ ν (cost n) 1 (n+1)
  have hbounded (n) : mean n ∈ Icc (- (|t| * ‖g‖)) (budget.toReal+|t| * ‖g‖) :=
    original_actual_iid_signed_mean_bounds_of_energy hcomplete hu hA hB hμ hν n
      (cost n) (hcost n) 1 ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2)
      (sq_nonneg _) g t budget ENNReal.ofReal_ne_top (henergy g t n)
  have hlimits (initial : ℕ → ℕ) (hinitial : StrictMono initial) (L : ℝ)
      (hlimit : Tendsto (mean ∘ initial) atTop (𝓝 L)) :
      (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t z ∂μ.map a) ≤ L :=
    original_actual_iid_signed_mean_limit_ge_same_atlas_of_focal_reverse
      hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hAB hμ hν hreg hμreg
      hface hgap hdist hdim hsep hlaw γ hγ hb hreverse hμinv hνinv D hseqLim
      (Eventually.of_forall fun _ ↦ trivial) g t initial hinitial L hlimit
  exact eventually_mean_lower_of_all_convergent_subsequences mean _ _ _ hbounded hlimits ε hε

end OTSelector.Reconstruction
