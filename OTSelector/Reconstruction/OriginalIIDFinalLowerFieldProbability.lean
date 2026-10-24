import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldActualMean
import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldMeanReadout
import OTSelector.Reconstruction.OriginalIIDSameAtlasProbabilityUpper
import OTSelector.Limit.FinslerProbabilityLowerBound
import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldMeanBounds
import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldSubsequence
import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldSignedRoot
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetHaarCore
import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.OriginalIIDActualTiltRootRefinement
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetCommonFrames
import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetNormalizedRoot

/-! The same original atlas supplies the actual independent-iid probability lower field. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
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

/-- The genuine actual iid mean lower and physical centered concentration
produce the final SAME-atlas probability lower field on arbitrary independent
iid sample spaces. No hprob, hp0, hvalue or finished mean lower is supplied. -/
theorem original_same_atlas_final_hprob_of_focal_reverse
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
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (R : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (R n)]
    (X Y : ∀ n, Fin (n+1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (R n)) (hYi : ∀ n, iIndepFun (Y n) (R n))
    (hXlaw : ∀ n i, (R n).map (X n i) = μ) (hYlaw : ∀ n i, (R n).map (Y n i) = ν)
    (hXY : ∀ n, IndepFun (fun ξ i ↦ X n i ξ) (fun ξ i ↦ Y n i ξ) (R n)) :
    let μp : ProbabilityMeasure M := ⟨μ,inferInstance⟩
    let νp : ProbabilityMeasure M := ⟨ν,inferInstance⟩
    ∀ (f : FinalProbeSpace A B) (t ε : ℝ), 0 < ε →
      Tendsto (fun n ↦ (R n).real {ξ | finslerSupportedPressure F μp νp (A ∪ B) (hA.union hB).measurableSet
        (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
        (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) u
        (((n+1 : ℕ) : ℝ)^(2/((finrank ℝ E : ℝ)-1))) f t <
        originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν f t-ε}) atTop (𝓝 0) := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : BorelSpace (ℚ → M) := inferInstance
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro μp νp f t ε hε
  let K := A ∪ B
  have hK : IsCompact K := hA.union hB
  have hμK : ∀ᵐ x ∂μ, x ∈ K := hμ.mono fun _ hx ↦ Or.inl hx
  have hνK : ∀ᵐ y ∂ν, y ∈ K := hν.mono fun _ hy ↦ Or.inr hy
  let g := originalFinalProbeAmbient F μp νp hA hB hμ hν f
  have hg := (originalFinalProbeAmbient_spec (F := F) μp νp hA hB hμ hν f).2
  have hmean := eventually_original_actual_iid_signed_mean_ge_same_atlas_of_focal_reverse
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hAB hμ hν hreg hμreg
    hface hgap hdist hdim hsep hlaw γ hγ hb hreverse hμinv hνinv g t (ε/2) (by linarith)
  refine finslerSupportedPressure_probability_lower_of_integral_lower hdim μp νp K hK hμK hνK
    R X Y hX hY hXi hYi hXlaw hYlaw hXY u hu.continuous f t
    (originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν f t) hε ?_
  have hscale (n : ℕ) : finslerMeanScale E n =
      (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 := by
    exact (original_scale_sq_eq_count_rpow (by omega : 0 < finrank ℝ E-1)
      (physicalSceneCanonicalHaarScale_pos _ n)
      (physicalSceneCanonicalHaarScale_pow _ (by omega : 0 < finrank ℝ E-1) n)).symm
  have hqdim : ((finrank ℝ E-1 : ℕ) : ℝ) = (finrank ℝ E : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ finrank ℝ E),Nat.cast_one]
  filter_upwards [hmean] with n hn
  have htransfer := integral_finslerSupportedPressure_eq_original_assignment hcomplete μp νp K hK
    hμK hνK (R n) (X n) (Y n) (hX n) (hY n) (hXi n) (hYi n) (hXlaw n) (hYlaw n) (hXY n)
    u hu f g hg t
  let cost := fun x y ↦ finslerMeanScale E n*((F.lengthEDist x y).toReal-u y+u x)+t*g (x,y)
  have hcost : Measurable (Function.uncurry cost) :=
    ((F.measurable_distance_slack hu).const_mul _).add (g.continuous.measurable.const_mul t)
  have hint := integrable_originalIIDOptimalMeanPlan_physical_tilt hcomplete hu hA hB hμ hν n
    cost hcost 1 (finslerMeanScale E n) g t
  have hread := integral_originalIIDOptimalMeanPlan_assignment_value μ ν cost hcost 1
    (by simpa only [one_mul] using hint)
  have heq : (∫ ξ, finslerSupportedPressure F μp νp K hK.measurableSet hμK hνK
      (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) u (finslerMeanScale E n) f t ∂R n) =
      ∫ p, (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
        ∂originalIIDOptimalMeanPlan μ ν (fun x y ↦
          (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
            ((F.lengthEDist x y).toReal-u y+u x)+t*g (x,y)) 1 (n+1) := by
    rw [htransfer]
    simp only [one_mul,integral_div] at hread
    simpa only [canonicalLaw,twoColourLaw,cost,hscale n,μp,νp,ProbabilityMeasure.coe_mk] using hread.symm
  have hcoeff : (((n+1 : ℕ) : ℝ)^(2/((finrank ℝ E : ℝ)-1))) = finslerMeanScale E n := by
    simp only [finslerMeanScale,hqdim]
  rw [hcoeff,heq]
  exact hn

end OTSelector.Reconstruction
