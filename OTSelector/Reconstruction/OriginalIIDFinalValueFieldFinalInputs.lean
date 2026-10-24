import OTSelector.Reconstruction.OriginalIIDFinalLowerFieldProbability
import OTSelector.Reconstruction.FinslerGeneralSelectorAssemblyFinal
import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenLocal
import OTSelector.Reconstruction.OriginalIIDRefinedPressureReadout

/-! Actual final lower, upper and value fields on one unchanged original population atlas. -/
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

/-- All final fields use the SAME original atlas pressure. The whole original
optimal face produces the calibrated plan, original clock coupling, screened
cores, summable root losses, iid energy, global integrability and hprob internally.
Only pointwise original conditional focal reverse pressure remains to be supplied. -/
theorem exists_original_same_atlas_final_inputs_of_focal_reverse
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
    (hb : Measurable b)
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
    ∃ inputs : FinslerSelectorFinalInputs F μp νp hA hB hμ hν R X Y u,
      inputs.pressureLower = originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν ∧
      inputs.pressureUpper = originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν := by
  classical
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : StandardBorelSpace M := inferInstance
  let : Nonempty M := nonempty_of_isProbabilityMeasure μ
  let : BorelSpace (ℚ → M) := inferInstance
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro μp νp
  obtain ⟨π,hπ⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν (hA.union hB)
    (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
  have hcarried := ae_original_regular_sameLabel_forward_of_optimal_face hF hcomplete hu ha hface hπ
  have hcal : ∀ᵐ p ∂π, u p.2-u p.1 = dist p.1 p.2 :=
    hcarried.mono fun p hp ↦ (horder p.1 hp.1 p.2 hp.2.1).mp ⟨hp.2.2.1,hp.2.2.2⟩
  have hπA : ∀ᵐ p ∂π, p.1 ∈ A := ae_of_ae_map measurable_fst.aemeasurable (hπ.1.1.symm ▸ hμ)
  have hπB : ∀ᵐ p ∂π, p.2 ∈ B := ae_of_ae_map measurable_snd.aemeasurable (hπ.1.2.symm ▸ hν)
  have hclockgap : ∀ᵐ p ∂π, gap ≤ u p.2-u p.1 := by
    filter_upwards [hπA,hπB,hcal] with p h₀ h₁ hc
    rw [hc]
    exact hdist p.1 h₀ p.2 h₁
  let I := (u '' A) ∪ (u '' B)
  have hI : IsCompact I := (hA.image hu.continuous).union (hB.image hu.continuous)
  have hμI : ∀ᵐ x ∂μ, u x ∈ I := hμ.mono fun x hx ↦ Or.inl (mem_image_of_mem u hx)
  have hνI : ∀ᵐ y ∂ν, u y ∈ I := hν.mono fun y hy ↦ Or.inr (mem_image_of_mem u hy)
  obtain ⟨γ,hγ,hGood⟩ := exists_original_clockPair_kernel_with_range μ ν π hπ.1 a u ha hu.continuous.measurable
    (hcarried.mono fun _ h ↦ h.2.2.1) gap hclockgap I hI.measurableSet hμI hνI
  let : IsMarkovKernel γ := hγ
  have hγforward : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
      ∀ᵐ p ∂γ z, p.1 ≤ p.2 := by
    filter_upwards [hGood] with z hz
    exact ⟨hz.1,hz.2.1.mono (fun p hp ↦ by linarith only [hp,hgap])⟩
  let accuracy := fun n ↦ originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)
  have haccuracy (n) : 0 < accuracy n ∧ accuracy n < 1 := originalUpperRefinementAccuracy_pos_lt_one _
  have haccLim : Tendsto accuracy atTop (𝓝 0) := tendsto_originalUpperReadoutAccuracy
  let δn := fun n ↦ ENNReal.ofReal (accuracy n)
  have hstep (n : ℕ) := hpopulation.exists_local_core_small_clock_screen
    (Good := originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I)
    (δ := δn n) (loss := δn n) hrecovery hF hcomplete hu ha hinj hκ hGood (half_pos hgap)
    (ENNReal.ofReal_pos.mpr (haccuracy n).1).ne' (ENNReal.ofReal_pos.mpr (haccuracy n).1).ne'
  choose D hscreen using hstep
  have hδ1 (n) : (δn n).toReal < 1 := by
    simpa only [δn,ENNReal.toReal_ofReal (haccuracy n).1.le] using (haccuracy n).2
  have hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0) := by
    simpa only [δn,ENNReal.toReal_ofReal (le_of_lt (haccuracy _).1)] using haccLim
  have hloss : (∑' n, δn n) ≠ ⊤ := tsum_originalUpperReadoutLoss_ne_top
  have hreverse0 := hreverse.mono (fun z hz ↦ hz (0 : M × M →ᵇ ℝ))
  obtain ⟨_,_,_,hglobal⟩ := exists_original_same_atlas_global_pressure_budget_of_focal_reverse
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hAB hμ hν hreg hμreg
    hface hgap hdist hdim hsep hlaw γ hγforward hb hreverse0
  have hp0 (f : FinalProbeSpace A B) :=
    (hglobal (originalFinalProbeAmbient F μp νp hA hB hμ hν f) 0).1
  have hprob := original_same_atlas_final_hprob_of_focal_reverse
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hAB hμ hν hreg hμreg
    hface hgap hdist hdim hsep hlaw γ hγforward hb hreverse hμinv hνinv
    R X Y hX hY hXi hYi hXlaw hYlaw hXY
  have hupper := original_same_atlas_final_hupper (μ := μp) (ν := νp) hI γ hlaw hF hcomplete hu ha hinj horder hb
    hμreg hreg hμinv hνinv hbalance.symm hdim hgap hsep hγforward δn δn D
    (fun _ ↦ ENNReal.ofReal_ne_top) hδ1 hδlim hloss accuracy haccLim haccuracy hscreen
    hA hB hAB hμ hν hp0 hdist π hπ.1 hcal R X Y hX hY hXi hYi hXlaw hYlaw hXY
    (fun _ ↦ 1)
  refine ⟨{
    pressureLower := originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν
    pressureUpper := originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν
    radius := fun _ ↦ 1
    hradius := fun _ ↦ by norm_num
    hvalue := fun _ _ ↦ rfl
    hprob := ?_
    hupper := hupper },rfl,rfl⟩
  intro f t ε _ht hε
  exact hprob f t ε hε

end OTSelector.Reconstruction
