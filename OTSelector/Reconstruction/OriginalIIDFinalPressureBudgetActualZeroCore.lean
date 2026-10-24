import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetCandidate
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

/-- The only remaining comparison is the explicitly named local focal
reverse-pressure theorem. Weak laws, full matching profiles and the finite sum
candidate budget are all produced from the actual original iid optimizer. -/
theorem PopulationLocalPressureCore.original_actual_zero_pressure_core_budget_of_focal_reverse
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



    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hGood : ∀ᵐ z ∂μ.map a, Good z) (hdim : 2 ≤ finrank ℝ E)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    {diameter : ℝ} (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
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
    ∃ candidate : Fin D.haar.continuous.count → (ℚ → M) → ℝ,
      (∀ i, Measurable (candidate i) ∧ Integrable (candidate i)
        ((μ.map a).restrict (D.haar.continuous.coefficient i).roots) ∧
        ∀ᵐ z ∂(μ.map a).restrict (D.haar.continuous.coefficient i).roots,
          originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b (0 : M × M →ᵇ ℝ) 0 z ≤ candidate i z) ∧
      (∑ i, ∫ z in (D.haar.continuous.coefficient i).roots, candidate i z ∂μ.map a) ≤ budget.toReal := by
  classical
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : BorelSpace (ℚ → M) := inferInstance
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  let C := D.haar.continuous.coefficient
  let j := fun i ↦ (C i).seedIndex
  let q := fun i ↦ finrank ℝ (P (j i)).seed.covector.ker
  let V := fun i ↦ Fin (q i) → ℝ
  let X := fun i ↦ V i × ℝ
  let Macro := fun i ↦ OriginalIIDMaskedMacroCarrier (0 : X i)
  let K := fun i ↦ physicalSceneOriginalMacroLabel (P := P) (a := a) (j i) '' (C i).roots
  let hK : ∀ i, IsCompact (K i) := by
    intro i
    have hlabel : ContinuousOn (physicalSceneOriginalMacroLabel (P := P) (a := a) (j i)) (C i).roots := by
      apply (Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.continuous.comp_continuousOn
      have hc := (D.haar.intensity i).continuous_label
      rwa [D.haar.intensity_roots i] at hc
    exact (C i).roots_compact.image_of_continuousOn hlabel
  let scale := fun i ↦ physicalSceneCanonicalHaarScale (q i)
  let coord := fun i n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) (j i) (scale i n)
  let H := fun i ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) (j i)
  let hH : ∀ i, MeasurableSet (H i) := fun i ↦ measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj (j i)
  let ref := fun i (c : V i) ↦ a ((P (j i)).seed.curve
    ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm c) 0)
  let root := fun i ↦ physicalSceneOriginalMacroRootValue (P := P) (a := a) (j i)
  obtain ⟨m,hm,Q,hweakFull,hroot,input,hinput,hprofile0⟩ :=
    exists_original_actual_common_core_matching_laws_of_energy
      (hcore := hpopulation) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
      (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
      (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
      (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
      (J := Fin D.haar.continuous.count) (fun _ ↦ D) (fun i ↦ i)
      cost hcost k budget hbudget henergy hdim
  let Λ := fun i ↦ originalIIDWholeCoreSceneKernel (K i) (hK i).measurableSet (Q i)
  have href (i) {c : V i} (hc : c ∈ K i) : root i c = ref i c := by
    obtain ⟨z,hz,rfl⟩ := hc
    rw [show root i (physicalSceneOriginalMacroLabel (P := P) (a := a) (j i) z) = z from
      physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj (j i) ((C i).roots_subset_piece hz)]
    symm
    change a ((P (j i)).seed.curve
      ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm
        ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL
          (populationSeedRootLabelValue (P (j i)).seed a z))) 0) = z
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (D.haar.intensity i).root_identity z ((D.haar.intensity_roots i).symm ▸ hz)
  have hprofile (i) : ∀ᵐ c ∂(volume : Measure (V i)).restrict (K i),
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) (j i) (ref i c))
        (condDistrib u a μ (root i c)) (condDistrib u a ν (root i c)) (input i c) (Λ i c) := by
    have hp : ∀ᵐ c ∂(volume : Measure (V i)).restrict (K i),
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ (μ.map a) (j i) (ref i c))
          (condDistrib u a μ (ref i c)) (condDistrib u a ν (ref i c)) (input i c) (Λ i c) := by
      convert hprofile0 i using 1 <;>
        simp only [K,Λ,physicalSceneOriginalMacroLabel,Set.image_image] <;> rfl
    filter_upwards [hp,ae_restrict_mem (hK i).measurableSet] with c hc hmem
    simpa only [href i hmem] using hc
  have hweak (i) (frame) : Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : X i) μ ν
      (by simpa only [Fintype.card_fin] using original_seed_transverse_finrank_pos (P (j i)).seed hdim)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) (H i) (hH i)
      (fun x ↦ coord i (m n) x-scale i (m n) • originalMacroFrameCenter (q i) frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj (j i) (scale i (m n))).sub
        measurable_const) u hu.continuous.measurable) atTop
      (𝓝 ((Q i frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : X i)).measurable.aemeasurable)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ (hweakFull i frame)
      (continuous_originalIIDMaskedMacroPlanProjection (0 : X i))
    convert hw using 1
    simp only [coord,scale,physicalSceneOriginalSeedScaledPosition,
      physicalSceneOriginalSeedBasisPosition,originalIIDMaskedMacroPlanLaw,smul_sub]
    rfl
  let θcoord := fun i (c : V i) ↦
    (originalSeedCoordinateHaarFactor (P (j i)).seed (κ (j i)) : ℝ) *
      (populationSeedPieceHaarDensity P a κ (μ.map a) (j i)
        ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm c)).toReal
  let θ := fun i ↦ (K i).indicator (θcoord i)
  let hθ : ∀ i, Measurable (θ i) := fun i ↦
    (measurable_originalIIDCoordinateIntensity hF hcomplete hu ha hinj hκ (j i)).indicator (hK i).measurableSet
  let Ξ := fun i ↦ originalIIDUnitColoredSceneKernel (q i) (θ i) (hθ i) (Λ i)
  let Amatrix := fun i ↦ physicalSceneOriginalMacroCoefficient (P := P) (a := a) (j i)
  let probe := fun i ↦ originalIIDMacroPhysicalProbe (P := P) (j i) (0 : M × M →ᵇ ℝ)
  let value := fun i ↦ originalIIDCandidateNormalizedValue (q i) (θ i) (Ξ i) (Amatrix i) (probe i) 0
  let label := fun i ↦ physicalSceneOriginalMacroLabel (P := P) (a := a) (j i)
  have hlabels := D.haar.originalIID_actual_candidate_label_readout
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim (0 : M × M →ᵇ ℝ) 0 cost hcost k budget hbudget henergy
    m hm.tendsto_atTop Q hroot (fun i c ↦ input i c) hprofile hweak
  have hcost := D.haar.originalIID_actual_candidate_zero_label_budget
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim (0 : M × M →ᵇ ℝ) cost hcost k budget hbudget henergy
    m hm.tendsto_atTop Q hroot (fun i c ↦ input i c) hprofile hweak
  refine ⟨fun i z ↦ value i (label i z),?_,hcost.2⟩
  intro i
  refine ⟨(hlabels.2 i).1,(hlabels.2 i).2.1,?_⟩
  filter_upwards [(hlabels.2 i).2.2.2,ae_restrict_of_ae hsep,ae_restrict_of_ae hreverse,
    ae_restrict_mem (C i).roots_compact.measurableSet] with z hz hs hr hmem
  obtain ⟨M,_,hvalue⟩ := hz
  have hpop : z ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,hmem⟩
  obtain ⟨data⟩ := (D.haar.continuous.population.good z hpop).2 (j i) ((C i).roots_subset_piece hmem) |>.1
  have hp := original_zero_pressure_le_normalized_iid_macro_candidate_of_focal_reverse
    hF hcomplete hu ha hinj (j i) ((C i).roots_subset_piece hmem) data hs
    (hr (j i) ((C i).roots_subset_piece hmem) data) M
  have hvalue0 : value i (label i z) = θcoord i (label i z)^(-2/(q i : ℝ))*M.value 0 := by
    simpa only [zero_mul] using hvalue
  exact hp.trans_eq hvalue0.symm

end OTSelector.Reconstruction
