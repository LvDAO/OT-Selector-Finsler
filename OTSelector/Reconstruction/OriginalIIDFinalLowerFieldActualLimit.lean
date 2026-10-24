import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetSameAtlas
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

/-- Any convergent subsequence of the genuine original iid tilted mean lies
above the SAME original atlas pressure integral. All matching candidates and
profiles use a further subsequence of those same physical samples. -/
theorem original_actual_iid_signed_mean_limit_ge_same_atlas_of_focal_reverse
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
    {δseq lossseq : ℕ → ℝ≥0∞}
    (D : ∀ d, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r (δseq d) (lossseq d))
    (hloss : Tendsto lossseq atTop (𝓝 0)) (hGood : ∀ᵐ z ∂μ.map a, Good z)
    (g : M × M →ᵇ ℝ) (t : ℝ) (initial : ℕ → ℕ) (hinitial : StrictMono initial) (L : ℝ)
    (hmean : Tendsto (fun n ↦ ∫ p, (physicalSceneCanonicalHaarScale (finrank ℝ E-1) (initial n))^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
      ∂originalIIDOptimalMeanPlan μ ν (fun x y ↦
        (physicalSceneCanonicalHaarScale (finrank ℝ E-1) (initial n))^2 *
          ((F.lengthEDist x y).toReal-u y+u x)+t*g (x,y)) 1 (initial n+1)) atTop (𝓝 L)) :
    (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t z ∂μ.map a) ≤ L := by
  classical
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : BorelSpace (ℚ → M) := inferInstance
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  obtain ⟨Cenergy,hCenergy,_hwhole,henergy⟩ := exists_original_iid_physical_energy_of_same_face
    hF hcomplete hdim hu ha hinj horder hA hB hAB hμ hν hμreg hreg hface
  let budget := ENNReal.ofReal (Cenergy+2 * |t| * ‖g‖)
  let cost := fun n x y ↦ (physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
    ((F.lengthEDist x y).toReal-u y+u x)+t*g (x,y)
  have hcost (n) : Measurable (Function.uncurry (cost n)) :=
    ((F.measurable_distance_slack hu).const_mul _).add (g.continuous.measurable.const_mul t)
  have hphysical : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) 1 ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget :=
    Eventually.of_forall (fun n ↦ henergy g t n)
  have hreverse0 := hreverse.mono (fun z hz ↦ hz (0 : M × M →ᵇ ℝ))
  obtain ⟨_,_,_,hglobal⟩ := exists_original_same_atlas_global_pressure_budget_of_focal_reverse
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hAB hμ hν hreg hμreg
    hface hgap hdist hdim hsep hlaw γ hγ hb hreverse0
  have hp := (hglobal g t).1
  let C := fun d ↦ (D d).haar.continuous.coefficient
  let j := fun d i ↦ (C d i).seedIndex
  let q := fun d i ↦ finrank ℝ (P (j d i)).seed.covector.ker
  let V := fun d i ↦ Fin (q d i) → ℝ
  let X := fun d i ↦ V d i × ℝ
  let Macro := fun d i ↦ OriginalIIDMaskedMacroCarrier (0 : X d i)
  let K := fun d i ↦ physicalSceneOriginalMacroLabel (P := P) (a := a) (j d i) '' (C d i).roots
  let hK : ∀ d i, IsCompact (K d i) := by
    intro d i
    have hlabel : ContinuousOn (physicalSceneOriginalMacroLabel (P := P) (a := a) (j d i)) (C d i).roots := by
      apply (Module.finBasis ℝ (P (j d i)).seed.covector.ker).equivFunL.continuous.comp_continuousOn
      have hc := ((D d).haar.intensity i).continuous_label
      rwa [(D d).haar.intensity_roots i] at hc
    exact (C d i).roots_compact.image_of_continuousOn hlabel
  let scale := fun d i ↦ physicalSceneCanonicalHaarScale (q d i)
  let coord := fun d i n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) (j d i) (scale d i n)
  let H := fun d i ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) (j d i)
  let hH : ∀ d i, MeasurableSet (H d i) := fun d i ↦ measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj (j d i)
  let ref := fun d i (c : V d i) ↦ a ((P (j d i)).seed.curve
    ((Module.finBasis ℝ (P (j d i)).seed.covector.ker).equivFunL.symm c) 0)
  let root := fun d i ↦ physicalSceneOriginalMacroRootValue (P := P) (a := a) (j d i)
  let J := (d : ℕ) × Fin (D d).haar.continuous.count
  obtain ⟨extraction,hextraction,Qflat,hweakFullFlat,hrootFlat,inputFlat,hinput,hprofileFlat⟩ :=
    exists_original_actual_core_matching_laws_along_subsequence_of_energy
      (hcore := hpopulation) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
      (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
      (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
      (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
      (J := J) (fun k ↦ D k.1) (fun k ↦ k.2)
      cost hcost (fun _ ↦ 1) budget ENNReal.ofReal_ne_top hphysical initial hinitial (by omega : 2 ≤ finrank ℝ E)
  let m := initial ∘ extraction
  have hm : StrictMono m := hinitial.comp hextraction
  let Q := fun d (i : Fin (D d).haar.continuous.count) ↦ Qflat (⟨d,i⟩ : J)
  let input := fun d (i : Fin (D d).haar.continuous.count) c ↦ inputFlat (⟨d,i⟩ : J) c
  let Λ := fun d i ↦ originalIIDWholeCoreSceneKernel (K d i) (hK d i).measurableSet (Q d i)
  have hroot (d) (i) (frame) := hrootFlat (⟨d,i⟩ : J) frame
  have href (d) (i) {c : V d i} (hc : c ∈ K d i) : root d i c = ref d i c := by
    obtain ⟨z,hz,rfl⟩ := hc
    rw [show root d i (physicalSceneOriginalMacroLabel (P := P) (a := a) (j d i) z) = z from
      physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj (j d i) ((C d i).roots_subset_piece hz)]
    symm
    change a ((P (j d i)).seed.curve
      ((Module.finBasis ℝ (P (j d i)).seed.covector.ker).equivFunL.symm
        ((Module.finBasis ℝ (P (j d i)).seed.covector.ker).equivFunL
          (populationSeedRootLabelValue (P (j d i)).seed a z))) 0) = z
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ((D d).haar.intensity i).root_identity z (((D d).haar.intensity_roots i).symm ▸ hz)
  have hprofile (d) (i) : ∀ᵐ c ∂(volume : Measure (V d i)).restrict (K d i),
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) (j d i) (ref d i c))
        (condDistrib u a μ (root d i c)) (condDistrib u a ν (root d i c)) (input d i c) (Λ d i c) := by
    have hh : ∀ᵐ c ∂(volume : Measure (V d i)).restrict (K d i),
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ (μ.map a) (j d i) (ref d i c))
          (condDistrib u a μ (ref d i c)) (condDistrib u a ν (ref d i c)) (input d i c) (Λ d i c) := by
      convert hprofileFlat (⟨d,i⟩ : J) using 1 <;>
        simp only [K,Λ,physicalSceneOriginalMacroLabel,Set.image_image] <;> rfl
    filter_upwards [hh,ae_restrict_mem (hK d i).measurableSet] with c hc hmem
    simpa only [href d i hmem] using hc
  have hweak (d) (i) (frame) : Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : X d i) μ ν
      (by simpa only [Fintype.card_fin] using original_seed_transverse_finrank_pos (P (j d i)).seed (by omega : 2 ≤ finrank ℝ E))
      (cost (m n)) (hcost (m n)) 1 (m n) (H d i) (hH d i)
      (fun x ↦ coord d i (m n) x-scale d i (m n) • originalMacroFrameCenter (q d i) frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj (j d i) (scale d i (m n))).sub
        measurable_const) u hu.continuous.measurable) atTop
      (𝓝 ((Q d i frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : X d i)).measurable.aemeasurable)) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (hweakFullFlat (⟨d,i⟩ : J) frame) (continuous_originalIIDMaskedMacroPlanProjection (0 : X d i))
    convert hw using 1
    simp only [coord,scale,physicalSceneOriginalSeedScaledPosition,
      physicalSceneOriginalSeedBasisPosition,originalIIDMaskedMacroPlanLaw,smul_sub]
    rfl
  let θcoord := fun d i (c : V d i) ↦
    (originalSeedCoordinateHaarFactor (P (j d i)).seed (κ (j d i)) : ℝ) *
      (populationSeedPieceHaarDensity P a κ (μ.map a) (j d i)
        ((Module.finBasis ℝ (P (j d i)).seed.covector.ker).equivFunL.symm c)).toReal
  let θ := fun d i ↦ (K d i).indicator (θcoord d i)
  let hθ : ∀ d i, Measurable (θ d i) := fun d i ↦
    (measurable_originalIIDCoordinateIntensity hF hcomplete hu ha hinj hκ (j d i)).indicator (hK d i).measurableSet
  let Ξ := fun d i ↦ originalIIDUnitColoredSceneKernel (q d i) (θ d i) (hθ d i) (Λ d i)
  let Amatrix := fun d i ↦ physicalSceneOriginalMacroCoefficient (P := P) (a := a) (j d i)
  let probe := fun d i ↦ originalIIDMacroPhysicalProbe (P := P) (j d i) g
  let value := fun d i ↦ originalIIDCandidateNormalizedValue (q d i) (θ d i) (Ξ d i) (Amatrix d i) (probe d i) t
  let label := fun d i ↦ physicalSceneOriginalMacroLabel (P := P) (a := a) (j d i)
  have hlabels (d) := (D d).haar.originalIID_actual_candidate_label_readout
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood (by omega : 2 ≤ finrank ℝ E) g t cost hcost (fun _ ↦ 1) budget
    ENNReal.ofReal_ne_top hphysical m hm.tendsto_atTop (Q d) (hroot d) (input d) (hprofile d) (hweak d)
  have hcompare (d) (i) : ∀ᵐ z ∂(μ.map a).restrict (C d i).roots,
      originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t z ≤ value d i (label d i z) := by
    have hcurve := (D d).haar.original_inverse_ae_of_ae_recovery hF hcomplete hu ha hinj horder hb
      hμreg hreg hμinv hνinv rfl hbalance.symm i
    filter_upwards [(hlabels d).2 i |>.2.2.2,hcurve,ae_restrict_of_ae hsep,ae_restrict_of_ae hreverse,
      ae_restrict_mem (C d i).roots_compact.measurableSet] with z hz hc hs hr hmem
    obtain ⟨M,_,hvalue⟩ := hz
    have hpop : z ∈ (D d).haar.continuous.population.roots :=
      (D d).haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,hmem⟩
    obtain ⟨data⟩ := ((D d).haar.continuous.population.good z hpop).2 (j d i) ((C d i).roots_subset_piece hmem) |>.1
    have htheta : θcoord d i (label d i z) = originalSeedCoordinateIntensity P a κ (μ.map a) (j d i) z := by
      dsimp only [θcoord,label,originalSeedCoordinateIntensity,populationAtlasTheta]
      congr 3
      exact (Module.finBasis ℝ (P (j d i)).seed.covector.ker).equivFunL.symm_apply_apply _
    have hbound := original_signed_pressure_le_normalized_iid_macro_candidate_of_focal_reverse
      hF hcomplete hu ha hinj (j d i) ((C d i).roots_subset_piece hmem) data hs g hc.1 hc.2
      (hr g (j d i) ((C d i).roots_subset_piece hmem) data) M t
    change value d i (label d i z) = θcoord d i (label d i z)^(-2/(q d i : ℝ))*
      M.value (t*θcoord d i (label d i z)^(2/(q d i : ℝ))) at hvalue
    have hvalue' : value d i (label d i z) = θcoord d i (label d i z)^(-2/(q d i : ℝ))*
        M.value (t*originalSeedCoordinateIntensity P a κ (μ.map a) (j d i) z^(2/(q d i : ℝ))) := by
      simpa only [htheta] using hvalue
    exact hbound.trans_eq hvalue'.symm
  have hfinite (d) : (∑ i, ∫ z in (C d i).roots,
      originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t z ∂μ.map a) ≤
      (∑ i, ∫ p, physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j d i) g t p-|t| * ‖g‖
        ∂(((volume : Measure (V d i)).restrict (K d i)) ⊗ₘ originalIIDRawPairPalmKernel (Λ d i))) := by
    apply Finset.sum_le_sum
    intro i _
    rw [← (hlabels d).2 i |>.2.2.1]
    exact integral_mono_ae hp.integrableOn ((hlabels d).2 i |>.2.1) (hcompare d i)
  have hphysicalLimit := hmean.comp hextraction.tendsto_atTop
  have hraw := originalIID_actual_root_refinement_signed_tilt_lower
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist (fun d ↦ (D d).haar) hloss hGood (by omega : 2 ≤ finrank ℝ E) g t
    cost hcost (fun _ ↦ 1) budget ENNReal.ofReal_ne_top hphysical m hm.tendsto_atTop
    Q hroot input hprofile hweak L hphysicalLimit
  have hcoreLimit := tendsto_original_haar_core_signed_integrals hcomplete (fun d ↦ (D d).haar)
    hloss (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t) hp
  have hle (ε : ℝ) (hε : 0 < ε) :
      (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t z ∂μ.map a) ≤ L+ε := by
    apply le_of_tendsto hcoreLimit
    filter_upwards [hraw ε hε] with d hd
    exact (hfinite d).trans hd
  by_contra hnot
  have hpos : 0 < ((∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b g t z ∂μ.map a)-L)/2 := by
    linarith only [not_le.mp hnot]
  have hh := hle _ hpos
  linarith only [hh,hpos]

end OTSelector.Reconstruction
