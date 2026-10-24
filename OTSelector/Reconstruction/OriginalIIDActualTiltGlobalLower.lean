import OTSelector.Reconstruction.OriginalIIDActualTiltLowerBound

/-! Finite original root cells share the actual physical shifted energy once.
Each cell uses the same original cost, optimizer and sample subsequence; no
physical/core mass difference is discarded when their shifts are recovered. -/
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
attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}



variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [∀ j, SigmaFinite (κ j)]

/-- Actual disjoint original root cells consume the unchanged iid physical
plan energy once, including before any integrand measurability is known. -/
theorem PopulationHaarPressureCore.sum_originalIID_root_cell_source_energy_le
    (D : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (n : ℕ)
    (cost : M → M → ℝ) (k : ℝ) (energy : M × M → ℝ≥0∞) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost k
    (∑ i : Fin D.continuous.count, ∫⁻ ξ, ∫⁻ p, energy p
      ∂(Γ ξ).restrict ((a ⁻¹' (D.continuous.coefficient i).roots) ×ˢ univ) ∂law) ≤
      ∫⁻ ξ, ∫⁻ p, energy p ∂Γ ξ ∂law := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  intro law Γ
  let cells := fun i : Fin D.continuous.count ↦ (a ⁻¹' (D.continuous.coefficient i).roots) ×ˢ (univ : Set M)
  have hmeas (i) : MeasurableSet (cells i) :=
    ((D.continuous.coefficient i).roots_compact.measurableSet.preimage ha).prod MeasurableSet.univ
  have hd : Pairwise (Disjoint on cells) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact Set.disjoint_left.mp (D.continuous.disjoint hij) hpi.1 hpj.1
  apply (fixedCandidate_sum_lintegral_le law (fun i ξ ↦ ∫⁻ p, energy p ∂(Γ ξ).restrict (cells i))).trans
  apply lintegral_mono
  intro ξ
  calc
    _ = ∫⁻ p in ⋃ i, cells i, energy p ∂Γ ξ := by
      simpa only [tsum_fintype] using (lintegral_iUnion hmeas hd energy).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- Every actual seed has the same canonical transverse scale, since the
stored original normalization identifies codimension one exactly. -/
theorem originalIID_seed_transverse_finrank_eq (S : F.CalibratedLevelSeedPatch u) :
    finrank ℝ S.covector.ker = finrank ℝ E-1 := by
  have h : finrank ℝ S.covector.ker+1 = finrank ℝ E := by
    simpa only [Module.finrank_prod,Module.finrank_self,add_comm] using S.normalization.toLinearEquiv.finrank_eq
  omega

theorem PopulationHaarPressureCore.originalIID_finite_core_shifted_tilt_le_global_liminf
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



    (D : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hGood : ∀ᵐ z ∂μ.map a, Good z) (hdim : 2 ≤ finrank ℝ E)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    let C := D.continuous.coefficient
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
        have hc := (D.intensity i).continuous_label
        rwa [D.intensity_roots i] at hc
      exact (C i).roots_compact.image_of_continuousOn hlabel
    let scale := fun i ↦ physicalSceneCanonicalHaarScale (q i)
    let coord := fun i n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) (j i) (scale i n)
    let H := fun i ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) (j i)
    let hH := fun i ↦ measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj (j i)
    let ref := fun i (c : V i) ↦ a ((P (j i)).seed.curve
      ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm c) 0)
    let root := fun i ↦ physicalSceneOriginalMacroRootValue (P := P) (a := a) (j i)
    ∀ Q : (i : Fin D.continuous.count) → ℕ → ProbabilityMeasure (Macro i × Macro i),
    (∀ i frame, (originalIIDFixedCandidateFullSceneJoint (Q i frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier (q i))
        (physicalScene_centered_unitCube_mass (Fin (q i))) : Measure (V i))) →
    let Λ := fun i ↦ originalIIDWholeCoreSceneKernel (K i) (hK i).measurableSet (Q i)
    ∀ input : (i : Fin D.continuous.count) → V i →
      Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint (q i)) × LocalFiniteMeasure (LegalMarkedPhysicalPoint (q i))),
    (∀ i, ∀ᵐ c ∂(volume : Measure (V i)).restrict (K i),
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) (j i) (ref i c))
        (condDistrib u a μ (root i c)) (condDistrib u a ν (root i c)) (input i c) (Λ i c)) →
    (∀ i frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : X i) μ ν
      (by simpa only [Fintype.card_fin] using original_seed_transverse_finrank_pos (P (j i)).seed hdim)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) (H i) (hH i)
      (fun x ↦ coord i (m n) x-scale i (m n) • originalMacroFrameCenter (q i) frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj (j i) (scale i (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q i frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : X i)).measurable.aemeasurable))) →
    (∑ i, ∫⁻ c in K i, ∫⁻ mark,
      ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j i) g t (c,mark))
        ∂originalIIDRawPairPalmKernel (Λ i) c ∂volume) ≤
      liminf (fun r ↦ ∫⁻ ξ, ∫⁻ p,
        ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) (m r))^2*
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
        ∂originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ
        ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  intro C j q V X Macro K hK scale coord H hH ref root Q hroot Λ input hprofile hweak
  let physicalEnergy := fun n (p : M × M) ↦ ENNReal.ofReal
    ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2*
      ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
  let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n+1) ↦ ν))
  let masked := fun i n ↦ ∫⁻ ξ, ∫⁻ p, physicalEnergy n p
    ∂(originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict ((a ⁻¹' (C i).roots) ×ˢ univ) ∂law n
  have hqeq (i) : finrank ℝ (P (j i)).seed.covector.ker = finrank ℝ E-1 := originalIID_seed_transverse_finrank_eq (P (j i)).seed
  have hcell (i : Fin D.continuous.count) :=
    originalIID_fixed_candidate_shifted_tilt_le_masked_liminf (j := j i)
      hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
      hA hB hμ hν hreg hμreg hface hgap hdist D i rfl g t cost hcost k
      (original_seed_transverse_finrank_pos (P (j i)).seed hdim) budget hbudget
      (by simpa only [hqeq i] using henergy) hGood (K i) (hK i)
      (by simp only [originalIIDSeedCoordinateCast_rfl,image_id']; rfl)
      (Q i) (hroot i) m hm (input i) (hprofile i) (hweak i)
  have hlocal (i) : (∫⁻ c in K i, ∫⁻ mark,
      ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j i) g t (c,mark))
        ∂originalIIDRawPairPalmKernel (Λ i) c ∂volume) ≤ liminf (fun r ↦ masked i (m r)) atTop := by
    simpa only [physicalEnergy,masked,law,hqeq i] using hcell i
  exact (Finset.sum_le_sum (fun i _ ↦ hlocal i)).trans
    ((fixedCandidate_sum_liminf_le_liminf_sum (fun i r ↦ masked i (m r))).trans
      (liminf_le_liminf (Eventually.of_forall (fun r ↦
        D.sum_originalIID_root_cell_source_energy_le hcomplete ha (m r) (cost (m r)) (k (m r)) (physicalEnergy (m r))))))

end OTSelector.Reconstruction
