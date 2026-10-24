import OTSelector.Reconstruction.OriginalIIDActualTiltSignedLower

/-! Actual stored-loss root refinements remove the physical/root shift deficit.
All actual weak laws use the same original optimizer, cost and subsequence. -/
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

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  [∀ j, SigmaFinite (κ j)]

attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish

theorem originalIID_actual_root_refinement_signed_tilt_lower
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



    {δseq lossseq : ℕ → ℝ≥0∞}
    (D : ∀ d, PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r (δseq d) (lossseq d))
    (hloss : Tendsto lossseq atTop (𝓝 0))
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
    let C := fun d ↦ (D d).continuous.coefficient
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
        have hc := ((D d).intensity i).continuous_label
        rwa [(D d).intensity_roots i] at hc
      exact (C d i).roots_compact.image_of_continuousOn hlabel
    let scale := fun d i ↦ physicalSceneCanonicalHaarScale (q d i)
    let coord := fun d i n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) (j d i) (scale d i n)
    let H := fun d i ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) (j d i)
    let hH := fun d i ↦ measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj (j d i)
    let ref := fun d i (c : V d i) ↦ a ((P (j d i)).seed.curve
      ((Module.finBasis ℝ (P (j d i)).seed.covector.ker).equivFunL.symm c) 0)
    let root := fun d i ↦ physicalSceneOriginalMacroRootValue (P := P) (a := a) (j d i)
    ∀ Q : (d : ℕ) → (i : Fin (D d).continuous.count) → ℕ → ProbabilityMeasure (Macro d i × Macro d i),
    (∀ d i frame, (originalIIDFixedCandidateFullSceneJoint (Q d i frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier (q d i))
        (physicalScene_centered_unitCube_mass (Fin (q d i))) : Measure (V d i))) →
    let Λ := fun d i ↦ originalIIDWholeCoreSceneKernel (K d i) (hK d i).measurableSet (Q d i)
    ∀ input : (d : ℕ) → (i : Fin (D d).continuous.count) → V d i →
      Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint (q d i)) × LocalFiniteMeasure (LegalMarkedPhysicalPoint (q d i))),
    (∀ d i, ∀ᵐ c ∂(volume : Measure (V d i)).restrict (K d i),
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) (j d i) (ref d i c))
        (condDistrib u a μ (root d i c)) (condDistrib u a ν (root d i c)) (input d i c) (Λ d i c)) →
    (∀ d i frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : X d i) μ ν
      (by simpa only [Fintype.card_fin] using original_seed_transverse_finrank_pos (P (j d i)).seed hdim)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) (H d i) (hH d i)
      (fun x ↦ coord d i (m n) x-scale d i (m n) • originalMacroFrameCenter (q d i) frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj (j d i) (scale d i (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q d i frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : X d i)).measurable.aemeasurable))) →
    ∀ (L : ℝ),
    Tendsto (fun r ↦ ∫ p, (physicalSceneCanonicalHaarScale (finrank ℝ E-1) (m r))^2*
      ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
      ∂originalIIDOptimalMeanPlan μ ν (cost (m r)) (k (m r)) (m r+1)) atTop (𝓝 L) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ d in atTop,
      (∑ i, ∫ p, physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j d i) g t p-|t| * ‖g‖
        ∂(((volume : Measure (V d i)).restrict (K d i)) ⊗ₘ originalIIDRawPairPalmKernel (Λ d i))) ≤ L+ε := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  intro C j q V X Macro K hK scale coord H hH ref root Q hroot Λ input hprofile hweak L hphysical ε hε
  have hmass := populationHaarPressureCore_map_root_mass_tendsto_one hcomplete ha D hloss
  have hbound (d : ℕ) := (D d).originalIID_finite_core_signed_tilt_le_physical_limit
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim g t cost hcost k budget hbudget henergy m hm
    (Q d) (hroot d) (input d) (hprofile d) (hweak d) L hphysical
  have ht : Tendsto (fun d ↦ L+|t| * ‖g‖*(1-∑ i, ((μ.map a) (C d i).roots).toReal))
      atTop (𝓝 L) := by
    simpa only [sub_self,mul_zero,add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub hmass)) :
        Tendsto (fun d ↦ L+|t| * ‖g‖*(1-∑ i, ((μ.map a) (C d i).roots).toReal))
          atTop (𝓝 (L+|t| * ‖g‖*(1-1))))
  filter_upwards [ht.eventually (gt_mem_nhds (lt_add_of_pos_right L hε))] with d hd
  exact (hbound d).trans hd.le

end OTSelector.Reconstruction
