import OTSelector.Reconstruction.OriginalIIDActualCandidateLabelReadout

/-! One actual original iid kinetic budget pays every original-label unit candidate at zero tilt. -/
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

/-- Every same-law unit candidate retains its exact original label integral. The
sum of these real zero-tilt values is bounded by the ONE original physical iid
energy budget, including all actual core coefficients and intensity factors. -/
theorem PopulationHaarPressureCore.originalIID_actual_candidate_zero_label_budget
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
    (g : (M × M) →ᵇ ℝ)
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
    let θcoord := fun i (c : V i) ↦
      (originalSeedCoordinateHaarFactor (P (j i)).seed (κ (j i)) : ℝ) *
        (populationSeedPieceHaarDensity P a κ (μ.map a) (j i)
          ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm c)).toReal
    let θ := fun i ↦ (K i).indicator (θcoord i)
    let hθ : ∀ i, Measurable (θ i) := fun i ↦
      (measurable_originalIIDCoordinateIntensity hF hcomplete hu ha hinj hκ (j i)).indicator (hK i).measurableSet
    let Ξ := fun i ↦ originalIIDUnitColoredSceneKernel (q i) (θ i) (hθ i) (Λ i)
    let Amatrix := fun i ↦ physicalSceneOriginalMacroCoefficient (P := P) (a := a) (j i)
    let probe := fun i ↦ originalIIDMacroPhysicalProbe (P := P) (j i) g
    let value := fun i ↦ originalIIDCandidateNormalizedValue (q i) (θ i) (Ξ i) (Amatrix i) (probe i) 0
    let label := fun i ↦ physicalSceneOriginalMacroLabel (P := P) (a := a) (j i)
    (∀ i, Integrable (fun z ↦ value i (label i z)) ((μ.map a).restrict (C i).roots)) ∧
      (∑ i, ∫ z in (C i).roots, value i (label i z) ∂μ.map a) ≤ budget.toReal := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro C j q V X Macro K hK scale coord H hH ref root Q hroot Λ input hprofile hweak
    θcoord θ hθ Ξ Amatrix probe value label
  let joint := fun i ↦ ((volume : Measure (V i)).restrict (K i)) ⊗ₘ originalIIDRawPairPalmKernel (Λ i)
  let kin := fun i (p : V i × PhysicalPairPalmMark (Fin (q i))) ↦
    matrixQuadratic (Amatrix i (p.1,p.2.1)) p.2.2
  have hkinMeas (i) : Measurable (kin i) := continuous_matrixQuadratic.measurable.comp
    (((measurable_physicalSceneOriginalMacroCoefficient hF hcomplete hu ha hinj (j i)).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  have hdata (i : Fin D.continuous.count) := D.fixed_candidate_raw_joint_data
    hF hcomplete hu ha hinj i (Λ i) inferInstance gap hgap (input i) (hprofile i)
  letI (i : Fin D.continuous.count) : IsFiniteMeasure (joint i) := (hdata i).2.1
  have hlabels := D.originalIID_actual_candidate_label_readout
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim g 0 cost hcost k budget hbudget henergy m hm
    Q hroot input hprofile hweak
  have hglobal := D.originalIID_finite_core_shifted_tilt_le_global_liminf
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim g 0 cost hcost k budget hbudget henergy m hm
    Q hroot input hprofile hweak
  have hNNbound : (∑ i, ∫⁻ p, ENNReal.ofReal (kin i p) ∂joint i) ≤ budget := by
    have hev : ∀ᶠ r in atTop,
        (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) (m r))^2 *
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
          ∂originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ
          ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) ≤ budget :=
      hm henergy
    have hlim := liminf_le_liminf hev
    simp only [liminf_const] at hlim
    have hglobalClean : (∑ i, ∫⁻ c in K i, ∫⁻ mark,
        ENNReal.ofReal (kin i (c,mark)) ∂originalIIDRawPairPalmKernel (Λ i) c ∂volume) ≤
        liminf (fun r ↦ ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal
          ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) (m r))^2 *
            ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
          ∂originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ
          ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop := by
      simpa only [physicalSceneOriginalMacroShiftedTiltEnergy,zero_mul,abs_zero,add_zero] using hglobal
    have heq : (∑ i, ∫⁻ p, ENNReal.ofReal (kin i p) ∂joint i) =
        (∑ i, ∫⁻ c in K i, ∫⁻ mark, ENNReal.ofReal (kin i (c,mark))
          ∂originalIIDRawPairPalmKernel (Λ i) c ∂volume) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Measure.lintegral_compProd (hkinMeas i).ennreal_ofReal
    rw [heq]
    exact hglobalClean.trans hlim
  refine ⟨fun i ↦ (hlabels.2 i).2.1, ?_⟩
  have hcell (i : Fin D.continuous.count) :
      (∫ z in (C i).roots, value i (label i z) ∂μ.map a) =
        (∫⁻ p, ENNReal.ofReal (kin i p) ∂joint i).toReal := by
    have heq := (hlabels.2 i).2.2.1
    simp only [physicalSceneOriginalMacroShiftedTiltEnergy, zero_mul, abs_zero, add_zero, sub_zero] at heq
    exact heq.trans (integral_eq_lintegral_of_nonneg_ae (hdata i).2.2.1 (hkinMeas i).aestronglyMeasurable)
  simp_rw [hcell]
  rw [← ENNReal.toReal_sum (fun i _ ↦ ne_top_of_le_ne_top hbudget
    ((Finset.single_le_sum (fun j _ ↦ bot_le) (Finset.mem_univ i)).trans hNNbound))]
  exact ENNReal.toReal_mono hbudget hNNbound

end OTSelector.Reconstruction
