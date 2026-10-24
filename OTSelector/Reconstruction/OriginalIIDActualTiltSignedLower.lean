import OTSelector.Reconstruction.OriginalIIDActualTiltGlobalLower
import OTSelector.MeasureTheory.FiniteSignedShiftCancellation
import OTSelector.Reconstruction.OriginalIIDHaarRawPalmData
import OTSelector.Reconstruction.OriginalIIDRootMassRecovery

/-! Exact signed physical readouts of the original iid optimizer. All finite
source/core mass deficits are retained until original mass recovery is used. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The actual averaged two-array optimizer is itself a probability measure. -/
theorem isProbabilityMeasure_originalIIDOptimalMeanPlan
    {M : Type*} [MeasurableSpace M]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k : ℝ) :
    IsProbabilityMeasure (originalIIDOptimalMeanPlan μ ν cost k (n+1)) := by
  let P := originalIIDOptimalMeanPlan μ ν cost k (n+1)
  have hsource : P.map Prod.fst = μ := originalIIDOptimalMeanPlan_source μ ν cost hcost k
  letI : IsProbabilityMeasure (P.map Prod.fst) := by rw [hsource]; infer_instance
  exact Measure.isProbabilityMeasure_of_map Prod.fst

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Compact actual populations make every original physical signed readout
integrable, for the true mean optimizer and any finite scaling coefficient. -/
theorem integrable_originalIIDOptimalMeanPlan_physical_tilt
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k w : ℝ)
    (g : (M × M) →ᵇ ℝ) (t : ℝ) :
    Integrable (fun p : M × M ↦ w*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p)
      (originalIIDOptimalMeanPlan μ ν cost k (n+1)) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  let P := originalIIDOptimalMeanPlan μ ν cost k (n+1)
  letI : IsProbabilityMeasure P := isProbabilityMeasure_originalIIDOptimalMeanPlan μ ν n cost hcost k
  have hs : ∀ᵐ p ∂P, p.1 ∈ A := ae_of_ae_map measurable_fst.aemeasurable (by
    rw [show P.map Prod.fst = μ from originalIIDOptimalMeanPlan_source μ ν cost hcost k]
    exact hμ)
  have ht : ∀ᵐ p ∂P, p.2 ∈ B := ae_of_ae_map measurable_snd.aemeasurable (by
    rw [show P.map Prod.snd = ν from originalIIDOptimalMeanPlan_target μ ν cost hcost k]
    exact hν)
  obtain ⟨D,hD,hbound⟩ := F.exists_uniform_compact_distance_slack_bound hA hB hu
  apply (integrable_const (|w| * D+|t| * ‖g‖)).mono'
    (((F.measurable_distance_slack hu).const_mul w).add (g.continuous.measurable.const_mul t)).aestronglyMeasurable
  filter_upwards [hs,ht] with p hpA hpB
  have hb := hbound p.1 hpA p.2 hpB
  calc
    _ ≤ ‖w*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)‖+‖t*g p‖ := norm_add_le _ _
    _ = |w| * ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+|t| * ‖g p‖ := by
      rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hb.1]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg w))
      (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p) (abs_nonneg t))

/-- The shift |t| norm(g) makes the true physical signed integrand
nonnegative globally, using its original Lipschitz slack. -/
theorem originalIID_physical_shifted_tilt_nonneg
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (w : ℝ) (hw : 0 ≤ w) (g : (M × M) →ᵇ ℝ) (t : ℝ) (p : M × M) :
    0 ≤ w*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖ := by
  letI : MetricSpace M := F.metricSpace
  have hs := hu.le_add_mul p.2 p.1
  simp only [NNReal.coe_one,one_mul,dist_comm p.2 p.1] at hs
  have hslack : 0 ≤ (F.lengthEDist p.1 p.2).toReal-u p.2+u p.1 := by
    change 0 ≤ dist p.1 p.2-u p.2+u p.1
    linarith
  have habs : |t*g p| ≤ |t| * ‖g‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm p) (abs_nonneg t)
  have hn := (abs_le.mp habs).1
  linarith [mul_nonneg hw hslack]



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

/-- The actual full shifted lower passage implies a signed lower bound on
all retained original cells. The precise missing original label mass remains
in the shift error, and raw signed integrability is proved internally. -/
theorem PopulationHaarPressureCore.originalIID_finite_core_signed_tilt_le_physical_limit
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
    ∀ (L : ℝ),
    Tendsto (fun r ↦ ∫ p, (physicalSceneCanonicalHaarScale (finrank ℝ E-1) (m r))^2*
      ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
      ∂originalIIDOptimalMeanPlan μ ν (cost (m r)) (k (m r)) (m r+1)) atTop (𝓝 L) →
    let joint := fun i ↦ ((volume : Measure (V i)).restrict (K i)) ⊗ₘ originalIIDRawPairPalmKernel (Λ i)
    (∑ i, ∫ p, physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j i) g t p-|t| * ‖g‖ ∂joint i) ≤
      L+|t| * ‖g‖*(1-∑ i, ((μ.map a) (C i).roots).toReal) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro C j q V X Macro K hK scale coord H hH ref root Q hroot Λ input hprofile hweak L hphysical joint
  let shift := |t| * ‖g‖
  let rawEnergy := fun i ↦ physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j i) g t
  let physical := fun r ↦ originalIIDOptimalMeanPlan μ ν (cost (m r)) (k (m r)) (m r+1)
  let physicalEnergy := fun r (p : M × M) ↦
    (physicalSceneCanonicalHaarScale (finrank ℝ E-1) (m r))^2*
      ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
  have hdata (i : Fin D.continuous.count) := D.fixed_candidate_raw_joint_data
    hF hcomplete hu ha hinj i (Λ i) inferInstance gap hgap (input i) (hprofile i)
  letI (i : Fin D.continuous.count) : IsFiniteMeasure (joint i) := (hdata i).2.1
  letI (n : ℕ) : IsProbabilityMeasure (physical n) :=
    isProbabilityMeasure_originalIIDOptimalMeanPlan μ ν (m n) (cost (m n)) (hcost (m n)) (k (m n))
  have hmass (n : ℕ) : (physical n).real univ = 1 := by simp
  have hphysInt (n : ℕ) : Integrable (physicalEnergy n) (physical n) :=
    integrable_originalIIDOptimalMeanPlan_physical_tilt hcomplete hu hA hB hμ hν
      (m n) (cost (m n)) (hcost (m n)) (k (m n)) _ g t
  have hphysSign (n : ℕ) : ∀ᵐ p ∂physical n, 0 ≤ physicalEnergy n p+shift :=
    Eventually.of_forall (fun p ↦ originalIID_physical_shifted_tilt_nonneg hu _ (sq_nonneg _) g t p)
  obtain ⟨hlimitSign,hshiftTendsto⟩ := tendsto_shifted_lintegral_of_signed_integral_tendsto
    physical physicalEnergy hphysInt shift 1 L hphysSign hmass hphysical
  have hrawMeas (i : Fin D.continuous.count) : Measurable (rawEnergy i) :=
    measurable_physicalSceneOriginalMacroShiftedTiltEnergy hF hcomplete hu ha hinj (j i) g t
  have hmeanReadout (n : ℕ) :
      (∫⁻ p, ENNReal.ofReal (physicalEnergy n p+shift) ∂physical n) =
      ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (physicalEnergy n p+shift)
        ∂originalIIDOptimalPhysicalPlan (n := m n+1) (cost (m n)) (k (m n)) ξ
        ∂(Measure.pi (fun _ : Fin (m n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (m n+1) ↦ ν)) := by
    apply lintegral_originalIIDOptimalMeanPlan μ ν (cost (m n)) (hcost (m n)) (k (m n)) (m n+1)
    exact ((((F.measurable_distance_slack hu).const_mul _).add
      (g.continuous.measurable.const_mul t)).add_const shift).ennreal_ofReal
  have hglobal := D.originalIID_finite_core_shifted_tilt_le_global_liminf
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim g t cost hcost k budget hbudget henergy m hm
    Q hroot input hprofile hweak
  have hshift : (∑ i, ∫⁻ p, ENNReal.ofReal (rawEnergy i p) ∂joint i) ≤
      liminf (fun n ↦ ∫⁻ p, ENNReal.ofReal (physicalEnergy n p+shift) ∂physical n) atTop := by
    simp_rw [hmeanReadout]
    convert hglobal using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact Measure.lintegral_compProd (hrawMeas i).ennreal_ofReal
  have hrawFinite (i : Fin D.continuous.count) :
      (∫⁻ p, ENNReal.ofReal (rawEnergy i p) ∂joint i) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (Finset.single_le_sum (fun j _ ↦ bot_le) (Finset.mem_univ i)).trans
      (hshift.trans_eq hshiftTendsto.liminf_eq)
  have hrawSign (i : Fin D.continuous.count) : ∀ᵐ p ∂joint i, 0 ≤ rawEnergy i p := (hdata i).2.2.2 g t
  have hrawInt (i : Fin D.continuous.count) : Integrable (rawEnergy i) (joint i) :=
    (lintegral_ofReal_ne_top_iff_integrable (hrawMeas i).aestronglyMeasurable (hrawSign i)).mp (hrawFinite i)
  have hsignedInt (i : Fin D.continuous.count) : Integrable (fun p ↦ rawEnergy i p-shift) (joint i) :=
    (hrawInt i).sub (integrable_const shift)
  have hjointMass (i : Fin D.continuous.count) : (joint i).real univ = ((μ.map a) (C i).roots).toReal := by
    unfold Measure.real
    rw [(hdata i).1]
  have hresult := sum_integral_le_of_shifted_lintegral_sum_le_liminf
    joint physical (fun i p ↦ rawEnergy i p-shift) hsignedInt physicalEnergy hphysInt
    shift (mul_nonneg (abs_nonneg t) (norm_nonneg g))
    (fun i ↦ by simpa only [sub_add_cancel] using hrawSign i) hphysSign 1 L hmass hphysical
    (by simpa only [sub_add_cancel] using hshift)
  simpa only [hjointMass] using hresult

end OTSelector.Reconstruction
