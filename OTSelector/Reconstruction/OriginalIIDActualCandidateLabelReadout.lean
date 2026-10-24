import OTSelector.Reconstruction.OriginalIIDActualTiltSignedLower
import OTSelector.Reconstruction.OriginalIIDUnitDensityValueReadout
import OTSelector.Reconstruction.OriginalIIDCandidateLabelTransport

/-! Same-candidate unit values, original Haar labels and actual finite energy.
The normalized value is a measurable readout of the existing colored kernel;
its original intensity factor is retained before label change of variables. -/
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

section MeasurableUnitValue
variable {C : Type*} [MeasurableSpace C] (q : ℕ)
local instance (q : ℕ) : PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance (q : ℕ) : PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual Palm of the same measurable colored scene kernel. -/
def originalIIDColoredPairPalmKernel (Ξ : Kernel C (LegalMarkedOptimalInputScene q)) :
    Kernel C (PhysicalPairPalmMark (Fin q)) :=
  ((physicalScenePairKernel ∘ₖ (Ξ.map Prod.fst)).restrict
    ((measurableSet_palmUnitCube (Fin q)).prod MeasurableSet.univ)).map Prod.snd

instance originalIIDColoredPairPalmKernelIsSFinite
    (Ξ : Kernel C (LegalMarkedOptimalInputScene q)) [IsSFiniteKernel Ξ] :
    IsSFiniteKernel (originalIIDColoredPairPalmKernel q Ξ) := by
  unfold originalIIDColoredPairPalmKernel
  infer_instance

@[simp] theorem originalIIDColoredPairPalmKernel_apply
    (Ξ : Kernel C (LegalMarkedOptimalInputScene q)) [IsMarkovKernel Ξ] (c : C) :
    originalIIDColoredPairPalmKernel q Ξ c = legalMarkedJointPalm q ⟨Ξ c,inferInstance⟩ := by
  rw [originalIIDColoredPairPalmKernel,Kernel.map_apply _ measurable_snd,
    Kernel.restrict_apply,Kernel.comp_apply,Kernel.map_apply _ measurable_fst]
  rfl

/-- Original-label normalization of the signed value of this exact unit law.
Its positive branch is theta^(-2/q) times its true unit-density value. -/
def originalIIDCandidateNormalizedValue
    (θ : C → ℝ) (Ξ : Kernel C (LegalMarkedOptimalInputScene q))
    (A : C × (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (probe : C × (ℝ × ℝ) → ℝ) (t : ℝ) (c : C) : ℝ :=
  θ c ^ (-2/(q : ℝ)) *
    ((∫ m, matrixQuadratic (A (c,m.1)) m.2 ∂originalIIDColoredPairPalmKernel q Ξ c) +
      (t * θ c ^ (2/(q : ℝ))) * ∫ m, probe (c,m.1) ∂originalIIDColoredPairPalmKernel q Ξ c)

/-- The normalized same-law candidate value is jointly measurable in the root.
No energy bound or measurable choice of a matching structure is requested. -/
theorem measurable_originalIIDCandidateNormalizedValue
    (hq : 0 < q) (θ : C → ℝ) (hθ : Measurable θ) (hθn : ∀ c, 0 ≤ θ c)
    (Ξ : Kernel C (LegalMarkedOptimalInputScene q)) [IsSFiniteKernel Ξ]
    (A : C × (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A)
    (probe : C × (ℝ × ℝ) → ℝ) (hp : Measurable probe) (t : ℝ) :
    Measurable (originalIIDCandidateNormalizedValue q θ Ξ A probe t) := by
  have hkin : Measurable (fun p : C × PhysicalPairPalmMark (Fin q) ↦
      matrixQuadratic (A (p.1,p.2.1)) p.2.2) := continuous_matrixQuadratic.measurable.comp
    ((hA.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  have hprobe : Measurable (fun p : C × PhysicalPairPalmMark (Fin q) ↦ probe (p.1,p.2.1)) :=
    hp.comp (measurable_fst.prodMk measurable_snd.fst)
  have hpow : Measurable (fun c ↦ θ c ^ (2/(q : ℝ))) :=
    (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 2/(q : ℝ))).measurable.comp hθ
  have hneg : Measurable (fun c ↦ θ c ^ (-2/(q : ℝ))) := by
    convert hpow.inv using 1
    funext c
    rw [show (-2/(q : ℝ)) = -(2/(q : ℝ)) by ring,Real.rpow_neg (hθn c)]
    rfl
  exact hneg.mul ((hkin.stronglyMeasurable.integral_kernel_prod_right').measurable.add
    ((hpow.const_mul t).mul (hprobe.stronglyMeasurable.integral_kernel_prod_right').measurable))

/-- The exact original intensity multiplies its normalized unit value back to
the raw signed readout, including the real zero-intensity empty-law branch. -/
theorem originalIIDCandidateNormalizedValue_mul_intensity
    (hq : 0 < q) (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (c : C) (hθc : 0 ≤ θ c) (gap : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (h : OriginalIIDConditionalMatchingProfile gap (θ c) α β input (Λ c))
    (A : C × (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A)
    (probe : C × (ℝ × ℝ) → ℝ) (hp : Measurable probe) (t : ℝ) :
    θ c * originalIIDCandidateNormalizedValue q θ
      (originalIIDUnitColoredSceneKernel q θ hθ Λ) A probe t c =
      (∫ m, matrixQuadratic (A (c,m.1)) m.2 ∂originalIIDRawPairPalmKernel Λ c) +
        t * ∫ m, probe (c,m.1) ∂originalIIDRawPairPalmKernel Λ c := by
  let Ξ := originalIIDUnitColoredSceneKernel q θ hθ Λ
  have hAp : Measurable (fun clocks ↦ A (c,clocks)) := hA.comp (measurable_const.prodMk measurable_id)
  have hpp : Measurable (fun clocks ↦ probe (c,clocks)) := hp.comp (measurable_const.prodMk measurable_id)
  by_cases hpos : 0 < θ c
  · have hv := originalIIDUnitColoredSceneKernel_density_weighted_value q hq θ hθ Λ c hθc gap α β input h
      (fun a b v ↦ matrixQuadratic (A (c,(a,b))) v)
      (continuous_matrixQuadratic.measurable.comp ((hAp.comp measurable_fst).prodMk measurable_snd))
      (fun a b d _ v ↦ matrixQuadratic_smul (A (c,(a,b))) d v)
      (fun a b ↦ probe (c,(a,b))) hpp t
    have hfactor : θ c * θ c ^ (-2/(q : ℝ)) = θ c ^ (1-2/(q : ℝ)) := by
      calc
        _ = θ c ^ ((1 : ℝ)+(-2/(q : ℝ))) := by
          simpa only [Real.rpow_one] using (Real.rpow_add hpos 1 (-2/(q : ℝ))).symm
        _ = _ := by congr 1; ring
    dsimp only [originalIIDCandidateNormalizedValue]
    rw [← mul_assoc,hfactor]
    simpa only [originalIIDColoredPairPalmKernel_apply,legalMarkedJointPalm,legalMarkedInputPairLaw,ProbabilityMeasure.toMeasure_map,ProbabilityMeasure.coe_mk,originalIIDRawPairPalmKernel_apply] using hv
  · have hz : θ c = 0 := le_antisymm (le_of_not_gt hpos) hθc
    have hzero := original_raw_palm_eq_zero_of_matching_profile q gap α β input (Λ c)
      (by simpa only [hz] using h)
    simp only [hz,zero_mul,originalIIDRawPairPalmKernel_apply,hzero,integral_zero_measure,mul_zero,add_zero]


/-- Finite raw energy of the unchanged joint law supplies integrability of
its density-weighted same-unit value, and an actual legal matching at each
positive-intensity root. This helper is consumed by the physical producer. -/
theorem originalIIDCandidateNormalizedValue_integrable_readout
    (η : Measure C) [SFinite η] (hq : 0 < q)
    (θ : C → ℝ) (hθ : Measurable θ) (hθn : ∀ c, 0 ≤ θ c)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    [IsFiniteMeasure (η ⊗ₘ originalIIDRawPairPalmKernel Λ)]
    (gap : ℝ) (hgap : 0 < gap)
    (α β : C → Measure ℝ) [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (input : C → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (hprofile : ∀ᵐ c ∂η, OriginalIIDConditionalMatchingProfile gap (θ c) (α c) (β c) (input c) (Λ c))
    (A : C × (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A)
    (hraw : Integrable (fun p : C × PhysicalPairPalmMark (Fin q) ↦ matrixQuadratic (A (p.1,p.2.1)) p.2.2)
      (η ⊗ₘ originalIIDRawPairPalmKernel Λ))
    (probe : C × (ℝ × ℝ) → ℝ) (hp : Measurable probe)
    (G : ℝ) (hbound : ∀ c a b, |probe (c,(a,b))| ≤ G) (t : ℝ) :
    let Ξ := originalIIDUnitColoredSceneKernel q θ hθ Λ
    let value := originalIIDCandidateNormalizedValue q θ Ξ A probe t
    Integrable (fun c ↦ θ c*value c) η ∧
      (∫ c, θ c*value c ∂η) =
        ∫ p, matrixQuadratic (A (p.1,p.2.1)) p.2.2+t*probe (p.1,p.2.1)
          ∂η ⊗ₘ originalIIDRawPairPalmKernel Λ ∧
      ∀ᵐ c ∂η, 0 < θ c →
        ∃ M : LegalWeightedStationaryPoissonMatching q (α c) (β c)
            (fun a b v ↦ matrixQuadratic (A (c,(a,b))) v) (fun a b ↦ probe (c,(a,b))),
          M.law = ⟨Ξ c,inferInstance⟩ ∧ value c = θ c ^ (-2/(q : ℝ))*M.value (t*θ c ^ (2/(q : ℝ))) := by
  intro Ξ value
  let κraw := originalIIDRawPairPalmKernel Λ
  let kin := fun p : C × PhysicalPairPalmMark (Fin q) ↦ matrixQuadratic (A (p.1,p.2.1)) p.2.2
  let probeFull := fun p : C × PhysicalPairPalmMark (Fin q) ↦ probe (p.1,p.2.1)
  have hpm : Measurable probeFull := hp.comp (measurable_fst.prodMk measurable_snd.fst)
  have hprobe : Integrable probeFull (η ⊗ₘ κraw) := by
    apply (integrable_const G).mono' hpm.aestronglyMeasurable
    exact .of_forall (fun p ↦ by simpa only [probeFull,Real.norm_eq_abs] using hbound p.1 p.2.1.1 p.2.1.2)
  have hsigned : Integrable (fun p ↦ kin p+t*probeFull p) (η ⊗ₘ κraw) := hraw.add (hprobe.const_mul t)
  have haeKin := ((Measure.integrable_compProd_iff hraw.1).mp hraw).1
  have haeProbe := ((Measure.integrable_compProd_iff hprobe.1).mp hprobe).1
  have hmeas : Measurable (fun p ↦ kin p+t*probeFull p) :=
    (continuous_matrixQuadratic.measurable.comp
      ((hA.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)).add (hpm.const_mul t)
  have heq : (fun c ↦ θ c*value c) =ᵐ[η]
      (fun c ↦ ∫ m, kin (c,m)+t*probeFull (c,m) ∂κraw c) := by
    filter_upwards [hprofile,haeKin,haeProbe] with c hc hk hpInt
    rw [integral_add hk (hpInt.const_mul t),integral_const_mul]
    exact originalIIDCandidateNormalizedValue_mul_intensity q hq θ hθ Λ c (hθn c) gap (α c) (β c) (input c) hc A hA probe hp t
  have hnorm := ((Measure.integrable_compProd_iff hsigned.1).mp hsigned).2
  have houter : Integrable (fun c ↦ ∫ m, kin (c,m)+t*probeFull (c,m) ∂κraw c) η := by
    apply hnorm.mono
      (hmeas.stronglyMeasurable.integral_kernel_prod_right' (κ := κraw)).aestronglyMeasurable
    exact .of_forall (fun c ↦ (norm_integral_le_integral_norm _).trans_eq
      (Real.norm_of_nonneg (integral_nonneg (fun m ↦ norm_nonneg (kin (c,m)+t*probeFull (c,m))))).symm)
  refine ⟨houter.congr heq.symm,?_,?_⟩
  · exact (integral_congr_ae heq).trans (Measure.integral_compProd hsigned).symm
  · filter_upwards [hprofile,haeKin] with c hc hk hpos
    obtain ⟨M,hM,hmvalue⟩ := exists_originalLegalWeightedCandidate_density_value q hq gap (θ c) hgap hpos
      (α c) (β c) (input c) (Λ c) hc (fun clocks ↦ A (c,clocks))
      (hA.comp (measurable_const.prodMk measurable_id))
      (by simpa only [originalIIDRawPairPalmKernel_apply] using hk)
      (fun a b ↦ probe (c,(a,b))) (hp.comp (measurable_const.prodMk measurable_id)) G (hbound c) t
    have hMlaw : M.law = (⟨Ξ c,inferInstance⟩ : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) := by
      apply ProbabilityMeasure.toMeasure_injective
      rw [hM]
      exact (originalIIDUnitColoredSceneKernel_eq_positive q θ hθ Λ c hpos).symm
    refine ⟨M,hMlaw,?_⟩
    dsimp only [value,originalIIDCandidateNormalizedValue]
    rw [originalIIDColoredPairPalmKernel_apply,← hMlaw]
    rfl

end MeasurableUnitValue

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


/-- The unchanged original paired physical probe in the actual seed frame. -/
def originalIIDMacroPhysicalProbe (j : ℕ) (g : (M × M) →ᵇ ℝ)
    (p : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ)) : ℝ :=
  let S := (P j).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  g (populationSeedPhysicalMap S (e.symm p.1,p.2.1),
    populationSeedPhysicalMap S (e.symm p.1,p.2.2))

theorem measurable_originalIIDMacroPhysicalProbe (j : ℕ) (g : (M × M) →ᵇ ℝ)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) :
    Measurable (originalIIDMacroPhysicalProbe (P := P) j g) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  let S := (P j).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  exact g.continuous.measurable.comp
    (((measurable_populationSeedPhysicalMap S).comp
      ((e.symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd.fst)).prodMk
    ((measurable_populationSeedPhysicalMap S).comp
      ((e.symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd.snd)))

theorem originalIIDMacroPhysicalProbe_bound (j : ℕ) (g : (M × M) →ᵇ ℝ) (c) (a b : ℝ) :
    |originalIIDMacroPhysicalProbe (P := P) j g (c,(a,b))| ≤ ‖g‖ := by
  exact g.norm_coe_le_norm _




theorem PopulationHaarPressureCore.originalIID_actual_candidate_label_readout
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
    let value := fun i ↦ originalIIDCandidateNormalizedValue (q i) (θ i) (Ξ i) (Amatrix i) (probe i) t
    let label := fun i ↦ physicalSceneOriginalMacroLabel (P := P) (a := a) (j i)
    (∀ i, q i = finrank ℝ E-1) ∧
    ∀ i, Measurable (fun z ↦ value i (label i z)) ∧
      Integrable (fun z ↦ value i (label i z)) ((μ.map a).restrict (C i).roots) ∧
      (∫ z in (C i).roots, value i (label i z) ∂μ.map a) =
        ∫ p, physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j i) g t p-|t| * ‖g‖
          ∂((volume : Measure (V i)).restrict (K i)) ⊗ₘ originalIIDRawPairPalmKernel (Λ i) ∧
      ∀ᵐ z ∂(μ.map a).restrict (C i).roots,
        ∃ M : LegalWeightedStationaryPoissonMatching (q i)
            (condDistrib u a μ (root i (label i z))) (condDistrib u a ν (root i (label i z)))
            (fun a b v ↦ matrixQuadratic (Amatrix i (label i z,(a,b))) v)
            (fun a b ↦ probe i (label i z,(a,b))),
          M.law = ⟨Ξ i (label i z),inferInstance⟩ ∧
          value i (label i z) = θcoord i (label i z) ^ (-2/(q i : ℝ))*
            M.value (t*θcoord i (label i z) ^ (2/(q i : ℝ))) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro C j q V X Macro K hK scale coord H hH ref root Q hroot Λ input hprofile hweak
    θcoord θ hθ Ξ Amatrix probe value label
  let η := fun i ↦ (volume : Measure (V i)).restrict (K i)
  let joint := fun i ↦ (η i) ⊗ₘ originalIIDRawPairPalmKernel (Λ i)
  let kin := fun i (p : V i × PhysicalPairPalmMark (Fin (q i))) ↦ matrixQuadratic (Amatrix i (p.1,p.2.1)) p.2.2
  have hAmeas (i) : Measurable (Amatrix i) := measurable_physicalSceneOriginalMacroCoefficient hF hcomplete hu ha hinj (j i)
  have hkinMeas (i) : Measurable (kin i) := continuous_matrixQuadratic.measurable.comp
    (((hAmeas i).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  have hdata (i : Fin D.continuous.count) := D.fixed_candidate_raw_joint_data
    hF hcomplete hu ha hinj i (Λ i) inferInstance gap hgap (input i) (hprofile i)
  letI (i : Fin D.continuous.count) : IsFiniteMeasure (joint i) := (hdata i).2.1
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
  have hrawInt (i : Fin D.continuous.count) : Integrable (kin i) (joint i) := by
    apply (lintegral_ofReal_ne_top_iff_integrable (hkinMeas i).aestronglyMeasurable (hdata i).2.2.1).mp
    exact ne_top_of_le_ne_top hbudget
      ((Finset.single_le_sum (fun j _ ↦ bot_le) (Finset.mem_univ i)).trans hNNbound)
  have hθn (i) (c : V i) : 0 ≤ θcoord i c := mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hθunitn (i) (c : V i) : 0 ≤ θ i c := indicator_nonneg (fun c _ ↦ hθn i c) c
  have hθcoordMeas (i) : Measurable (θcoord i) := measurable_originalIIDCoordinateIntensity hF hcomplete hu ha hinj hκ (j i)
  have hlabelMeas (i) : Measurable (label i) :=
    (Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.continuous.measurable.comp
      (measurable_populationSeedRootLabelValue (P (j i)).seed hF hcomplete hu ha hinj)
  have hcoordinate (i) : ∀ c ∈ K i, θcoord i c =
      originalSeedCoordinateIntensity P a κ (μ.map a) (j i) (ref i c) := by
    intro c hc
    obtain ⟨z,hz,rfl⟩ := hc
    have hrecover : ref i (label i z) = z := by
      change a ((P (j i)).seed.curve
        ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm
          ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL
            (populationSeedRootLabelValue (P (j i)).seed a z))) 0) = z
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact (D.intensity i).root_identity z ((D.intensity_roots i).symm ▸ hz)
    change (originalSeedCoordinateHaarFactor (P (j i)).seed (κ (j i)) : ℝ) *
      (populationSeedPieceHaarDensity P a κ (μ.map a) (j i)
        ((Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm (label i z))).toReal = _
    rw [show (Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm (label i z) =
      populationSeedRootLabelValue (P (j i)).seed a z from
      (Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL.symm_apply_apply _]
    change _ = (originalSeedCoordinateHaarFactor (P (j i)).seed (κ (j i)) : ℝ) *
      (populationSeedPieceHaarDensity P a κ (μ.map a) (j i)
        (populationSeedRootLabelValue (P (j i)).seed a (ref i (label i z)))).toReal
    rw [hrecover]
  have hprofileUnit (i) : ∀ᵐ c ∂η i, OriginalIIDConditionalMatchingProfile gap (θ i c)
      (condDistrib u a μ (root i c)) (condDistrib u a ν (root i c)) (input i c) (Λ i c) := by
    filter_upwards [hprofile i,ae_restrict_mem (hK i).measurableSet] with c hc hmem
    change OriginalIIDConditionalMatchingProfile gap
      (originalSeedCoordinateIntensity P a κ (μ.map a) (j i) (ref i c))
      (condDistrib u a μ (root i c)) (condDistrib u a ν (root i c)) (input i c) (Λ i c) at hc
    simpa only [θ,indicator_of_mem hmem,hcoordinate i c hmem] using hc
  have hreadout (i : Fin D.continuous.count) := originalIIDCandidateNormalizedValue_integrable_readout (q i)
    (η i) (original_seed_transverse_finrank_pos (P (j i)).seed hdim)
    (θ i) (hθ i) (hθunitn i) (Λ i) gap hgap
    (fun c ↦ condDistrib u a μ (root i c)) (fun c ↦ condDistrib u a ν (root i c)) (input i) (hprofileUnit i)
    (Amatrix i) (hAmeas i) (hrawInt i) (probe i) (measurable_originalIIDMacroPhysicalProbe (j i) g hcomplete)
    ‖g‖ (originalIIDMacroPhysicalProbe_bound (j i) g) t
  have hvalueMeas (i) : Measurable (value i) := measurable_originalIIDCandidateNormalizedValue (q i)
    (original_seed_transverse_finrank_pos (P (j i)).seed hdim) (θ i) (hθ i) (hθunitn i) (Ξ i)
    (Amatrix i) (hAmeas i) (probe i) (measurable_originalIIDMacroPhysicalProbe (j i) g hcomplete) t
  refine ⟨fun i ↦ originalIID_seed_transverse_finrank_eq (P (j i)).seed,?_⟩
  intro i
  have hθeq : θ i =ᵐ[η i] θcoord i := by
    filter_upwards [ae_restrict_mem (hK i).measurableSet] with c hc
    exact indicator_of_mem hc _
  have hweightedInt : Integrable (fun c ↦ θcoord i c*value i c) (η i) :=
    (hreadout i).1.congr (hθeq.mono (fun c hc ↦ by
      change θ i c*value i c = θcoord i c*value i c
      rw [hc]))
  have hnest : (Module.finBasis ℝ (P (j i)).seed.covector.ker).equivFunL ''
      (populationSeedRootLabelValue (P (j i)).seed a '' (C i).roots) = K i := by
    simp only [K,physicalSceneOriginalMacroLabel,image_image]
    rfl
  have htransport := (D.candidate_label_transport hF hcomplete hu ha hinj i).2.1
    (value i) (hvalueMeas i).aestronglyMeasurable
  change (Integrable (fun z ↦ value i (label i z)) ((μ.map a).restrict (C i).roots) ↔
      Integrable (fun c ↦ θcoord i c*value i c) (volume.restrict _)) ∧ _ at htransport
  rw [hnest] at htransport
  refine ⟨(hvalueMeas i).comp (hlabelMeas i),htransport.1.mpr hweightedInt,?_,?_⟩
  · refine htransport.2.trans ?_
    calc
      _ = ∫ c, θ i c*value i c ∂η i := by
        change (∫ c, θcoord i c*value i c ∂η i) = _
        apply integral_congr_ae
        filter_upwards [hθeq] with c hc
        exact congrArg (fun v : ℝ ↦ v*value i c) hc.symm
      _ = ∫ p, kin i p+t*probe i (p.1,p.2.1) ∂joint i := (hreadout i).2.1
      _ = _ := integral_congr_ae (Eventually.of_forall (fun p ↦ by
        dsimp only [kin,Amatrix,probe,originalIIDMacroPhysicalProbe,physicalSceneOriginalMacroShiftedTiltEnergy]
        ring))
  · have hmap := D.map_original_label_eq_coordinate_intensity hF hcomplete hu ha hinj i
    change ((μ.map a).restrict (C i).roots).map (label i) =
      (volume.restrict _).withDensity (fun c ↦ ENNReal.ofReal (θcoord i c)) at hmap
    rw [hnest] at hmap
    let good := fun c : V i ↦ ∃ M : LegalWeightedStationaryPoissonMatching (q i)
        (condDistrib u a μ (root i c)) (condDistrib u a ν (root i c))
        (fun a b v ↦ matrixQuadratic (Amatrix i (c,(a,b))) v) (fun a b ↦ probe i (c,(a,b))),
        M.law = ⟨Ξ i c,inferInstance⟩ ∧ value i c = θcoord i c ^ (-2/(q i : ℝ))*
          M.value (t*θcoord i c ^ (2/(q i : ℝ)))
    change ∀ᵐ z ∂(μ.map a).restrict (C i).roots, good (label i z)
    have hae : ∀ᵐ c ∂η i, 0 < θcoord i c → good c := by
      filter_upwards [(hreadout i).2.2,ae_restrict_mem (hK i).measurableSet] with c hc hmem
      intro hpos
      simpa only [θ,indicator_of_mem hmem] using hc (by simpa only [θ,indicator_of_mem hmem] using hpos)
    apply ae_of_ae_map (μ := (μ.map a).restrict (C i).roots) (p := good) (hlabelMeas i).aemeasurable
    rw [hmap,ae_withDensity_iff (hθcoordMeas i).ennreal_ofReal]
    filter_upwards [hae] with c hc hnonzero
    exact hc (lt_of_not_ge (fun h ↦ hnonzero (ENNReal.ofReal_eq_zero.mpr h)))



/-- The genuine finite-core signed lower now uses the exact same unit-law
value integrated against original labels. Its original omitted-root shift
remains explicit until actual stored-loss root refinement. -/
theorem PopulationHaarPressureCore.originalIID_actual_candidate_label_signed_lower
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
    let value := fun i ↦ originalIIDCandidateNormalizedValue (q i) (θ i) (Ξ i) (Amatrix i) (probe i) t
    let label := fun i ↦ physicalSceneOriginalMacroLabel (P := P) (a := a) (j i)
    ∀ (L : ℝ),
    Tendsto (fun r ↦ ∫ p, (physicalSceneCanonicalHaarScale (finrank ℝ E-1) (m r))^2*
      ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
      ∂originalIIDOptimalMeanPlan μ ν (cost (m r)) (k (m r)) (m r+1)) atTop (𝓝 L) →
    (∑ i, ∫ z in (C i).roots, value i (label i z) ∂μ.map a) ≤
      L+|t| * ‖g‖*(1-∑ i, ((μ.map a) (C i).roots).toReal) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  intro C j q V X Macro K hK scale coord H hH ref root Q hroot Λ input hprofile hweak
    θcoord θ hθ Ξ Amatrix probe value label L hphysical
  have hlabels := D.originalIID_actual_candidate_label_readout
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim g t cost hcost k budget hbudget henergy m hm
    Q hroot input hprofile hweak
  have hsigned := D.originalIID_finite_core_signed_tilt_le_physical_limit
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hμ hν hreg hμreg
    hface hgap hdist hGood hdim g t cost hcost k budget hbudget henergy m hm
    Q hroot input hprofile hweak L hphysical
  calc
    _ = ∑ i, ∫ p, physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) (j i) g t p-|t| * ‖g‖
        ∂((volume : Measure (V i)).restrict (K i)) ⊗ₘ originalIIDRawPairPalmKernel (Λ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hlabels.2 i).2.2.1
    _ ≤ _ := hsigned

end OTSelector.Reconstruction
