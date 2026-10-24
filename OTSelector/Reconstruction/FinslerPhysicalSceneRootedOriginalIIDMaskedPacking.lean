import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedAveragePacking
import OTSelector.Probability.IIDBipartiteAssignment

/-!
# Masked original packing in the original iid target and Dirichlet experiment

Chart absolute continuity supplies distinct iid targets. The fixed-target original
packing estimate is then integrated in the same target-times-Dirichlet environment.
The actual finite completed physical plans retain their original allocations almost
surely, including the physical source and target masks.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section WitnessMeasurability
variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

/-- The screened numeric witness is jointly measurable for the actual finite
physical families, including arbitrary measurable masks on both endpoints. -/
theorem measurable_rooted_masked_average_screened_rectangle_witness
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hΓp : Measurable Γp) (hΓm : Measurable Γm)
    (S : Set (M × M)) (hS : MeasurableSet S)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N ε : ℝ)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁)
    (Eroot : Set (ι → ℝ)) (hEroot : MeasurableSet Eroot) :
    let avg := fun w z ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan ((Γp w).restrict S) coord u N z +
       physicalSceneRootedPlan ((Γm w).restrict S) coord u N z)
    Measurable (fun v : Ω × (ι → ℝ) ↦ Eroot.indicator (fun z ↦
      ENNReal.ofReal ε * min 1 (min (avg v.1 z (A₀ ×ˢ B₀))
        (avg v.1 z (A₁ ×ˢ B₁)))) v.2) := by
  let avg := fun w z ↦ (2 : ℝ≥0∞)⁻¹ •
    (physicalSceneRootedPlan ((Γp w).restrict S) coord u N z +
     physicalSceneRootedPlan ((Γm w).restrict S) coord u N z)
  have hr (Γ : Ω → Measure (M × M)) (hΓ : Measurable Γ) :
      Measurable (fun w ↦ (Γ w).restrict S) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simp only [Measure.restrict_apply hV]
    exact (Measure.measurable_coe (hV.inter hS)).comp hΓ
  have hp := measurable_joint_physicalSceneRootedPlan
    (fun w ↦ (Γp w).restrict S) (hr Γp hΓp) coord hcoord u hu N
  have hm := measurable_joint_physicalSceneRootedPlan
    (fun w ↦ (Γm w).restrict S) (hr Γm hΓm) coord hcoord u hu N
  have heval (T : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (hT : MeasurableSet T) :
      Measurable (fun v : Ω × (ι → ℝ) ↦ avg v.1 v.2 T) := by
    simpa only [avg, Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      Function.comp_def, Pi.add_apply] using
      (((Measure.measurable_coe hT).comp hp).add
        ((Measure.measurable_coe hT).comp hm)).const_mul ((2 : ℝ≥0∞)⁻¹)
  have hw := (((measurable_const : Measurable (fun _ : Ω × (ι → ℝ) ↦ (1 : ℝ≥0∞))).min
    ((heval _ (hA₀.prod hB₀)).min (heval _ (hA₁.prod hB₁)))).const_mul
      (ENNReal.ofReal ε)).indicator (hEroot.preimage measurable_snd)
  convert hw using 1
  funext v
  by_cases hv : v.2 ∈ Eroot <;> simp [hv, avg]

end WitnessMeasurability

variable {ι E M : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {n : ℕ}

/-- In the original iid-target times Dirichlet experiment, every pair of jointly
measurable original opposite global optimizers satisfies the actual masked average
packing bound. Target distinctness, base optimizer existence, Fubini measurability,
and the almost-sure completion identity are all produced internally. -/
theorem lintegral_original_iid_finsler_rooted_average_screened_masked_rectangle_witness_le
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A : Set M} (hA : IsCompact A) (hμA : ∀ᵐ x ∂μ, x ∈ A)
    (pot : M → ℝ)
    (hpot : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    (scale : ℝ) (hscale : scale ≠ 0)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobe_bound : ∀ x y, |probe x y| ≤ G) (t : ℝ) (ht : 0 ≤ t)
    (ap am : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun v :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am v.1 v.2 j))
    (hp : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
        scale * ((F.lengthEDist x (w.1 j)).toReal - pot (w.1 j) + pot x) +
          t * probe x (w.1 j)) (ap w))
    (hm : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
        scale * ((F.lengthEDist x (w.1 j)).toReal - pot (w.1 j) + pot x) +
          (-t) * probe x (w.1 j)) (am w))
    (H Ks Kt : Set M) (hH : MeasurableSet H)
    (hKs : MeasurableSet Ks) (hKt : MeasurableSet Kt)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (Eroot : Set (ι → ℝ)) (hEroot : MeasurableSet Eroot)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ᵐ Y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
      ∀ z ∈ Eroot, ∀ x ∈ H ∩ Ks, ∀ x' ∈ H ∩ Ks,
        (coord x - z, pot x) ∈ A₀ → (coord x' - z, pot x') ∈ A₁ →
        ∀ j, Y j ∈ Kt → (coord (Y j) - z, pot (Y j)) ∈ B₀ →
        ∀ l, Y l ∈ Kt → (coord (Y l) - z, pot (Y l)) ∈ B₁ →
          ε ≤ scale * ((F.lengthEDist x (Y j)).toReal - pot (Y j) + pot x) +
            scale * ((F.lengthEDist x' (Y l)).toReal - pot (Y l) + pot x') -
            scale * ((F.lengthEDist x (Y l)).toReal - pot (Y l) + pot x) -
            scale * ((F.lengthEDist x' (Y j)).toReal - pot (Y j) + pot x'))
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
    let avg := fun w z ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ ap (fun w ↦ w.1) w).restrict
          ((H ∩ Ks) ×ˢ Kt)) coord pot N z +
       physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ am (fun w ↦ w.1) w).restrict
          ((H ∩ Ks) ×ˢ Kt)) coord pot N z)
    (∫⁻ w, ∫⁻ z, Eroot.indicator (fun z ↦ ENNReal.ofReal ε *
        min 1 (min (avg w z (A₀ ×ˢ B₀)) (avg w z (A₁ ×ˢ B₁)))) z
      ∂cavityRootMeasure volume D N ∂Penv) ≤
        ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instDiffuse : NullSingletonClass ν :=
    nullSingletonClass_of_chartwise_ac m ν hdim hνchart
  let Ω := (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)
  let Penv : Measure Ω := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γp := physicalSceneGlobalAllocationFamily μ ap (fun w : Ω ↦ w.1)
  let Γm := physicalSceneGlobalAllocationFamily μ am (fun w : Ω ↦ w.1)
  let S := (H ∩ Ks) ×ˢ Kt
  let avg := fun w z ↦ (2 : ℝ≥0∞)⁻¹ •
    (physicalSceneRootedPlan ((Γp w).restrict S) coord pot N z +
     physicalSceneRootedPlan ((Γm w).restrict S) coord pot N z)
  let W := fun w ↦ ∫⁻ z, Eroot.indicator (fun z ↦ ENNReal.ofReal ε *
    min 1 (min (avg w z (A₀ ×ˢ B₀)) (avg w z (A₁ ×ˢ B₁)))) z
      ∂cavityRootMeasure volume D N
  have hY (j : Fin (n + 1)) : Measurable (fun w : Ω ↦ w.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hΓp : Measurable Γp := measurable_physicalSceneGlobalAllocationFamily μ ap hpm _ hY
  have hΓm : Measurable Γm := measurable_physicalSceneGlobalAllocationFamily μ am hmm _ hY
  have hW : Measurable W := by
    have hw := measurable_rooted_masked_average_screened_rectangle_witness Γp Γm hΓp hΓm S
      ((hH.inter hKs).prod hKt) coord hcoord pot hpot.continuous.measurable N ε
      A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ Eroot hEroot
    change Measurable (fun w ↦ ∫⁻ z, Eroot.indicator (fun z ↦ ENNReal.ofReal ε *
      min 1 (min (avg w z (A₀ ×ˢ B₀)) (avg w z (A₁ ×ˢ B₁)))) z
        ∂cavityRootMeasure volume D N)
    simp only [cavityRootMeasure, lintegral_smul_measure, smul_eq_mul]
    exact hw.lintegral_prod_right'.const_mul _
  have heqp := physicalSceneGlobalAllocationFamily_ae_eq Penv μ ap
    (fun w : Ω ↦ w.1) (fun w ↦ w.2) (hp.mono fun _ h ↦ h.1)
  have heqm := physicalSceneGlobalAllocationFamily_ae_eq Penv μ am
    (fun w : Ω ↦ w.1) (fun w ↦ w.2) (hm.mono fun _ h ↦ h.1)
  have hb : ∀ᵐ w ∂Penv,
      W w ≤ ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hW measurable_const)).mpr
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1)) ν,
      hgap, Measure.ae_ae_of_ae_prod hp, Measure.ae_ae_of_ae_prod hm,
      Measure.ae_ae_of_ae_prod heqp, Measure.ae_ae_of_ae_prod heqm]
      with Y hYinj hgapY hpY hmY heqpY heqmY
    have hf := ae_dirichlet_original_finsler_rooted_average_screened_masked_rectangle_witness_le
      hF hcomplete hdim m μ hμchart hA hμA hpot scale hscale probe hprobe G hprobe_bound
      t ht Y hYinj H Ks Kt hH hKs hKt coord hcoord A₀ A₁ B₀ B₁
      hA₀ hA₁ hB₀ hB₁ hdisj K hK offset hbox Eroot hEroot ε hε D N hN hgapY
    filter_upwards [hf, hpY, hmY, heqpY, heqmY] with p hfp hpp hmp hep hem
    have hbound := hfp (ap (Y, p)) (am (Y, p)) hpp hmp
      (fun j ↦ (hpm j).comp (measurable_const.prodMk measurable_id))
      (fun j ↦ (hmm j).comp (measurable_const.prodMk measurable_id))
    change Γp (Y, p) = _ at hep
    change Γm (Y, p) = _ at hem
    simpa only [W, avg, hep, hem, S] using hbound
  change (∫⁻ w, W w ∂Penv) ≤ _
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι
        ∂Penv := lintegral_mono_ae hb
    _ = _ := by simp

end OTSelector.Reconstruction
