import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreDisplacement

/-!
# Original conditional scalar screens control full physical target tails

The retained conditional legal-coupling loss bounds both scalar marginal tails.
Exact original disintegration turns those screens into physical population mass.
Together with the produced discarded-root loss, this bounds the entire physical
target-core complement and its actual global-allocation Haar-window intensity.
The local-core constructor retains the original conditional forward coupling.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry Filter
open OTSelector.Probability
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Original conditional legal-coupling loss controls both complete marginal
scalar tails on the same actual coefficient interval. -/
theorem conditional_scalar_interval_tails_lt
    (i : Fin D.haar.continuous.count) {z : ℚ → M}
    (hz : z ∈ (D.haar.continuous.coefficient i).roots)
    (hlegal : ∃ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a η₀ z)
      (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2) :
    let C := D.haar.continuous.coefficient i
    (condDistrib u a η₀ z) (Icc (C.window.val.1 : ℝ) C.window.val.2.1)ᶜ < δ ∧
      (condDistrib u a η₁ z) (Icc (C.window.val.1 : ℝ) C.window.val.2.1)ᶜ < δ := by
  let C := D.haar.continuous.coefficient i
  obtain ⟨π, hπ, horder⟩ := hlegal
  have hloss := C.coupling_loss z hz π hπ horder
  have h0 : (condDistrib u a η₀ z) (Icc (C.window.val.1 : ℝ) C.window.val.2.1)ᶜ ≤
      π C.window.regionᶜ := by
    rw [← hπ.1, Measure.map_apply measurable_fst measurableSet_Icc.compl]
    exact measure_mono (fun p hp hmem ↦ hp hmem.1.1)
  have h1 : (condDistrib u a η₁ z) (Icc (C.window.val.1 : ℝ) C.window.val.2.1)ᶜ ≤
      π C.window.regionᶜ := by
    rw [← hπ.2, Measure.map_apply measurable_snd measurableSet_Icc.compl]
    exact measure_mono (fun p hp hmem ↦ hp hmem.1.2)
  exact ⟨h0.trans_lt hloss, h1.trans_lt hloss⟩

/-- Disintegration on the same original root core turns the conditional tail
screen into a physical target mass estimate. -/
theorem original_target_scalar_tail_on_piece_le
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : Measurable u) (ha : Measurable a)
    (i : Fin D.haar.continuous.count)
    (hlegal : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∃ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a η₀ z)
        (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2) :
    let C := D.haar.continuous.coefficient i
    η₁ ((a ⁻¹' C.roots) ∩ u ⁻¹' (Icc (C.window.val.1 : ℝ) C.window.val.2.1)ᶜ) ≤
      δ * lambda C.roots := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let I := Icc (C.window.val.1 : ℝ) C.window.val.2.1
  have hI : MeasurableSet I := measurableSet_Icc
  have hroots : MeasurableSet C.roots := D.haar.continuous.recovery.measurable i
  have he := congrArg (fun σ : Measure ((ℚ → M) × ℝ) ↦ σ (univ ×ˢ Iᶜ))
    (D.haar.continuous.recovery.target_joint i)
  rw [Measure.map_apply (ha.prodMk hu) (MeasurableSet.univ.prod hI.compl),
    Measure.compProd_apply_prod MeasurableSet.univ hI.compl,
    Measure.restrict_univ] at he
  have hpre : (fun x : M ↦ (a x, u x)) ⁻¹' (univ ×ˢ Iᶜ) = u ⁻¹' Iᶜ := by
    ext x
    simp
  rw [hpre, Measure.restrict_apply (hI.compl.preimage hu), inter_comm] at he
  calc
    _ = ∫⁻ z, (condDistrib u a η₁ z) Iᶜ ∂lambda.restrict C.roots := he
    _ ≤ ∫⁻ _z, δ ∂lambda.restrict C.roots := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hroots] with z hz
      exact (D.conditional_scalar_interval_tails_lt i hz (hlegal z hz)).2.le
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- Both the discarded roots and the actual scalar interval tails are paid by
the original population mass. No global plan is assumed to stay in these cores. -/
theorem original_target_outside_physical_cores_le
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : Measurable u) (ha : Measurable a)
    (hreg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (hlegal : ∀ i : Fin D.haar.continuous.count,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∃ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a η₀ z)
        (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2) :
    η₁ (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ * lambda univ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let roots := D.haar.continuous.population.roots
  let bad := fun i : Fin D.haar.continuous.count ↦
    (a ⁻¹' (D.haar.continuous.coefficient i).roots) ∩
      u ⁻¹' (Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1)ᶜ
  have hsub : ∀ᵐ x ∂η₁, x ∈ (⋃ i, D.physicalCoreDomain i)ᶜ →
      x ∈ (a ⁻¹' rootsᶜ) ∪ ⋃ i, bad i := by
    filter_upwards [hreg] with x hx hn
    by_cases hr : a x ∈ roots
    · right
      have hr' : a x ∈ ⋃ i, (D.haar.continuous.coefficient i).roots := by
        rw [D.haar.continuous.union_eq]
        exact hr
      obtain ⟨i, hi⟩ := mem_iUnion.mp hr'
      apply mem_iUnion.mpr
      refine ⟨i, hi, ?_⟩
      intro ht
      apply hn
      exact mem_iUnion.mpr ⟨i, hx, hi, ht⟩
    · exact Or.inl hr
  have hb : η₁ (⋃ i, bad i) ≤ ∑ i, η₁ (bad i) := by
    simpa only [tsum_fintype] using measure_iUnion_le bad
  have hdec := congrArg (fun σ : Measure (ℚ → M) ↦ σ univ)
    D.haar.continuous.recovery.label_decomposition
  simp only [Measure.add_apply, Measure.finsetSum_apply, Measure.restrict_apply_univ] at hdec
  have hmass : (∑ i, lambda (D.haar.continuous.coefficient i).roots) ≤ lambda univ :=
    (le_self_add).trans hdec.le
  have hsum : (∑ i, η₁ (bad i)) ≤ δ * lambda univ := by
    calc
      _ ≤ ∑ i, δ * lambda (D.haar.continuous.coefficient i).roots :=
        Finset.sum_le_sum fun i _ ↦
          D.original_target_scalar_tail_on_piece_le hcomplete hu ha i (hlegal i)
      _ = δ * ∑ i, lambda (D.haar.continuous.coefficient i).roots :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_left hmass δ
  calc
    _ ≤ η₁ ((a ⁻¹' rootsᶜ) ∪ ⋃ i, bad i) := measure_mono_ae hsub
    _ ≤ η₁ (a ⁻¹' rootsᶜ) + η₁ (⋃ i, bad i) := measure_union_le _ _
    _ ≤ loss + δ * lambda univ :=
      add_le_add D.haar.continuous.population.remainder_mass.2.2.2.le (hb.trans hsum)

/-- The original target-times-Dirichlet global allocation pays for all endpoints
outside the full retained physical cores, including scalar interval tails. -/
theorem rooted_original_outside_physical_cores_expected_le
    [IsProbabilityMeasure η₁]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hreg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (hlegal : ∀ i : Fin D.haar.continuous.count,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∃ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a η₀ z)
        (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2)
    (n : ℕ)
    (A : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ η₁)).prod (dirichletOne n)),
      IsSemidiscreteAllocation η₀ z.2 (A z))
    {ι : Type*} [Fintype ι]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (N : ℝ) (hN : 0 < N)
    (rootDomain U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (H : Set M) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily η₀ A (fun z ↦ z.1) w).restrict
        ((univ ×ˢ (⋃ i, D.physicalCoreDomain i)ᶜ) ∩ (H ×ˢ univ))) coord u N z
      {e | e.1.1 ∈ U} ∂cavityRootMeasure volume rootDomain N
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ η₁)).prod (dirichletOne n))) ≤
      volume U * (loss + δ * lambda univ) := by
  let _inst : MetricSpace M := F.metricSpace
  have hK : MeasurableSet (⋃ i, D.physicalCoreDomain i)ᶜ :=
    (MeasurableSet.iUnion fun i ↦ D.measurableSet_physicalCoreDomain hF hcomplete hu ha i).compl
  exact (lintegral_physicalSceneGlobalAllocationFamily_rooted_discarded_target_le
    η₀ η₁ n A hfeas coord hcoord u hu.continuous.measurable N hN rootDomain U hU hUf H hK).trans
      (mul_le_mul_right
        (D.original_target_outside_physical_cores_le hcomplete hu.continuous.measurable ha hreg hlegal) _)

end PopulationLocalPressureCore
/-- The original local-core law retains the actual conditional forward-coupling
property while constructing a core whose complete physical target complement
has the stated small mass. -/
theorem exists_original_core_small_physical_target_tail
    (hcore : PopulationLocalPressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b r)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : Measurable u) (ha : Measurable a)
    (hreg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (hlegal : ∀ᵐ z ∂lambda, ∃ π : Measure (ℝ × ℝ),
      Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
        ∀ᵐ p ∂π, p.1 ≤ p.2)
    {δ loss : ℝ≥0∞} (hδ : δ ≠ 0) (hloss : loss ≠ 0) :
    ∃ D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (fun z ↦ ∃ π : Measure (ℝ × ℝ),
        Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧
          ∀ᵐ p ∂π, p.1 ≤ p.2) r δ loss,
      η₁ (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ * lambda univ := by
  obtain ⟨D⟩ := hcore _ hlegal δ hδ loss hloss
  refine ⟨D, D.original_target_outside_physical_cores_le hcomplete hu ha hreg ?_⟩
  intro i z hz
  have hroot : z ∈ D.haar.continuous.population.roots := by
    rw [← D.haar.continuous.union_eq]
    exact mem_iUnion.mpr ⟨i, hz⟩
  exact (D.haar.continuous.population.good z hroot).1

end OTSelector.Reconstruction
