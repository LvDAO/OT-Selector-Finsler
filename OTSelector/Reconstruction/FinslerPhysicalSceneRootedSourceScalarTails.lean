import OTSelector.Reconstruction.FinslerPhysicalSceneRootedScalarTails
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedConditionalClock

/-!
# Both original physical populations outside one retained core

Exact original source disintegration gives the companion scalar tail estimate.
The same original optimal face constructs one actual local core with both
physical population complements bounded by the prescribed original losses.
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

/-- Disintegration on the same original root core turns the conditional tail
screen into a physical source mass estimate. -/
theorem original_source_scalar_tail_on_piece_le
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : Measurable u) (ha : Measurable a)
    (i : Fin D.haar.continuous.count)
    (hlegal : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∃ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a η₀ z)
        (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2) :
    let C := D.haar.continuous.coefficient i
    η₀ ((a ⁻¹' C.roots) ∩ u ⁻¹' (Icc (C.window.val.1 : ℝ) C.window.val.2.1)ᶜ) ≤
      δ * lambda C.roots := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let I := Icc (C.window.val.1 : ℝ) C.window.val.2.1
  have hI : MeasurableSet I := measurableSet_Icc
  have hroots : MeasurableSet C.roots := D.haar.continuous.recovery.measurable i
  have he := congrArg (fun σ : Measure ((ℚ → M) × ℝ) ↦ σ (univ ×ˢ Iᶜ))
    (D.haar.continuous.recovery.source_joint i)
  rw [Measure.map_apply (ha.prodMk hu) (MeasurableSet.univ.prod hI.compl),
    Measure.compProd_apply_prod MeasurableSet.univ hI.compl,
    Measure.restrict_univ] at he
  have hpre : (fun x : M ↦ (a x, u x)) ⁻¹' (univ ×ˢ Iᶜ) = u ⁻¹' Iᶜ := by
    ext x
    simp
  rw [hpre, Measure.restrict_apply (hI.compl.preimage hu), inter_comm] at he
  calc
    _ = ∫⁻ z, (condDistrib u a η₀ z) Iᶜ ∂lambda.restrict C.roots := he
    _ ≤ ∫⁻ _z, δ ∂lambda.restrict C.roots := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hroots] with z hz
      exact (D.conditional_scalar_interval_tails_lt i hz (hlegal z hz)).1.le
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- Both the discarded roots and the actual scalar interval tails are paid by
the original population mass. No global plan is assumed to stay in these cores. -/
theorem original_source_outside_physical_cores_le
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : Measurable u) (ha : Measurable a)
    (hreg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hlegal : ∀ i : Fin D.haar.continuous.count,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∃ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a η₀ z)
        (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂π, p.1 ≤ p.2) :
    η₀ (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ * lambda univ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let roots := D.haar.continuous.population.roots
  let bad := fun i : Fin D.haar.continuous.count ↦
    (a ⁻¹' (D.haar.continuous.coefficient i).roots) ∩
      u ⁻¹' (Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1)ᶜ
  have hsub : ∀ᵐ x ∂η₀, x ∈ (⋃ i, D.physicalCoreDomain i)ᶜ →
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
  have hb : η₀ (⋃ i, bad i) ≤ ∑ i, η₀ (bad i) := by
    simpa only [tsum_fintype] using measure_iUnion_le bad
  have hdec := congrArg (fun σ : Measure (ℚ → M) ↦ σ univ)
    D.haar.continuous.recovery.label_decomposition
  simp only [Measure.add_apply, Measure.finsetSum_apply, Measure.restrict_apply_univ] at hdec
  have hmass : (∑ i, lambda (D.haar.continuous.coefficient i).roots) ≤ lambda univ :=
    (le_self_add).trans hdec.le
  have hsum : (∑ i, η₀ (bad i)) ≤ δ * lambda univ := by
    calc
      _ ≤ ∑ i, δ * lambda (D.haar.continuous.coefficient i).roots :=
        Finset.sum_le_sum fun i _ ↦
          D.original_source_scalar_tail_on_piece_le hcomplete hu ha i (hlegal i)
      _ = δ * ∑ i, lambda (D.haar.continuous.coefficient i).roots :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_left hmass δ
  calc
    _ ≤ η₀ ((a ⁻¹' rootsᶜ) ∪ ⋃ i, bad i) := measure_mono_ae hsub
    _ ≤ η₀ (a ⁻¹' rootsᶜ) + η₀ (⋃ i, bad i) := measure_union_le _ _
    _ ≤ loss + δ * lambda univ :=
      add_le_add D.haar.continuous.population.remainder_mass.2.2.1.le (hb.trans hsum)


end PopulationLocalPressureCore
end OTSelector.Reconstruction

namespace OTSelector.Reconstruction
section OriginalCore
open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- One original core retains both populations, with conditional forward clock
couplings constructed internally from the same original optimal face. -/
theorem exists_original_core_small_physical_population_tails_of_face
    (hcore : PopulationLocalPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
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
    {δ loss : ℝ≥0∞} (hδ : δ ≠ 0) (hloss : loss ≠ 0) :
    ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (fun z ↦ ∃ π : Measure (ℝ × ℝ),
        Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
          ∀ᵐ p ∂π, p.1 ≤ p.2) r δ loss,
      μ (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ ∧
      ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤ loss + δ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨D, htarget⟩ := exists_original_core_small_physical_target_tail_of_face hcore hcomplete
    hu ha hbalance hA hB hμ hν hreg hface hδ hloss
  have hsource := D.original_source_outside_physical_cores_le hcomplete hu.continuous.measurable
    ha hμreg (fun i z hz ↦ ?_)
  · refine ⟨D, ?_, htarget⟩
    simpa only [Measure.map_apply ha MeasurableSet.univ, preimage_univ, measure_univ, mul_one] using hsource
  · have hroot : z ∈ D.haar.continuous.population.roots := by
      rw [← D.haar.continuous.union_eq]
      exact mem_iUnion.mpr ⟨i, hz⟩
    exact (D.haar.continuous.population.good z hroot).1

end OriginalCore

end OTSelector.Reconstruction
