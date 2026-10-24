import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutPopulation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMarginals
import OTSelector.Probability.DirichletReferenceMoments

/-!
# Exact original mean marginals and discarded-target root intensity

The same globally feasible original allocation retains the source population
exactly. Averaging its target marginal in the original target-times-Dirichlet
experiment gives the original target population. This controls actual rooted
mass aimed at discarded target sets while preserving realized restricted columns.
-/

open MeasureTheory Set Filter OTSelector.Probability
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

theorem lintegral_physicalSceneOriginalDirichlet_weight (n : ℕ) (j : Fin (n + 1)) :
    (∫⁻ p, ENNReal.ofReal (p j) ∂dirichletOne n) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  classical
  have h := lintegral_dirichletOne_nat_powers n (fun k ↦ if k = j then 1 else 0)
  have hp (p : Fin (n + 1) → ℝ) :
      (∏ k, ENNReal.ofReal (p k) ^ (if k = j then 1 else 0)) = ENNReal.ofReal (p j) := by
    simp
  simp_rw [hp] at h
  have heq : ((n.factorial : ℝ) *
      (∏ k : Fin (n + 1), (if k = j then 1 else 0).factorial : ℝ) /
        (n + ∑ k : Fin (n + 1), (if k = j then 1 else 0)).factorial) = 1 / ((n : ℝ) + 1) := by
    have hprod : (∏ k : Fin (n + 1), ((if k = j then 1 else 0).factorial : ℝ)) = 1 := by
      apply Finset.prod_eq_one
      intro k _
      split_ifs <;> norm_num
    have hsum : (∑ k : Fin (n + 1), (if k = j then 1 else 0)) = 1 := by simp
    rw [hprod, hsum, Nat.factorial_succ]
    push_cast
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  rw [heq] at h
  exact h

variable {M : Type*} [MeasurableSpace M]

/-- The original product experiment has the exact target intensity against any
nonnegative test. This is an environment identity, with the original weights. -/
theorem lintegral_physicalSceneOriginalDirichlet_weighted_targets
    (ν : Measure M) [IsProbabilityMeasure ν] (n : ℕ)
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ),
      ∑ j, f (z.1 j) * ENNReal.ofReal (z.2 j)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) = ∫⁻ y, f y ∂ν := by
  classical
  have hmeas (j : Fin (n + 1)) : Measurable
      (fun z : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ) ↦
        f (z.1 j) * ENNReal.ofReal (z.2 j)) :=
    (hf.comp ((measurable_pi_apply j).comp measurable_fst)).mul
      (((measurable_pi_apply j).comp measurable_snd).ennreal_ofReal)
  rw [lintegral_finsetSum Finset.univ (fun j _ ↦ hmeas j)]
  have hterm (j : Fin (n + 1)) :
      (∫⁻ z : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ),
        f (z.1 j) * ENNReal.ofReal (z.2 j)
          ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) =
        (∫⁻ y, f y ∂ν) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [lintegral_prod_mul
      (f := fun Y : Fin (n + 1) → M ↦ f (Y j))
      (g := fun p : Fin (n + 1) → ℝ ↦ ENNReal.ofReal (p j))
      (hf.comp (measurable_pi_apply j)).aemeasurable
      ((measurable_pi_apply j).ennreal_ofReal).aemeasurable,
      lintegral_physicalSceneOriginalDirichlet_weight]
    congr 1
    exact (measurePreserving_eval (μ := fun _ : Fin (n + 1) ↦ ν) j).lintegral_comp hf
  simp_rw [hterm]
  have hcoeff : ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    have hr : ((n + 1 : ℕ) : ℝ) * (1 / ((n : ℝ) + 1)) = 1 := by push_cast; field_simp
    rw [hr, ENNReal.ofReal_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = (∫⁻ y, f y ∂ν) * (((n + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / ((n : ℝ) + 1))) := by ac_rfl
    _ = _ := by rw [hcoeff, mul_one]

/-- Averaging the same original globally feasible allocation recovers exactly the
original target population. No local columns or plan-level iid law is asserted. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_target_eq_population
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (a z))
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, ∫⁻ e, f e.2
      ∂physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) = ∫⁻ y, f y ∂ν := by
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  have heq : (∫⁻ z, ∫⁻ e, f e.2
      ∂physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) z ∂P) =
      ∫⁻ z : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ),
        ∑ j, f (z.1 j) * ENNReal.ofReal (z.2 j) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ a
      (fun z ↦ z.1) (fun z ↦ z.2) hfeas, hfeas] with z he hz
    rw [he]
    rw [← lintegral_map hf measurable_snd]
    change (∫⁻ y, f y ∂(physicalSceneAllocationPlan μ (a z) z.1).snd) = _
    rw [physicalSceneAllocationPlan_snd hz z.1,
      lintegral_map hf (measurable_of_finite z.1)]
    simp [semidiscreteLabelMeasure, lintegral_finsetSum_measure, lintegral_smul_measure,
      lintegral_dirac, smul_eq_mul, mul_comm]
  exact heq.trans (lintegral_physicalSceneOriginalDirichlet_weighted_targets ν n f hf)

/-- Every globally feasible physical allocation has the unchanged original
source marginal even before averaging its original environment. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_source_eq_population
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (a z))
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, ∫⁻ e, f e.1
      ∂physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) = ∫⁻ x, f x ∂μ := by
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  have heq : (∫⁻ z, ∫⁻ e, f e.1
      ∂physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) z ∂P) = ∫⁻ _z, ∫⁻ x, f x ∂μ ∂P := by
    apply lintegral_congr_ae
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ a
      (fun z ↦ z.1) (fun z ↦ z.2) hfeas, hfeas] with z he hz
    rw [he, ← lintegral_map hf measurable_fst]
    change (∫⁻ x, f x ∂(physicalSceneAllocationPlan μ (a z) z.1).fst) = _
    rw [physicalSceneAllocationPlan_fst hz z.1]
  simpa only [lintegral_const, measure_univ, mul_one] using heq

/-- Discarded target sets are paid by exactly their original population mass
in the unchanged global target-times-Dirichlet experiment. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_targetSet_eq
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (a z))
    {K : Set M} (hK : MeasurableSet K) :
    (∫⁻ z, physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) z (univ ×ˢ K)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) = ν K := by
  have h := lintegral_physicalSceneGlobalAllocationFamily_target_eq_population μ ν n a hfeas
    (K.indicator (fun _ ↦ 1)) (measurable_const.indicator hK)
  have hpoint (Γ : Measure (M × M)) :
      (∫⁻ e, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) e.2 ∂Γ) = Γ (univ ×ˢ K) := by
    calc
      _ = ∫⁻ e, (univ ×ˢ K).indicator (fun _ ↦ (1 : ℝ≥0∞)) e ∂Γ := by
        apply lintegral_congr
        intro e
        by_cases he : e.2 ∈ K <;> simp [he]
      _ = _ := lintegral_indicator_one (MeasurableSet.univ.prod hK)
  calc
    _ = ∫⁻ z, ∫⁻ e, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) e.2
        ∂physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) := by
      apply lintegral_congr
      intro z
      exact (hpoint _).symm
    _ = _ := h
    _ = _ := lintegral_indicator_one hK

/-- Haar-rooted source-window mass aimed at a discarded original target set is
bounded by window volume times that original target mass, even after retaining
an arbitrary actual source cell. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_rooted_discarded_target_le
    {ι : Type*} [Fintype ι]
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (a : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (a z))
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (H : Set M) {K : Set M} (hK : MeasurableSet K) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
      ((physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1) w).restrict
        ((univ ×ˢ K) ∩ (H ×ˢ univ))) coord u N z {e | e.1.1 ∈ U}
      ∂cavityRootMeasure volume D N
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ volume U * ν K := by
  let Γ := physicalSceneGlobalAllocationFamily μ a (fun z ↦ z.1)
  calc
    _ ≤ ∫⁻ w, volume U * Γ w (univ ×ˢ K)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) := by
      apply lintegral_mono
      intro w
      apply (lintegral_physicalSceneRootedPlan_sourceWindow_le
        ((Γ w).restrict ((univ ×ˢ K) ∩ (H ×ˢ univ)))
        coord hcoord u hu N hN D U hU).trans
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul_right (measure_mono inter_subset_left) _
    _ = volume U * ∫⁻ w, Γ w (univ ×ˢ K)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) :=
      lintegral_const_mul' _ _ hUf
    _ = _ := by
      rw [lintegral_physicalSceneGlobalAllocationFamily_targetSet_eq μ ν n a hfeas hK]

end OTSelector.Reconstruction
