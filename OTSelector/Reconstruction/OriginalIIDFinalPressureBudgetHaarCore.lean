import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetCore

/-! The literal stored original Haar cores recover whole-root candidate and signed budgets. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : ℕ → (ℚ → M) → Prop} {r : ℕ → ℝ} {δ loss : ℕ → ℝ≥0∞}

/-- Finite same-law candidate values on the actual original Haar cores give a whole-root
nonnegative pressure budget. The omitted mass comes from the cores' stored loss; no
global pressure integrability, cover, coordinate sum or pressure budget is assumed. -/
theorem original_haar_core_pressure_budget_of_candidates
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (D : ∀ n, PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (Good n) (r n) (δ n) (loss n)) (hloss : Tendsto loss atTop (𝓝 0))
    (p : (ℚ → M) → ℝ) (hp : AEStronglyMeasurable p lambda)
    (hnonneg : ∀ᵐ z ∂lambda, 0 ≤ p z)
    (candidate : (n : ℕ) → Fin (D n).continuous.count → (ℚ → M) → ℝ)
    (hInt : ∀ n i, Integrable (candidate n i)
      (lambda.restrict ((D n).continuous.coefficient i).roots))
    (hcompare : ∀ n i, ∀ᵐ z ∂lambda.restrict ((D n).continuous.coefficient i).roots,
      p z ≤ candidate n i z)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hcost : ∀ n, (∑ i, ∫ z in ((D n).continuous.coefficient i).roots,
      candidate n i z ∂lambda) ≤ C.toReal) :
    Integrable p lambda ∧ (∫ z, p z ∂lambda) ≤ C.toReal := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  have hn (n) (i : Fin (D n).continuous.count) :
      ∀ᵐ z ∂lambda.restrict ((D n).continuous.coefficient i).roots, 0 ≤ p z :=
    ae_restrict_of_ae hnonneg
  have hi (n) (i : Fin (D n).continuous.count) :
      Integrable p (lambda.restrict ((D n).continuous.coefficient i).roots) := by
    apply (hInt n i).mono' hp.restrict
    filter_upwards [hn n i, hcompare n i] with z hz hc
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hc
  apply integrable_nonneg_of_finite_root_core_losses lambda p hp hnonneg
    (fun n ↦ Fin (D n).continuous.count)
    (fun n i ↦ ((D n).continuous.coefficient i).roots)
    (fun n i ↦ ((D n).continuous.coefficient i).roots_compact.measurableSet)
    (fun n ↦ (D n).continuous.disjoint)
    (populationHaarPressureCore_root_complement_tendsto_zero D hloss)
    C hC (fun _ ↦ 0) tendsto_const_nhds
  apply Eventually.of_forall
  intro n
  simp only [add_zero]
  calc
    _ = ENNReal.ofReal (∑ i, ∫ z in ((D n).continuous.coefficient i).roots, p z ∂lambda) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ integral_nonneg_of_ae (hn n i))]
      exact Finset.sum_congr rfl (fun i _ ↦ (ofReal_integral_eq_lintegral_ofReal (hi n i) (hn n i)).symm)
    _ ≤ ENNReal.ofReal (∑ i, ∫ z in ((D n).continuous.coefficient i).roots, candidate n i z ∂lambda) :=
      ENNReal.ofReal_le_ofReal (Finset.sum_le_sum (fun i _ ↦ integral_mono_ae (hi n i) (hInt n i) (hcompare n i)))
    _ ≤ ENNReal.ofReal C.toReal := ENNReal.ofReal_le_ofReal (hcost n)
    _ = C := ENNReal.ofReal_toReal hC

/-- The actual stored Haar-core refinements recover the full integral of every
integrable signed root field, including varying seed indices and coefficient counts. -/
theorem tendsto_original_haar_core_signed_integrals
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (D : ∀ n, PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b
      (Good n) (r n) (δ n) (loss n)) (hloss : Tendsto loss atTop (𝓝 0))
    (p : (ℚ → M) → ℝ) (hp : Integrable p lambda) :
    Tendsto (fun n ↦ ∑ i, ∫ z in ((D n).continuous.coefficient i).roots, p z ∂lambda)
      atTop (𝓝 (∫ z, p z ∂lambda)) := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  exact tendsto_finite_root_core_integrals lambda p hp
    (fun n ↦ Fin (D n).continuous.count)
    (fun n i ↦ ((D n).continuous.coefficient i).roots)
    (fun n i ↦ ((D n).continuous.coefficient i).roots_compact.measurableSet)
    (fun n ↦ (D n).continuous.disjoint)
    (populationHaarPressureCore_root_complement_tendsto_zero D hloss)

end OTSelector.Reconstruction
