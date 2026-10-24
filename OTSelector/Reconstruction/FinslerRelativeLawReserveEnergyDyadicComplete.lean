import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyDyadicBudget
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyOptimalCounts

/-!
# Actual adaptive repair on original bounded observations

The original observation law supplies the carrier and moment bounds. An
independent actual phase constructs full quadratic repairs of every selected
core almost surely. The concrete expected budget uses the original iid law,
and no distribution is assigned to unmatched endpoints.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Finite edge sums of an adaptively selected matching are measurable on the
original observation space. -/
theorem measurable_retained_edge_sum
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (σ : Ω → OTSelector.PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (f : Ω → Fin m × Fin n → ℝ) (hf : ∀ e, Measurable (fun ω ↦ f ω e)) :
    Measurable (fun ω ↦ ∑ e ∈ (σ ω).edges, f ω e) := by
  classical
  have heq : (fun ω ↦ ∑ e ∈ (σ ω).edges, f ω e) = fun ω ↦
      ∑ e : Fin m × Fin n, if e ∈ (σ ω).edges then f ω e else 0 := by
    funext ω
    have hfilter : (Finset.univ.filter fun e : Fin m × Fin n ↦ e ∈ (σ ω).edges) =
        (σ ω).edges := by ext e; simp
    rw [← Finset.sum_filter, hfilter]
  rw [heq]
  exact Finset.measurable_sum _ fun e _ ↦ Measurable.ite (hσ e) (hf e) measurable_const

/-- Original cube carriers give integrability of actual retained displacement,
for every measurable adaptive core. -/
theorem integrable_retainedCoordinateDisplacement_of_cube
    {Ω : Type*} [MeasurableSpace Ω] {N q : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (σ : Ω → OTSelector.PartialMatching N N)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hX : ∀ᵐ ω ∂P, ∀ i k, 0 ≤ xs i ω k ∧ xs i ω k ≤ 1)
    (hY : ∀ᵐ ω ∂P, ∀ j k, 0 ≤ ys j ω k ∧ ys j ω k ≤ 1) :
    Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P := by
  have hm := measurable_retained_edge_sum σ hσ
    (fun ω e ↦ ∑ k, |xs e.1 ω k - ys e.2 ω k|) (fun e ↦
      Finset.measurable_sum _ fun k _ ↦ by
        simpa only [Function.comp_def, Pi.sub_apply, Real.norm_eq_abs] using
          measurable_norm.comp (((measurable_pi_apply k).comp (hx e.1)).sub
            ((measurable_pi_apply k).comp (hy e.2))))
  apply Integrable.of_bound hm.aestronglyMeasurable ((N : ℝ) * q)
  filter_upwards [hX, hY] with ω hxs hys
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun e _ ↦
    Finset.sum_nonneg fun k _ ↦ abs_nonneg _)]
  calc
    _ ≤ ∑ _e ∈ (σ ω).edges, (q : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      calc
        _ ≤ ∑ _k : Fin q, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_le]
          constructor <;> linarith [(hxs e.1 k).1, (hxs e.1 k).2,
            (hys e.2 k).1, (hys e.2 k).2]
        _ = _ := by simp
    _ = ((σ ω).card : ℝ) * q := by simp [OTSelector.PartialMatching.card]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (σ ω).card_le.trans (min_le_left N N))
      (Nat.cast_nonneg q)

/-- Every original point stays in the population cube carrier, before any
adaptive selection of the core or its unmatched partners. -/
theorem ae_original_arrays_mem_cube
    {Ω : Type*} [MeasurableSpace Ω] {N q : ℕ} (P : Measure Ω)
    (μ : Measure (Fin q → ℝ))
    (hμ : ∀ᵐ x ∂μ, ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (xs : Fin N → Ω → Fin q → ℝ) (hx : ∀ i, Measurable (xs i))
    (hxl : ∀ i, P.map (xs i) = μ) :
    ∀ᵐ ω ∂P, ∀ i k, 0 ≤ xs i ω k ∧ xs i ω k ≤ 1 :=
  ae_all_iff.mpr fun i ↦
    (show MeasurePreserving (xs i) P μ from ⟨hx i, hxl i⟩).quasiMeasurePreserving.tendsto_ae.eventually hμ

/-- The concrete dyadic budget bounds actual quadratic full completions almost
surely on the original observations and an independent actual common phase. -/
theorem ae_exists_completion_le_dyadicOrphanRepairBudget
    {Ω : Type*} [MeasurableSpace Ω] {N q : ℕ} (K : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : Ω → OTSelector.PartialMatching N N)
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hX : ∀ᵐ ω ∂P, ∀ i k, 0 ≤ xs i ω k ∧ xs i ω k ≤ 1)
    (hY : ∀ᵐ ω ∂P, ∀ j k, 0 ≤ ys j ω k ∧ ys j ω k ≤ 1)
    (allowed : Ω → Finset (Fin N × Fin N)) :
    ∀ᵐ p : Ω × (Fin q → ℝ) ∂P.prod (shiftedGridPhaseLaw q 1),
      ∃ τ : OTSelector.PartialMatching N N,
        τ.card = N ∧ (σ p.1).edges ⊆ τ.edges ∧
        (∑ e ∈ τ.edges \ (σ p.1).edges, ∑ k, (xs e.1 p.1 k - ys e.2 p.1 k) ^ 2) ≤
          dyadicOrphanRepairBudget K (σ p.1) (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) p.2 ∧
        ((τ.edges \ (σ p.1).edges).filter fun e ↦ e ∉ allowed p.1).card ≤ N - (σ p.1).card := by
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q 1) := shiftedGridPhaseLaw_probability q (by norm_num)
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hX,
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hY,
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually (ae_shiftedGridPhaseLaw_one_mem (q := q))]
    with p hxs hys hu
  exact exists_completion_le_dyadicOrphanRepairBudget K (σ p.1)
    (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) p.2 hu hxs hys (allowed p.1)

/-- Original cube-supported iid laws produce the full explicit expected
repair budget, including all moment conditions, for every measurable core. -/
theorem integral_dyadicOrphanRepairBudget_le_of_original_cube
    {Ω : Type*} [MeasurableSpace Ω] {N q : ℕ} (K : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin q → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (σ : Ω → OTSelector.PartialMatching N N)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P) :
    Integrable (fun p : Ω × (Fin q → ℝ) ↦ dyadicOrphanRepairBudget K (σ p.1)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) p.2) (P.prod (shiftedGridPhaseLaw q 1)) ∧
    (∫ p : Ω × (Fin q → ℝ), dyadicOrphanRepairBudget K (σ p.1)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) p.2 ∂(P.prod (shiftedGridPhaseLaw q 1))) ≤
      (∫ ω, (N : ℝ) - (σ ω).card ∂P) * ((4 * q : ℝ) * (1 / 4 : ℝ) ^ K) +
      (1 / 2 : ℝ) * ∑ k : Fin K, ((8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ)) *
        Real.sqrt (2 * (N : ℝ) * ((2 ^ ((k : ℕ) + 1)) ^ q : ℕ)) +
      (∫ ω, retainedCoordinateDisplacement (σ ω)
        (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) *
        ∑ k : Fin K, ((8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ)) / ((2 : ℝ) ^ (k : ℕ))⁻¹ := by
  have hX := ae_original_arrays_mem_cube P μ hμ xs hx hxl
  have hY := ae_original_arrays_mem_cube P μ hμ ys hy hyl
  have hdisp := integrable_retainedCoordinateDisplacement_of_cube P σ hσ xs ys hx hy hX hY
  exact integral_dyadicOrphanRepairBudget_le K P μ σ hσ xs ys hx hy hxi hyi hxl hyl hxy hdisp

end OTSelector.Reconstruction
