import OTSelector.Finite.CommonSampleMatchingCore
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyShifted
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyAbsorption
import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair

/-!
# Explicit relative kinetic absorption for adaptive orphan repair

The true finite-cutoff repair budget has a relative quadratic-energy term and
an explicit retained-count remainder. The cutoff coefficient remains visible;
these estimates do not claim that the coarse-scale remainder vanishes.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual shifted-grid repair budget admits any prescribed positive
quadratic-energy coefficient, with the complete cutoff-dependent remainder. -/
theorem integral_shifted_adaptiveOrphanRepairBudget_le_relative_energy
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    {K N q : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    [∀ k, MeasurableSpace (C k)] [∀ k, MeasurableSingletonClass (C k)]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Θ) [IsProbabilityMeasure Q]
    (μ : Measure (Fin q → ℝ)) [IsProbabilityMeasure μ]
    (σ : Ω → OTSelector.PartialMatching N N)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k)
    (phase : Fin K → Θ → Fin q → ℝ) (hp : ∀ k, Measurable (phase k))
    (hlaw : ∀ k, Q.map (phase k) = shiftedGridPhaseLaw q (ell k))
    (readout : (k : Fin K) → (Fin q → ℤ) → C k) (hr : ∀ k, Measurable (readout k))
    (base : ℝ) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hdisp : Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P)
    (henergy : Integrable (fun ω ↦ retainedSquaredDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun p : Ω × Θ ↦ adaptiveOrphanRepairBudget (σ p.1)
      (shiftedHierarchyCell ell phase readout p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight) (P.prod Q) ∧
    (∫ p : Ω × Θ, adaptiveOrphanRepairBudget (σ p.1)
      (shiftedHierarchyCell ell phase readout p.2)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) base weight ∂(P.prod Q)) ≤
      (∫ ω, (N : ℝ) - (σ ω).card ∂P) * base +
        (1 / 2 : ℝ) * ∑ k, weight k * Real.sqrt (2 * (N : ℝ) * Fintype.card (C k)) +
        ρ * (∫ ω, retainedSquaredDisplacement (σ ω)
          (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) +
        (∫ ω, ((σ ω).card : ℝ) ∂P) * q * (∑ k, weight k / ell k) ^ 2 / (4 * ρ) := by
  have h := integral_shifted_adaptiveOrphanRepairBudget_le P Q μ σ hσ xs ys hx hy
    hxi hyi hxl hyl hxy ell hell phase hp hlaw readout hr base weight hw hdisp
  have hcard : Integrable (fun ω ↦ ((σ ω).card : ℝ)) P := by
    apply Integrable.of_bound (measurable_retained_card σ hσ).aestronglyMeasurable N
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast ((σ ω).card_le.trans (min_le_left N N))
  have hb := integral_retainedCoordinateDisplacement_mul_le_energy P σ xs ys
    hdisp henergy hcard (∑ k, weight k / ell k) hρ
  refine ⟨h.1, ?_⟩
  nlinarith [h.2]

/-- The retained common core's quadratic energy is bounded by the original
model optimizer's actual quadratic energy, since every retained coordinate
agrees and all discarded kinetic terms are nonnegative. -/
theorem retainedSquaredDisplacement_commonSampleMatching_le
    {S T : Type*} {m n q : ℕ} (σ : OTSelector.PartialMatching m n)
    (sa sb : Fin m → S) (ta tb : Fin n → T)
    (scoord : S → Fin q → ℝ) (tcoord : T → Fin q → ℝ) :
    retainedSquaredDisplacement (commonSampleMatching σ sa sb ta tb)
      (scoord ∘ sa) (tcoord ∘ ta) ≤
      retainedSquaredDisplacement σ (scoord ∘ sb) (tcoord ∘ tb) := by
  classical
  have hsub := OTSelector.PartialMatching.commonSampleCore_subset σ sa sb ta tb
  unfold retainedSquaredDisplacement
  change (∑ e ∈ OTSelector.PartialMatching.commonSampleCore σ sa sb ta tb,
    ∑ i, (scoord (sa e.1) i - tcoord (ta e.2) i) ^ 2) ≤ _
  calc
    _ = ∑ e ∈ OTSelector.PartialMatching.commonSampleCore σ sa sb ta tb,
        ∑ i, (scoord (sb e.1) i - tcoord (tb e.2) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro e he
      have heq := (Finset.mem_filter.mp he).2
      simp only [heq.1, heq.2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e he he' ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _)

end OTSelector.Reconstruction
