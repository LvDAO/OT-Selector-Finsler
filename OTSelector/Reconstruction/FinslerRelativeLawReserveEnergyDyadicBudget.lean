import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyDyadic
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyPhase

/-!
# A concrete expected quadratic repair budget under the original law

An actual common phase determines one nested finite dyadic hierarchy. The
budget constructs a full extension of every adaptive retained core and its
expectation is estimated using the original iid law. The coarse flux term is
explicit and is not asserted to vanish.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Concrete finite-cutoff quadratic repair budget for the actual translated
dyadic hierarchy. -/
def dyadicOrphanRepairBudget {N q : ℕ} (K : ℕ) (σ : OTSelector.PartialMatching N N)
    (x y : Fin N → Fin q → ℝ) (u : Fin q → ℝ) : ℝ :=
  adaptiveOrphanRepairBudget σ (fun k : Fin K ↦ shiftedDyadicRepairCell q k u)
    x y ((4 * q : ℝ) * (1 / 4 : ℝ) ^ K)
    (fun k ↦ (8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ))

/-- The concrete budget constructs an actual full extension. Possible illegal
added edges are reported separately for any supplied legal graph. -/
theorem exists_completion_le_dyadicOrphanRepairBudget
    {N q : ℕ} (K : ℕ) (σ : OTSelector.PartialMatching N N)
    (x y : Fin N → Fin q → ℝ) (u : Fin q → ℝ)
    (hu : ∀ i, 0 < u i ∧ u i ≤ 1)
    (hx : ∀ i k, 0 ≤ x i k ∧ x i k ≤ 1)
    (hy : ∀ j k, 0 ≤ y j k ∧ y j k ≤ 1)
    (allowed : Finset (Fin N × Fin N)) :
    ∃ τ : OTSelector.PartialMatching N N,
      τ.card = N ∧ σ.edges ⊆ τ.edges ∧
      (∑ e ∈ τ.edges \ σ.edges, ∑ i, (x e.1 i - y e.2 i) ^ 2) ≤
        dyadicOrphanRepairBudget K σ x y u ∧
      ((τ.edges \ σ.edges).filter fun e ↦ e ∉ allowed).card ≤ N - σ.card := by
  obtain ⟨τ, hτ, hsub, hcost⟩ := exists_completion_le_adaptiveOrphanRepairBudget σ
    (fun k : Fin K ↦ shiftedDyadicRepairCell q k u)
    (fun k l hkl a b hab ↦ shiftedDyadicRepairCell_nested hkl u a b hab)
    x y (fun i j ↦ ∑ k, (x i k - y j k) ^ 2)
    ((4 * q : ℝ) * (1 / 4 : ℝ) ^ K) (by positivity)
    (fun k ↦ (8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ)) (fun _ ↦ by positivity)
    (fun i j ↦ sq_dist_le_shiftedDyadicRepair_partitionDistance u (x i) (y j) hu (hx i) (hy j))
  exact ⟨τ, hτ, hsub, hcost, by
    simpa using card_illegal_added_le_missing σ τ (by simpa using hτ) hsub allowed⟩

/-- Actual auxiliary phases lie in the required half-open phase cube. -/
theorem ae_shiftedGridPhaseLaw_one_mem {q : ℕ} :
    ∀ᵐ u ∂shiftedGridPhaseLaw q 1, ∀ i, 0 < u i ∧ u i ≤ 1 := by
  have : IsProbabilityMeasure (spatialRootLaw 0 1) := spatialRootLaw_isProbability (by norm_num)
  have hi : ∀ᵐ u ∂spatialRootLaw 0 1, 0 < u ∧ u ≤ 1 :=
    ae_cond_mem measurableSet_Ioc
  exact ae_all_iff.mpr fun i ↦
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin q ↦ spatialRootLaw 0 1) (i := i)).eventually hi

/-- Actual iid samples and one actual common phase give an integrable repair
budget with an explicit finite-cutoff expectation. Only original observations
are assumed iid; the selected core is arbitrary and measurable. -/
theorem integral_dyadicOrphanRepairBudget_le
    {Ω : Type*} [MeasurableSpace Ω] {N q : ℕ} (K : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin q → ℝ)) [IsProbabilityMeasure μ]
    (σ : Ω → OTSelector.PartialMatching N N)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges})
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P)
    (hdisp : Integrable (fun ω ↦ retainedCoordinateDisplacement (σ ω)
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)) P) :
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
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q 1) := shiftedGridPhaseLaw_probability q (by norm_num)
  have h := integral_phase_adaptiveOrphanRepairBudget_le
    (C := fun k : Fin K ↦ Fin q → Fin (2 ^ ((k : ℕ) + 1)))
    P (shiftedGridPhaseLaw q 1) μ σ hσ xs ys hx hy hxi hyi hxl hyl hxy
    (fun k ↦ ((2 : ℝ) ^ (k : ℕ))⁻¹) (fun _ ↦ by positivity)
    (fun u k ↦ shiftedDyadicRepairCell q k u)
    (fun k ↦ measurable_shiftedDyadicRepairCell q k)
    (fun k ↦ shiftedGridPhaseLaw_shiftedDyadicRepairCell_crossing_le (q := q) k)
    ((4 * q : ℝ) * (1 / 4 : ℝ) ^ K)
    (fun k ↦ (8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ)) (fun _ ↦ by positivity) hdisp
  simpa only [dyadicOrphanRepairBudget, Fintype.card_fun, Fintype.card_fin] using h

end OTSelector.Reconstruction
