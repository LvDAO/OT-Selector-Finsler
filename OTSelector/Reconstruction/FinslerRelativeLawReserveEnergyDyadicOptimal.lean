import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyDyadicComplete

/-!
# Concrete quadratic repair of the actual exact-optimal common core

All core measurability and count terms are produced from the original legal
graph, signed costs and common-sampling observations. The remaining explicit
flux term is the actual retained displacement, with no orphan iid premise.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Actual exact-optimal common sampling gives a concrete expected full-repair
budget charged to legal count deficit, original mismatch counts, original iid
histograms and the retained core's actual displacement. -/
theorem integral_dyadic_firstLegalOptimalCommonCoreBudget_le
    {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableEq S] [MeasurableEq T] {N q : ℕ} (K : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin q → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (allowed : Ω → Finset (Fin N × Fin N))
    (hallowed : ∀ E, MeasurableSet {ω | allowed ω = E})
    (score : Ω → Fin N → Fin N → ℝ) (hscore : ∀ i j, Measurable (fun ω ↦ score ω i j))
    (sa sb : Fin N → Ω → S) (ta tb : Fin N → Ω → T)
    (hsa : ∀ i, Measurable (sa i)) (hsb : ∀ i, Measurable (sb i))
    (hta : ∀ j, Measurable (ta j)) (htb : ∀ j, Measurable (tb j))
    (xs ys : Fin N → Ω → Fin q → ℝ)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P) :
    Integrable (fun p : Ω × (Fin q → ℝ) ↦ dyadicOrphanRepairBudget K (firstLegalOptimalCommonCore allowed score sa sb ta tb p.1)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) p.2) (P.prod (shiftedGridPhaseLaw q 1)) ∧
    (∫ p : Ω × (Fin q → ℝ), dyadicOrphanRepairBudget K (firstLegalOptimalCommonCore allowed score sa sb ta tb p.1)
      (fun i ↦ xs i p.1) (fun j ↦ ys j p.1) p.2 ∂(P.prod (shiftedGridPhaseLaw q 1))) ≤
      ((∫ ω, (N : ℝ) - PartialMatching.legalMaximumCard (allowed ω) ∂P) +
        (∫ ω, diffCount N (fun i ↦ (sa i ω, sb i ω)) ∂P) +
        ∫ ω, diffCount N (fun j ↦ (ta j ω, tb j ω)) ∂P) *
        ((4 * q : ℝ) * (1 / 4 : ℝ) ^ K) +
      (1 / 2 : ℝ) * ∑ k : Fin K, ((8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ)) *
        Real.sqrt (2 * (N : ℝ) * ((2 ^ ((k : ℕ) + 1)) ^ q : ℕ)) +
      (∫ ω, retainedCoordinateDisplacement (firstLegalOptimalCommonCore allowed score sa sb ta tb ω)
        (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∂P) *
        ∑ k : Fin K, ((8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ)) / ((2 : ℝ) ^ (k : ℕ))⁻¹ := by
  have h := integral_dyadicOrphanRepairBudget_le_of_original_cube K P μ hμ
    (firstLegalOptimalCommonCore allowed score sa sb ta tb)
    (measurableSet_mem_firstLegalOptimalCommonCore allowed hallowed score hscore sa sb ta tb
      hsa hsb hta htb) xs ys hx hy hxi hyi hxl hyl hxy
  have hcount := integral_firstLegalOptimalCommonCore_missing_le P allowed hallowed score hscore
    sa sb ta tb hsa hsb hta htb
  have hbase : 0 ≤ (4 * q : ℝ) * (1 / 4 : ℝ) ^ K := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcount hbase
  exact ⟨h.1, by linarith [h.2]⟩

end OTSelector.Reconstruction
