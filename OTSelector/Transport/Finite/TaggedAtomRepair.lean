import OTSelector.Finite.LegalFractionalSubarrayRounding
import OTSelector.Transport.Coupling.FiniteStageLegality
import OTSelector.Transport.Coupling.MixtureLabelQuadraticCost
import OTSelector.Transport.Coupling.MixtureLabelTransfer
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairFromCoupling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairFromCoupling`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepairFromCoupling

**Conditions:** Finite original atom arrays carry probability smoothing laws supported within the stated radii; their finite tagged-mixture coupling is strictly class ordered and has integrable squared cost.

**Objects:** A strict-class original-index bijection with explicit joint-cost plus radius-squared error.

**Proof detail:** Extract the genuine tagged endpoint matrix, use the original almost-sure radius bounds in the three-segment squared inequality, and choose a legal supported Birkhoff permutation whose cost does not exceed its weighted mean.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-! A genuine strict-class coupling of the actual tagged smoothing laws yields
a legal repair of the unchanged original finite atom labels and its true cost. -/
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 500000
variable {E I J : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [Fintype I] [Fintype J]

/-- RN unsmoothing and legal rounding produce a strict-class bijection on the
original indices. The error uses the actual number of original source atoms. -/
theorem exists_originalAtoms_strictClassRepair_of_taggedCoupling
    (κ : I → Measure E) (τ : J → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (τ j)]
    (c : I → ℕ) (d : J → ℕ) (x : I → E) (y : J → E)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ i, ∀ᵐ u ∂κ i, dist (x i) u ≤ a)
    (hy : ∀ j, ∀ᵐ v ∂τ j, dist v (y j) ≤ b)
    (Γ : Measure ((ℕ × E) × (ℕ × E))) [IsFiniteMeasure Γ]
    (hΓ : Vlasov.IsCoupling Γ (∑ i, (κ i).map (Prod.mk (c i)))
      (∑ j, (τ j).map (Prod.mk (d j))))
    (hstrict : ∀ᵐ p ∂Γ, p.1.1 < p.2.1)
    (hcost : Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) Γ) :
    ∃ σ : I ≃ J, (∀ i, c i < d (σ i)) ∧
      (∑ i, dist (x i) (y (σ i)) ^ 2) ≤
        3 * (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) +
          3 * (a ^ 2 + b ^ 2) * (Fintype.card I : ℝ) := by
  classical
  let κtag : I → Measure (ℕ × E) := fun i ↦ (κ i).map (Prod.mk (c i))
  let τtag : J → Measure (ℕ × E) := fun j ↦ (τ j).map (Prod.mk (d j))
  have : ∀ i, IsProbabilityMeasure (κtag i) := fun i ↦
    Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable
  have : ∀ j, IsProbabilityMeasure (τtag j) := fun j ↦
    Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable
  have hΓ' : Vlasov.IsCoupling Γ (∑ i, κtag i) (∑ j, τtag j) := hΓ
  let : PseudoMetricSpace (ℕ × E) := classPhysicalPseudoMetricSpace ℕ E
  have hκclass (i : I) : ∀ᵐ p ∂κtag i, p.1 = c i :=
    (classPhysical_smoothing_map_support (κ i) (c i) (x i) (hx i)).1
  have hκsupport (i : I) : ∀ᵐ p ∂κtag i, dist (c i, x i) p ≤ a :=
    (classPhysical_smoothing_map_support (κ i) (c i) (x i) (hx i)).2
  have hτnear (j : J) : ∀ᵐ v ∂τ j, dist (y j) v ≤ b := by
    simpa only [dist_comm] using hy j
  have hτclass (j : J) : ∀ᵐ p ∂τtag j, p.1 = d j :=
    (classPhysical_smoothing_map_support (τ j) (d j) (y j) (hτnear j)).1
  have hτsupport (j : J) : ∀ᵐ p ∂τtag j, dist p (d j, y j) ≤ b := by
    simpa only [dist_comm] using
      (classPhysical_smoothing_map_support (τ j) (d j) (y j) (hτnear j)).2
  have hI : Integrable (fun p : (ℕ × E) × (ℕ × E) ↦ dist p.1 p.2 ^ 2) Γ := hcost
  let P := smoothingEndpointLabelMatrix κtag τtag Γ
  obtain ⟨hP, hrow, hcol⟩ := smoothingEndpointLabelMatrix_rows_columns κtag τtag Γ hΓ'
  have hlegal := smoothingEndpointLabelMatrix_zero_of_forbidden_labels κtag τtag Γ hΓ'
    Prod.fst Prod.fst c d (fun i j : ℕ ↦ i < j) hκclass hτclass hstrict
  have hPbound := smoothingEndpointLabelMatrix_quadratic_cost_le κtag τtag
    (fun i ↦ (c i, x i)) (fun j ↦ (d j, y j)) ha hb hκsupport hτsupport Γ hΓ' hI
  have hmass : Γ univ = (Fintype.card I : ℝ≥0∞) := by
    have h := congrArg (fun μ : Measure (ℕ × E) ↦ μ univ) hΓ'.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
      Measure.finsetSum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using h
  have hmassR : Γ.real univ = (Fintype.card I : ℝ) := by
    rw [measureReal_def, hmass, ENNReal.toReal_natCast]
  have hPbound' : (∑ i, ∑ j, P i j * dist (x i) (y j) ^ 2) ≤
      3 * (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) +
        3 * (a ^ 2 + b ^ 2) * (Fintype.card I : ℝ) := by
    change (∑ i, ∑ j, P i j * dist (x i) (y j) ^ 2) ≤
      3 * (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) + 3 * (a ^ 2 + b ^ 2) * Γ.real univ at hPbound
    rw [hmassR] at hPbound
    exact hPbound
  obtain ⟨σ, hσ, hσcost⟩ := OTSelector.exists_legalEquiv_le_unitCapacityPlanCost
    P (fun i j ↦ dist (x i) (y j) ^ 2) hP hrow hcol (fun i j ↦ c i < d j) hlegal
  exact ⟨σ, hσ, hσcost.trans hPbound'⟩

end OTSelector.Reconstruction

end
end
