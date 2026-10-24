import OTSelector.Finite.LegalFractionalSubarrayRounding
import OTSelector.Transport.Coupling.FiniteStageLegality
import OTSelector.Transport.Coupling.MixtureDeviationEnergy
import OTSelector.Transport.Coupling.MixtureLabelTransfer
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairEnergyFromCoupling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairEnergyFromCoupling`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepairEnergyFromCoupling

**Conditions:** Finite original atom arrays carry probability smoothing laws with integrable squared deviations; a finite coupling of their tagged mixtures has strict class order and integrable squared cost.

**Objects:** A strict-class original-index bijection with cost bounded by the true joint and endpoint deviation energies.

**Proof detail:** Keep original tags while extracting the exact RN endpoint matrix, whose forbidden class entries vanish; integrate the three-segment squared-distance estimate and legally round the matrix by a supported Birkhoff permutation.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): Only the selected generic source commands are covered. The cited book sections provide the finite assignment, finite-sum or coupling foundations; the exact construction and quantitative statement are local corollaries or Lean adapters, not a claim that the book contains the same named Lean lemma.
-/

/-! True endpoint energies yield strict legal repair on the original atom labels. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Reconstruction

/-- The actual tagged mixture coupling gives a strict original-label bijection;
the error is exactly the two actual integrated endpoint deviation energies. -/
theorem exists_originalAtoms_strictClassRepair_of_taggedCoupling_deviationEnergy
    {E I J : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [Fintype I] [Fintype J]
    (κ : I → Measure E) (τ : J → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (τ j)]
    (c : I → ℕ) (d : J → ℕ) (x : I → E) (y : J → E)
    (hκI : ∀ i, Integrable (fun u ↦ dist (x i) u ^ 2) (κ i))
    (hτI : ∀ j, Integrable (fun v ↦ dist v (y j) ^ 2) (τ j))
    (Γ : Measure ((ℕ × E) × (ℕ × E))) [IsFiniteMeasure Γ]
    (hΓ : Vlasov.IsCoupling Γ (∑ i, (κ i).map (Prod.mk (c i)))
      (∑ j, (τ j).map (Prod.mk (d j))))
    (hstrict : ∀ᵐ p ∂Γ, p.1.1 < p.2.1)
    (hcost : Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) Γ) :
    ∃ σ : I ≃ J, (∀ i, c i < d (σ i)) ∧
      (∑ i, dist (x i) (y (σ i)) ^ 2) ≤
        3 * (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) +
          3 * (∑ i, ∫ u, dist (x i) u ^ 2 ∂κ i) +
          3 * (∑ j, ∫ v, dist v (y j) ^ 2 ∂τ j) := by
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
    (measurableEmbedding_prodMk_left (c i)).ae_map_iff.mpr (ae_of_all _ fun _ ↦ rfl)
  have hτclass (j : J) : ∀ᵐ p ∂τtag j, p.1 = d j :=
    (measurableEmbedding_prodMk_left (d j)).ae_map_iff.mpr (ae_of_all _ fun _ ↦ rfl)
  have hκtagI (i : I) : Integrable (fun p ↦ dist (c i, x i) p ^ 2) (κtag i) :=
    (measurableEmbedding_prodMk_left (c i)).integrable_map_iff.mpr (hκI i)
  have hτtagI (j : J) : Integrable (fun p ↦ dist p (d j, y j) ^ 2) (τtag j) :=
    (measurableEmbedding_prodMk_left (d j)).integrable_map_iff.mpr (hτI j)
  have hκenergy (i : I) : (∫ p, dist (x i) p.2 ^ 2 ∂κtag i) =
      ∫ u, dist (x i) u ^ 2 ∂κ i :=
    (measurableEmbedding_prodMk_left (c i)).integral_map _
  have hτenergy (j : J) : (∫ p, dist p.2 (y j) ^ 2 ∂τtag j) =
      ∫ v, dist v (y j) ^ 2 ∂τ j :=
    (measurableEmbedding_prodMk_left (d j)).integral_map _
  have hI : Integrable (fun p : (ℕ × E) × (ℕ × E) ↦ dist p.1 p.2 ^ 2) Γ := hcost
  let P := smoothingEndpointLabelMatrix κtag τtag Γ
  obtain ⟨hP, hrow, hcol⟩ := smoothingEndpointLabelMatrix_rows_columns κtag τtag Γ hΓ'
  have hlegal := smoothingEndpointLabelMatrix_zero_of_forbidden_labels κtag τtag Γ hΓ'
    Prod.fst Prod.fst c d (fun i j : ℕ ↦ i < j) hκclass hτclass hstrict
  have hPbound := smoothingEndpointLabelMatrix_quadratic_cost_le_deviationEnergy κtag τtag
    (fun i ↦ (c i, x i)) (fun j ↦ (d j, y j)) hκtagI hτtagI Γ hΓ' hI
  change (∑ i, ∑ j, P i j * dist (x i) (y j) ^ 2) ≤
    3 * (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) +
      3 * (∑ i, ∫ p, dist (x i) p.2 ^ 2 ∂κtag i) +
      3 * (∑ j, ∫ p, dist p.2 (y j) ^ 2 ∂τtag j) at hPbound
  simp_rw [hκenergy, hτenergy] at hPbound
  obtain ⟨σ, hσ, hσcost⟩ := OTSelector.exists_legalEquiv_le_unitCapacityPlanCost
    P (fun i j ↦ dist (x i) (y j) ^ 2) hP hrow hcol (fun i j ↦ c i < d j) hlegal
  exact ⟨σ, hσ, hσcost.trans hPbound⟩

end OTSelector.Reconstruction

end
end
