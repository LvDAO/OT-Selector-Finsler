import OTSelector.Transport.Coupling.MixtureLabelQuadraticCost
import OTSelector.Transport.Coupling.MixtureLabelTransfer
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairDeviationEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairDeviationEnergy`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepairDeviationEnergy

**Conditions:** Actual finite endpoint smoothing families have integrable squared deviations and the original smoothed coupling has integrable squared cost.

**Objects:** The original-label matrix cost bound using actual integrated endpoint deviations.

**Proof detail:** Integrate the three-segment squared-distance inequality over the exact endpoint components; their sums and pushforward marginals recover the original joint cost and both endpoint deviation energies.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Actual integrated endpoint deviations replace uniform unsmoothing radii. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Reconstruction

private theorem finiteParts_integral_readout
    {X Y K : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype K]
    (parts : K → Measure X) (F : X → Y) (hF : Measurable F)
    (μ : Measure Y) (hμ : (∑ k, parts k).map F = μ)
    (f : Y → ℝ) (hf : Integrable f μ) :
    (∀ k, Integrable (fun z ↦ f (F z)) (parts k)) ∧
      (∑ k, ∫ z, f (F z) ∂parts k) = ∫ y, f y ∂μ := by
  classical
  have hm : Integrable f ((∑ k, parts k).map F) := by rwa [hμ]
  have hs : Integrable (fun z ↦ f (F z)) (∑ k, parts k) :=
    hm.comp_aemeasurable hF.aemeasurable
  have hp (k : K) : Integrable (fun z ↦ f (F z)) (parts k) :=
    integrable_finsetSum_measure.mp hs k (Finset.mem_univ k)
  refine ⟨hp, ?_⟩
  calc
    _ = ∫ z, f (F z) ∂(∑ k, parts k) :=
      (integral_finsetSum_measure (fun k _ ↦ hp k)).symm
    _ = ∫ y, f y ∂((∑ k, parts k).map F) :=
      (integral_map hF.aemeasurable hm.aestronglyMeasurable).symm
    _ = _ := by rw [hμ]

/-- The same concrete RN label matrix obeys the true integrated three-segment
bound, with actual source and target smoothing energies and arbitrary finite mass. -/
theorem smoothingEndpointLabelMatrix_quadratic_cost_le_deviationEnergy
    {E I J : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [Fintype I] [Fintype J]
    (κ : I → Measure E) (σ : J → Measure E)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (x : I → E) (y : J → E)
    (hκI : ∀ i, Integrable (fun u ↦ dist (x i) u ^ 2) (κ i))
    (hσI : ∀ j, Integrable (fun v ↦ dist v (y j) ^ 2) (σ j))
    (π : Measure (E × E)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j))
    (hcost : Integrable (fun z : E × E ↦ dist z.1 z.2 ^ 2) π) :
    (∑ i, ∑ j, smoothingEndpointLabelMatrix κ σ π i j * dist (x i) (y j) ^ 2) ≤
      3 * (∫ z, dist z.1 z.2 ^ 2 ∂π) +
        3 * (∑ i, ∫ u, dist (x i) u ^ 2 ∂κ i) +
        3 * (∑ j, ∫ v, dist v (y j) ^ 2 ∂σ j) := by
  classical
  have hsrc (i : I) := finiteParts_integral_readout
    (fun j ↦ smoothingEndpointCouplingPart κ σ π i j) Prod.fst measurable_fst
    (κ i) (smoothingEndpointCouplingPart_row κ σ π hπ i)
    (fun u ↦ dist (x i) u ^ 2) (hκI i)
  have htgt (j : J) := finiteParts_integral_readout
    (fun i ↦ smoothingEndpointCouplingPart κ σ π i j) Prod.snd measurable_snd
    (σ j) (smoothingEndpointCouplingPart_column κ σ π hπ j)
    (fun v ↦ dist v (y j) ^ 2) (hσI j)
  have hpart (i : I) (j : J) :
      smoothingEndpointLabelMatrix κ σ π i j * dist (x i) (y j) ^ 2 ≤
        3 * (∫ z, dist z.1 z.2 ^ 2 ∂smoothingEndpointCouplingPart κ σ π i j) +
        3 * (∫ z, dist (x i) z.1 ^ 2 ∂smoothingEndpointCouplingPart κ σ π i j) +
        3 * (∫ z, dist z.2 (y j) ^ 2 ∂smoothingEndpointCouplingPart κ σ π i j) := by
    let τ := smoothingEndpointCouplingPart κ σ π i j
    have hsub := smoothingEndpointCouplingPart_le κ σ π hπ i j
    have : IsFiniteMeasure τ := isFiniteMeasure_of_le π hsub
    have hc : Integrable (fun z : E × E ↦ dist z.1 z.2 ^ 2) τ :=
      hcost.mono_measure hsub
    have hx : Integrable (fun z : E × E ↦ dist (x i) z.1 ^ 2) τ := (hsrc i).1 j
    have hy : Integrable (fun z : E × E ↦ dist z.2 (y j) ^ 2) τ := (htgt j).1 i
    have hthree := hc.const_mul (3 : ℝ)
    have herror : Integrable (fun z : E × E ↦
        (3 : ℝ) * (dist (x i) z.1 ^ 2 + dist z.2 (y j) ^ 2)) τ :=
      (hx.add hy).const_mul (3 : ℝ)
    calc
      _ = ∫ _z, dist (x i) (y j) ^ 2 ∂τ := by
        simp only [integral_const, smul_eq_mul, smoothingEndpointLabelMatrix, τ]
      _ ≤ ∫ z, (3 * dist z.1 z.2 ^ 2 +
          3 * (dist (x i) z.1 ^ 2 + dist z.2 (y j) ^ 2)) ∂τ := by
        apply integral_mono_ae (integrable_const _) (hthree.add herror)
        exact Eventually.of_forall fun z ↦ smoothingEndpoint_dist_sq_le
          (x i) (y j) z.1 z.2 dist_nonneg dist_nonneg le_rfl le_rfl
      _ = _ := by
        rw [integral_add hthree herror, integral_const_mul, integral_const_mul,
          integral_add hx hy]
        ring
  have hsource :
      (∑ i, ∑ j, ∫ z, dist (x i) z.1 ^ 2 ∂smoothingEndpointCouplingPart κ σ π i j) =
        ∑ i, ∫ u, dist (x i) u ^ 2 ∂κ i := by
    exact Finset.sum_congr rfl fun i _ ↦ (hsrc i).2
  have htarget :
      (∑ i, ∑ j, ∫ z, dist z.2 (y j) ^ 2 ∂smoothingEndpointCouplingPart κ σ π i j) =
        ∑ j, ∫ v, dist v (y j) ^ 2 ∂σ j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ (htgt j).2
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) ↦ hpart i j))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    smoothingEndpointCouplingPart_integral_sum κ σ π hπ hcost, hsource, htarget] using hsum

end OTSelector.Reconstruction

end
end
