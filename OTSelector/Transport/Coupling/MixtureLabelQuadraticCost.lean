import OTSelector.Transport.Coupling.MixtureLabelTransfer
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalSmoothingEndpointCouplingTransferQuadratic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalSmoothingEndpointCouplingTransferQuadratic`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalSmoothingEndpointCouplingTransferQuadratic

**Conditions:** Finite endpoint smoothing families and an actual coupling of their sums; original endpoints are almost surely within the stated smoothing radii.

**Objects:** The literal endpoint label matrix and its recovered quadratic transport cost.

**Proof detail:** Split the coupling into its true endpoint components, integrate the three-segment inequality d(x,y)^2≤3(d(x,u)^2+d(u,v)^2+d(v,y)^2), and use their exact sum and marginals.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini); [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Recover the literal original atom cost from a coupling of overlapping
smoothing mixtures by integrating the three-segment squared-distance bound. -/
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 150000
variable {E I J : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
  [Fintype I] [Fintype J]

omit [MeasurableSpace E] in
/-- The elementary three-segment estimate underlying endpoint unsmoothing. -/
theorem smoothingEndpoint_dist_sq_le (x y u v : E) {a b : ℝ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hx : dist x u ≤ a) (hy : dist v y ≤ b) :
    dist x y ^ 2 ≤ 3 * dist u v ^ 2 + 3 * (a ^ 2 + b ^ 2) := by
  have htri : dist x y ≤ a + dist u v + b := (dist_triangle4 x u v y).trans (by linarith)
  have hsquare := mul_self_le_mul_self (dist_nonneg : 0 ≤ dist x y) htri
  nlinarith [sq_nonneg (a - dist u v), sq_nonneg (a - b), sq_nonneg (dist u v - b)]

omit [PseudoMetricSpace E] in
/-- Integrals of the actual label subcouplings add back to the given plan. -/
theorem smoothingEndpointCouplingPart_integral_sum
    (κ : I → Measure E) (σ : J → Measure E)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (π : Measure (E × E)) (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j))
    {f : E × E → ℝ} (hf : Integrable f π) :
    (∑ i, ∑ j, ∫ z, f z ∂smoothingEndpointCouplingPart κ σ π i j) = ∫ z, f z ∂π := by
  classical
  have hsub (i : I) (j : J) := smoothingEndpointCouplingPart_le κ σ π hπ i j
  have hrow (i : I) : (∑ j, smoothingEndpointCouplingPart κ σ π i j) ≤ π := by
    calc
      _ ≤ ∑ k, ∑ j, smoothingEndpointCouplingPart κ σ π k j :=
        Finset.single_le_sum (f := fun k ↦ ∑ j, smoothingEndpointCouplingPart κ σ π k j)
          (fun _ _ ↦ bot_le) (Finset.mem_univ i)
      _ = π := smoothingEndpointCouplingPart_sum κ σ π hπ
  calc
    _ = ∑ i, ∫ z, f z ∂(∑ j, smoothingEndpointCouplingPart κ σ π i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum_measure (fun j _ ↦ hf.mono_measure (hsub i j))).symm
    _ = ∫ z, f z ∂(∑ i, ∑ j, smoothingEndpointCouplingPart κ σ π i j) :=
      (integral_finsetSum_measure (fun i _ ↦ hf.mono_measure (hrow i))).symm
    _ = _ := by rw [smoothingEndpointCouplingPart_sum κ σ π hπ]

/-- A genuine coupling of arbitrary finite smoothing mixtures controls the
literal squared cost of its recovered original labelled matrix. The error is
proportional to the actual total mass and the two squared smoothing radii. -/
theorem smoothingEndpointLabelMatrix_quadratic_cost_le
    (κ : I → Measure E) (σ : J → Measure E)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (x : I → E) (y : J → E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ i, ∀ᵐ u ∂κ i, dist (x i) u ≤ a)
    (hy : ∀ j, ∀ᵐ v ∂σ j, dist v (y j) ≤ b)
    (π : Measure (E × E)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j))
    (hcost : Integrable (fun z : E × E ↦ dist z.1 z.2 ^ 2) π) :
    (∑ i, ∑ j, smoothingEndpointLabelMatrix κ σ π i j * dist (x i) (y j) ^ 2) ≤
      3 * (∫ z, dist z.1 z.2 ^ 2 ∂π) + 3 * (a ^ 2 + b ^ 2) * π.real univ := by
  classical
  have hsub (i : I) (j : J) := smoothingEndpointCouplingPart_le κ σ π hπ i j
  have hparts (i : I) (j : J) :
      smoothingEndpointLabelMatrix κ σ π i j * dist (x i) (y j) ^ 2 ≤
        3 * (∫ z, dist z.1 z.2 ^ 2 ∂smoothingEndpointCouplingPart κ σ π i j) +
          3 * (a ^ 2 + b ^ 2) * (smoothingEndpointCouplingPart κ σ π i j).real univ := by
    let τ := smoothingEndpointCouplingPart κ σ π i j
    have : IsFiniteMeasure τ := isFiniteMeasure_of_le π (hsub i j)
    have hleft : τ.map Prod.fst ≤ κ i := by
      rw [← smoothingEndpointCouplingPart_row κ σ π hπ i]
      exact Measure.map_mono
        (Finset.single_le_sum (f := fun l ↦ smoothingEndpointCouplingPart κ σ π i l)
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)) measurable_fst
    have hright : τ.map Prod.snd ≤ σ j := by
      rw [← smoothingEndpointCouplingPart_column κ σ π hπ j]
      exact Measure.map_mono
        (Finset.single_le_sum (f := fun k ↦ smoothingEndpointCouplingPart κ σ π k j)
          (fun _ _ ↦ bot_le) (Finset.mem_univ i)) measurable_snd
    have hx' := ae_of_ae_map (μ := τ) measurable_fst.aemeasurable
      (hleft.absolutelyContinuous.ae_le (hx i))
    have hy' := ae_of_ae_map (μ := τ) measurable_snd.aemeasurable
      (hright.absolutelyContinuous.ae_le (hy j))
    have hτcost : Integrable (fun z : E × E ↦ dist z.1 z.2 ^ 2) τ :=
      hcost.mono_measure (hsub i j)
    have hthree : Integrable (fun z : E × E ↦ (3 : ℝ) * dist z.1 z.2 ^ 2) τ :=
      hτcost.const_mul (3 : ℝ)
    have hconstant : Integrable (fun _ : E × E ↦ (3 : ℝ) * (a ^ 2 + b ^ 2)) τ :=
      integrable_const _
    have hrightI : Integrable (fun z : E × E ↦ (3 : ℝ) * dist z.1 z.2 ^ 2 +
        3 * (a ^ 2 + b ^ 2)) τ := hthree.add hconstant
    calc
      _ = ∫ _z, dist (x i) (y j) ^ 2 ∂τ := by
        simp only [integral_const, smul_eq_mul, smoothingEndpointLabelMatrix, τ]
      _ ≤ ∫ z, (3 * dist z.1 z.2 ^ 2 + 3 * (a ^ 2 + b ^ 2)) ∂τ :=
        integral_mono_ae (integrable_const (μ := τ) (dist (x i) (y j) ^ 2))
          hrightI
          (by filter_upwards [hx', hy'] with z hz₁ hz₂
              exact smoothingEndpoint_dist_sq_le (x i) (y j) z.1 z.2 ha hb hz₁ hz₂)
      _ = _ := by
        rw [integral_add hthree hconstant, integral_const_mul,
          integral_const, smul_eq_mul]
        ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) ↦ hparts i j))
  have hmass := smoothingEndpointCouplingPart_integral_sum κ σ π hπ (integrable_const (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at hmass
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    smoothingEndpointCouplingPart_integral_sum κ σ π hπ hcost, hmass] using hsum

/-- Unsmoothing an actual finite-mass quadratic endpoint coupling produces a
nonnegative original label matrix with exact unit rows and columns. Empty label
sets require no special convention or normalization. -/
theorem exists_smoothingEndpoint_quadratic_labelMatrix
    (κ : I → Measure E) (σ : J → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (σ j)]
    (x : I → E) (y : J → E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ i, ∀ᵐ u ∂κ i, dist (x i) u ≤ a)
    (hy : ∀ j, ∀ᵐ v ∂σ j, dist v (y j) ≤ b)
    (π : Measure (E × E))
    (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j))
    (hcost : Integrable (fun z : E × E ↦ dist z.1 z.2 ^ 2 / 2) π) :
    ∃ P : I → J → ℝ, (∀ i j, 0 ≤ P i j) ∧
      (∀ i, ∑ j, P i j = 1) ∧ (∀ j, ∑ i, P i j = 1) ∧
      (∑ i, ∑ j, P i j * (dist (x i) (y j) ^ 2 / 2)) ≤
        3 * (∫ z, dist z.1 z.2 ^ 2 / 2 ∂π) +
          (3 / 2 : ℝ) * (a ^ 2 + b ^ 2) * π.real univ := by
  classical
  have hmass : π univ = (∑ i, κ i) univ := by
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using
      congrArg (fun μ : Measure E ↦ μ univ) hπ.1
  have : IsFiniteMeasure π := ⟨by rw [hmass]; exact measure_lt_top _ _⟩
  have hfull : Integrable (fun z : E × E ↦ dist z.1 z.2 ^ 2) π := by
    convert hcost.mul_const (2 : ℝ) using 1
    ext z
    ring
  obtain ⟨hP, hrow, hcol⟩ := smoothingEndpointLabelMatrix_rows_columns κ σ π hπ
  refine ⟨smoothingEndpointLabelMatrix κ σ π, hP, hrow, hcol, ?_⟩
  have hbound := smoothingEndpointLabelMatrix_quadratic_cost_le κ σ x y ha hb hx hy π hπ hfull
  have hsum : (∑ i, ∑ j, smoothingEndpointLabelMatrix κ σ π i j * (dist (x i) (y j) ^ 2 / 2)) =
      (∑ i, ∑ j, smoothingEndpointLabelMatrix κ σ π i j * dist (x i) (y j) ^ 2) / 2 := by
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
  have hint : (∫ z, dist z.1 z.2 ^ 2 ∂π) =
      2 * (∫ z, dist z.1 z.2 ^ 2 / 2 ∂π) := by
    calc
      _ = ∫ z, (2 : ℝ) * (dist z.1 z.2 ^ 2 / 2) ∂π := by
        apply integral_congr_ae
        exact Eventually.of_forall fun _ ↦ by ring
      _ = _ := integral_const_mul _ _
  rw [hsum]
  rw [hint] at hbound
  linarith

end OTSelector.Reconstruction

end
end
