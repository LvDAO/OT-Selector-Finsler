import OTSelector.Reconstruction.FinslerRelativeLawFixedInversePopulation
import OTSelector.Reconstruction.FinslerRelativeLawCellwiseBinPopulation

/-!
Retained and residual original populations use one given original physical
recovery inverse. Exact original marginals, calibration and residual mass are
preserved without choosing a second inverse for the coefficient comparison.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Original varying-bin cell splits use the same given original physical
recovery map for their retained populations and deterministic residual. -/
theorem exists_original_cellwise_bin_residual_population_with_inverse
    {X Z C : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    [Fintype C] {N : Set X} (hN : MeasurableSet N)
    {a : X → Z} {u : X → ℝ} (ha : Measurable a) (hu : Measurable u)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (π : Measure (X × X)) (hπ : Vlasov.IsCoupling π μ ν)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (hforward : ∀ᵐ p ∂π, u p.1 ≤ u p.2)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (I J : C → Type*) [∀ c, Fintype (I c)] [∀ c, Fintype (J c)]
    (S : ∀ c, I c → Set ℝ) (T : ∀ c, J c → Set ℝ)
    (hS : ∀ c i, MeasurableSet (S c i)) (hT : ∀ c j, MeasurableSet (T c j))
    (hdS : ∀ c, Pairwise (Disjoint on S c)) (hdT : ∀ c, Pairwise (Disjoint on T c))
    (hcoverS : ∀ᵐ z ∂μ.map a, ∀ c, z ∈ cell c →
      ∀ᵐ s ∂condDistrib u a μ z, s ∈ ⋃ i, S c i)
    (hcoverT : ∀ᵐ z ∂μ.map a, ∀ c, z ∈ cell c →
      ∀ᵐ t ∂condDistrib u a ν z, t ∈ ⋃ j, T c j)
    (fallbackS : ∀ c, I c → ℝ) (fallbackT : ∀ c, J c → ℝ)
    (allowed : ∀ c, I c → J c → Prop)
    (hbins : ∀ c i j, allowed c i j → ∀ s ∈ S c i, ∀ t ∈ T c j, s ≤ t)
    (P Q : ∀ c, Z → I c → J c → ℝ)
    (hmP : ∀ c i j, Measurable (fun z ↦ P c z i j))
    (hmQ : ∀ c i j, Measurable (fun z ↦ Q c z i j))
    (B : ℝ)
    (hflow : ∀ᵐ z ∂μ.map a, ∀ c, z ∈ cell c →
      (∀ i j, 0 ≤ P c z i j) ∧ (∀ i j, 0 ≤ Q c z i j) ∧
      (∀ i, ∑ j, (P c z i j + Q c z i j) = (condDistrib u a μ z).real (S c i)) ∧
      (∀ j, ∑ i, (P c z i j + Q c z i j) = (condDistrib u a ν z).real (T c j)) ∧
      (∀ i j, ¬ allowed c i j → P c z i j = 0 ∧ Q c z i j = 0) ∧
      (∑ i, ∑ j, Q c z i j) ≤ B) :
    let α := fun c i ↦ normalizedActualBinKernel (condDistrib u a μ)
      (S c i) (hS c i) (fallbackS c i)
    let β := fun c j ↦ normalizedActualBinKernel (condDistrib u a ν)
      (T c j) (hT c j) (fallbackT c j)
    let KP := fun c ↦ finiteClassPopulationKernel (P c) (α c) (β c)
    let χ := ((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell KP).map sameLabelPopulationPair
    ∃ ξ : Measure (X × X),
      Vlasov.IsCoupling (χ.map (Prod.map b b) + ξ) μ ν ∧
      (∀ᵐ p ∂χ.map (Prod.map b b) + ξ, u p.2 - u p.1 = dist p.1 p.2) ∧
      ξ ≤ χ.map (Prod.map b b) + ξ ∧
      ξ univ ≤ ENNReal.ofReal B + (μ.map a) (⋃ c, cell c)ᶜ := by
  let α := fun c i ↦ normalizedActualBinKernel (condDistrib u a μ)
    (S c i) (hS c i) (fallbackS c i)
  let β := fun c j ↦ normalizedActualBinKernel (condDistrib u a ν)
    (T c j) (hT c j) (fallbackT c j)
  let KP := fun c ↦ finiteClassPopulationKernel (P c) (α c) (β c)
  let KQ := fun c ↦ finiteClassPopulationKernel (Q c) (α c) (β c)
  have hsplit : ∀ᵐ z ∂μ.map a, ∀ c, z ∈ cell c →
      Vlasov.IsCoupling (KP c z + KQ c z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
      (∀ᵐ p ∂KP c z + KQ c z, p.1 ≤ p.2) ∧ KQ c z univ ≤ ENNReal.ofReal B := by
    filter_upwards [hcoverS, hcoverT, hflow] with z hs ht hf
    intro c hc
    obtain ⟨hp, hq, hr, hcol, hzero, hm⟩ := hf c hc
    exact originalBinPairKernel_split_at (condDistrib u a μ) (condDistrib u a ν)
      (S c) (T c) (hS c) (hT c) (hdS c) (hdT c) (fallbackS c) (fallbackT c)
      (P c) (Q c) (hmP c) (hmQ c) (allowed c) (hbins c) z (hs c hc) (ht c hc)
      hp hq hr hcol hzero B hm
  exact exists_original_cellwise_residual_population_with_inverse hN ha hu horder μ ν hμN hνN
    b hb hμinv hνinv π hπ hlabel hforward cell hcell hdisj KP KQ
    (hsplit.mono fun z hz c hc ↦ ⟨(hz c hc).1, (hz c hc).2.1⟩)
    B (hsplit.mono fun z hz c hc ↦ (hz c hc).2.2)


end OTSelector.Reconstruction
