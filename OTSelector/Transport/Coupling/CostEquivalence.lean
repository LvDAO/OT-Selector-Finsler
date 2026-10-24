import LeanPool.Vlasov.OT.Coupling

/-!
## Lemma skeleton

* **Conditions:** Independent measurable equivalences of source and target spaces and pointwise equality of nonnegative extended costs under their product map.
* **Objects:** Bijections of joint measures, feasible couplings and the whole optimal-coupling set; extended lower-integral cost.
* **Proof detail:** Push joint measures through the product equivalence, verify both marginals by projection functoriality, preserve lower integrals by change of variables, and compare every competitor through the inverse map.

## Mathematical sources

* Gabriel Peyré; Marco Cuturi, *Computational Optimal Transport (2019 author version)*, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
  https://optimaltransport.github.io/pdf/ComputationalOT.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf

**Relationship to the sources:** The references supply pushforward integration and the coupling optimization definition. The full-set equivalence and lower-integral generality are locally proved consequences; they require neither finiteness, optimizer attainment nor uniqueness.
-/

/-!
# Cost-preserving transformations of the whole optimal-coupling set

Independent measurable equivalences of the source and target spaces map couplings bijectively
onto couplings of the pushed-forward marginals. If they preserve the cost pointwise, they preserve
every coupling's nonnegative extended-valued cost and the entire optimal-coupling set. The lower
integral records a nonintegrable cost as infinity; no finiteness assumption or optimal-plan choice
is used. In particular, this applies to genuine distance costs under measurable isometries.

The marginal predicate is the existing `Vlasov.IsCoupling`. Optimality here means exactly
feasibility and comparison with every feasible coupling, including fractional couplings and ties.
-/

open MeasureTheory
open scoped ENNReal

namespace OTSelector

variable {α β α' β' : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace α'] [MeasurableSpace β']

/-- The nonnegative extended cost of a coupling; infinite costs retain their actual value. -/
noncomputable def couplingCost (cost : α → β → ℝ≥0∞) (π : Measure (α × β)) : ℝ≥0∞ :=
  ∫⁻ z, cost z.1 z.2 ∂π

/-- An optimal coupling is feasible and costs no more than every other feasible coupling. -/
def IsOptimalCoupling (cost : α → β → ℝ≥0∞) (μ : Measure α) (ν : Measure β)
    (π : Measure (α × β)) : Prop :=
  Vlasov.IsCoupling π μ ν ∧
    ∀ κ : Measure (α × β), Vlasov.IsCoupling κ μ ν → couplingCost cost π ≤ couplingCost cost κ

/-- Pushforward along the product equivalence is an equivalence of all joint measures. -/
noncomputable def couplingMeasureEquiv (e : α ≃ᵐ α') (f : β ≃ᵐ β') :
    Measure (α × β) ≃ Measure (α' × β') where
  toFun := Measure.map (e.prodCongr f)
  invFun := Measure.map (e.prodCongr f).symm
  left_inv := fun π ↦ (e.prodCongr f).map_symm_map (μ := π)
  right_inv := fun π ↦ (e.prodCongr f).map_map_symm (ν := π)

/-- Product pushforward preserves and reflects the prescribed marginal constraints. -/
theorem isCoupling_map_iff (e : α ≃ᵐ α') (f : β ≃ᵐ β')
    {μ : Measure α} {ν : Measure β} {π : Measure (α × β)} :
    Vlasov.IsCoupling (π.map (e.prodCongr f)) (μ.map e) (ν.map f) ↔
      Vlasov.IsCoupling π μ ν := by
  constructor
  · intro hπ
    have h := hπ.map e.symm f.symm e.symm.measurable f.symm.measurable
    change Vlasov.IsCoupling
      ((π.map (e.prodCongr f)).map (e.prodCongr f).symm)
      ((μ.map e).map e.symm) ((ν.map f).map f.symm) at h
    simpa only [MeasurableEquiv.map_symm_map] using h
  · intro hπ
    exact hπ.map e f e.measurable f.measurable

/-- The exact bijection between all couplings of the original and pushed-forward marginals. -/
noncomputable def couplingEquiv (e : α ≃ᵐ α') (f : β ≃ᵐ β')
    (μ : Measure α) (ν : Measure β) :
    {π : Measure (α × β) // Vlasov.IsCoupling π μ ν} ≃
      {π : Measure (α' × β') // Vlasov.IsCoupling π (μ.map e) (ν.map f)} :=
  (couplingMeasureEquiv e f).subtypeEquiv fun _ ↦ (isCoupling_map_iff e f).symm

@[simp]
theorem couplingEquiv_apply (e : α ≃ᵐ α') (f : β ≃ᵐ β')
    (μ : Measure α) (ν : Measure β) (π : {π // Vlasov.IsCoupling π μ ν}) :
    (couplingEquiv e f μ ν π).val = π.val.map (e.prodCongr f) :=
  rfl

/-- A pointwise cost identity preserves every joint measure's lower integral, even at infinity. -/
theorem couplingCost_map (e : α ≃ᵐ α') (f : β ≃ᵐ β')
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (e x) (f y) = cost x y) (π : Measure (α × β)) :
    couplingCost cost' (π.map (e.prodCongr f)) = couplingCost cost π := by
  rw [couplingCost, lintegral_map_equiv]
  exact lintegral_congr fun z ↦ hcost z.1 z.2

/-- Exact cost preservation transports optimality in both directions, with no unique-choice rule. -/
theorem isOptimalCoupling_map_iff (e : α ≃ᵐ α') (f : β ≃ᵐ β')
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (e x) (f y) = cost x y)
    {μ : Measure α} {ν : Measure β} {π : Measure (α × β)} :
    IsOptimalCoupling cost' (μ.map e) (ν.map f) (π.map (e.prodCongr f)) ↔
      IsOptimalCoupling cost μ ν π := by
  constructor
  · rintro ⟨hπ, hmin⟩
    refine ⟨(isCoupling_map_iff e f).mp hπ, fun κ hκ ↦ ?_⟩
    have h := hmin (κ.map (e.prodCongr f)) ((isCoupling_map_iff e f).mpr hκ)
    simpa only [couplingCost_map e f cost cost' hcost] using h
  · rintro ⟨hπ, hmin⟩
    refine ⟨(isCoupling_map_iff e f).mpr hπ, fun κ hκ ↦ ?_⟩
    let κ₀ := (couplingEquiv e f μ ν).symm ⟨κ, hκ⟩
    have hκ₀ : κ₀.val.map (e.prodCongr f) = κ :=
      congrArg Subtype.val ((couplingEquiv e f μ ν).apply_symm_apply ⟨κ, hκ⟩)
    calc
      couplingCost cost' (π.map (e.prodCongr f)) = couplingCost cost π :=
        couplingCost_map e f cost cost' hcost π
      _ ≤ couplingCost cost κ₀.val := hmin κ₀.val κ₀.property
      _ = couplingCost cost' (κ₀.val.map (e.prodCongr f)) :=
        (couplingCost_map e f cost cost' hcost κ₀.val).symm
      _ = couplingCost cost' κ := congrArg (couplingCost cost') hκ₀

/-- The pushforward bijection restricts to the entire optimal-coupling set. -/
noncomputable def optimalCouplingEquiv (e : α ≃ᵐ α') (f : β ≃ᵐ β')
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (e x) (f y) = cost x y)
    (μ : Measure α) (ν : Measure β) :
    {π : Measure (α × β) // IsOptimalCoupling cost μ ν π} ≃
      {π : Measure (α' × β') // IsOptimalCoupling cost' (μ.map e) (ν.map f) π} :=
  (couplingMeasureEquiv e f).subtypeEquiv fun _ ↦
    (isOptimalCoupling_map_iff e f cost cost' hcost).symm

@[simp]
theorem optimalCouplingEquiv_apply (e : α ≃ᵐ α') (f : β ≃ᵐ β')
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (e x) (f y) = cost x y)
    (μ : Measure α) (ν : Measure β) (π : {π // IsOptimalCoupling cost μ ν π}) :
    (optimalCouplingEquiv e f cost cost' hcost μ ν π).val = π.val.map (e.prodCongr f) :=
  rfl

/-- Genuine extended-distance optimality is unchanged by a measurable isometry equivalence. -/
theorem isOptimalCoupling_map_edist_iff [PseudoEMetricSpace α] [PseudoEMetricSpace α']
    (e : α ≃ᵐ α') (he : Isometry e)
    {μ ν : Measure α} {π : Measure (α × α)} :
    IsOptimalCoupling edist (μ.map e) (ν.map e) (π.map (e.prodCongr e)) ↔
      IsOptimalCoupling edist μ ν π :=
  isOptimalCoupling_map_iff e e edist edist (fun x y ↦ he.edist_eq x y)

end OTSelector
