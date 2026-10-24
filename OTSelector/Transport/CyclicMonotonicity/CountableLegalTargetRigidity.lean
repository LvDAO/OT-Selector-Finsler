import OTSelector.Transport.CyclicMonotonicity.CountableTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CountableLegalTwoCycleRigidity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CountableLegalTwoCycleRigidity`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.CountableLegalTwoCycleRigidity

**Conditions:** A measurable legal edge domain and countable targets; common legal source restrictions have measurable, atomless cost differences and the carried relation lies in the domain.

**Objects:** Almost-everywhere single-valued legal relation and equality of two plans with the same source marginal.

**Proof detail:** A two-target split and legal two-cycle monotonicity force the cost difference to be constant on its split set; atomlessness makes that set null, countability combines the exceptions, and single-valued measure uniqueness identifies both plans.

**Sources:** [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254), Appendix A.1, Theorem A.5, p. 242; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (generalization): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Countable-target rigidity on the legal edge domain

Only exchanges whose four edges belong to the actual cost domain are used.
Pairwise cost differences need to be atomless only on the common legal source
domain. This permits interleaving source and target marks and infinite mass.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {S J : Type*} [MeasurableSpace S] [Countable J]

/-- The two-cycle inequality is imposed only when the two crossed edges are
legal as well as the original edges in the carried relation. -/
def IsTwoCycleMonotoneOn (c : S → J → ℝ) (D Γ : Set (S × J)) : Prop :=
  ∀ x i y j, (x, i) ∈ Γ → (y, j) ∈ Γ → (x, j) ∈ D → (y, i) ∈ D →
    c x i + c y j ≤ c x j + c y i

/-- Sources at which both named target edges belong to the actual cost domain. -/
def commonLegalSource (D : Set (S × J)) (i j : J) : Set S :=
  {x | (x, i) ∈ D ∧ (x, j) ∈ D}

variable [MeasurableSpace J]

omit [Countable J] in
theorem measurableSet_commonLegalSource {D : Set (S × J)} (hD : MeasurableSet D)
    (i j : J) : MeasurableSet (commonLegalSource D i j) :=
  ((measurable_id.prodMk measurable_const) hD).inter
    ((measurable_id.prodMk measurable_const) hD)

/-- Overlap of two target fibers forces a constant cost difference on their
common legal domain. Restricted atomlessness therefore gives single-valuedness. -/
theorem IsTwoCycleMonotoneOn.ae_single_valued
    {c : S → J → ℝ} {D Γ : Set (S × J)} {μ : Measure S}
    (hcycle : IsTwoCycleMonotoneOn c D Γ) (hD : MeasurableSet D) (hsub : Γ ⊆ D)
    (hc : ∀ i j, AEMeasurable (fun x ↦ c x i - c x j)
      (μ.restrict (commonLegalSource D i j)))
    (hatom : ∀ i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource D i j)).map (fun x ↦ c x i - c x j))) :
    ∀ᵐ x ∂μ, ∀ i j, (x, i) ∈ Γ → (x, j) ∈ Γ → i = j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ _ _ ↦ hij)
  by_cases hex : ∃ x, (x, i) ∈ Γ ∧ (x, j) ∈ Γ
  · obtain ⟨x₀, hi₀, hj₀⟩ := hex
    let _ := hatom i j hij
    have hnull : (μ.restrict (commonLegalSource D i j))
        {x | c x i - c x j = c x₀ i - c x₀ j} = 0 := by
      have h := measure_singleton
        (μ := (μ.restrict (commonLegalSource D i j)).map (fun x ↦ c x i - c x j))
        (c x₀ i - c x₀ j)
      rw [Measure.map_apply_of_aemeasurable (hc i j) (measurableSet_singleton _)] at h
      exact h
    have hae := (ae_restrict_iff' (measurableSet_commonLegalSource hD i j)).mp
      (measure_eq_zero_iff_ae_notMem.mp hnull)
    filter_upwards [hae] with x hx hxi hxj
    have h₁ := hcycle x i x₀ j hxi hj₀ (hsub hxj) (hsub hi₀)
    have h₂ := hcycle x₀ i x j hi₀ hxj (hsub hj₀) (hsub hxi)
    exact False.elim (hx ⟨hsub hxi, hsub hxj⟩ (by linarith))
  · exact Filter.Eventually.of_forall (fun x hxi hxj ↦
      False.elim (hex ⟨x, hxi, hxj⟩))

variable [MeasurableSingletonClass J]

/-- Original same-source plans carried by the same legally monotone relation
agree; neither finiteness nor an all-pairs legal condition is required. -/
theorem IsTwoCycleMonotoneOn.measure_eq
    {c : S → J → ℝ} {D Γ : Set (S × J)} {μ : Measure S}
    (hcycle : IsTwoCycleMonotoneOn c D Γ) (hD : MeasurableSet D)
    (hΓ : MeasurableSet Γ) (hsub : Γ ⊆ D)
    (hc : ∀ i j, AEMeasurable (fun x ↦ c x i - c x j)
      (μ.restrict (commonLegalSource D i j)))
    (hatom : ∀ i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource D i j)).map (fun x ↦ c x i - c x j)))
    {π₀ π₁ : Measure (S × J)}
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (hcarried₀ : ∀ᵐ z ∂π₀, z ∈ Γ) (hcarried₁ : ∀ᵐ z ∂π₁, z ∈ Γ) : π₀ = π₁ :=
  measure_eq_of_common_ae_single_valued_relation hΓ
    (hcycle.ae_single_valued hD hsub hc hatom) hsource₀ hsource₁ hcarried₀ hcarried₁

/-- A legally monotone relation carrying the actual average forces equality of
the two original plans under only restricted cost-difference atomlessness. -/
theorem IsTwoCycleMonotoneOn.measure_eq_of_smul_add
    {c : S → J → ℝ} {D Γ : Set (S × J)} {μ : Measure S}
    (hcycle : IsTwoCycleMonotoneOn c D Γ) (hD : MeasurableSet D)
    (hΓ : MeasurableSet Γ) (hsub : Γ ⊆ D)
    (hc : ∀ i j, AEMeasurable (fun x ↦ c x i - c x j)
      (μ.restrict (commonLegalSource D i j)))
    (hatom : ∀ i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource D i j)).map (fun x ↦ c x i - c x j)))
    {π₀ π₁ : Measure (S × J)}
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    {a : ℝ≥0∞} (ha : a ≠ 0) (hcarried : ∀ᵐ z ∂a • (π₀ + π₁), z ∈ Γ) : π₀ = π₁ := by
  rw [Measure.ae_ennreal_smul_measure_iff ha, ae_add_measure_iff] at hcarried
  exact hcycle.measure_eq hD hΓ hsub hc hatom hsource₀ hsource₁ hcarried.1 hcarried.2

end OTSelector.Reconstruction

end
end
