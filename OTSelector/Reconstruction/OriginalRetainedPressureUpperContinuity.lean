import OTSelector.MeasureTheory.RetainedMarginalVariation
import OTSelector.Reconstruction.OriginalMarkedPressureVariationUpperContinuity

/-! Actual original retained pairings inherit the true pressure upper bound
from full original marginal continuity and their vanishing original loss.
The retained coupling selection itself need not vary continuously. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

/-- Original varying marginals and arbitrary actual retained subpairings
supply all law-continuity inputs of the true pressure upper theorem. The
same coarse repair applies before the retained laws or fine bins are chosen. -/
theorem exists_legalMarkedPressure_upper_of_original_retained_variation
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableEq A] [MeasurableEq B]
    (q : ℕ) (hq : 4 < q) {range : Set ℝ} (hrange : MeasurableSet range) {gap : ℝ}
    (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (source : A → ℝ) (target : B → ℝ) (hs : Measurable source) (ht : Measurable target)
    (αn : ℕ → ProbabilityMeasure A) (βn : ℕ → ProbabilityMeasure B)
    (α : ProbabilityMeasure A) (β : ProbabilityMeasure B)
    (hvariationS : Tendsto (fun n ↦
      ((αn n : Measure A).toSignedMeasure - (α : Measure A).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0))
    (hvariationT : Tendsto (fun n ↦
      ((βn n : Measure B).toSignedMeasure - (β : Measure B).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0))
    (πref : ProbabilityMeasure (A × B))
    (hπref : Vlasov.IsCoupling (πref : Measure (A × B)) (α : Measure A) (β : Measure B))
    (hIref : ∀ᵐ p ∂(πref : Measure (A × B)), source p.1 ∈ range ∧ target p.2 ∈ range)
    (hgapRef : ∀ᵐ p ∂(πref : Measure (A × B)), gap ≤ target p.2 - source p.1)
    (hsepRef : ∀ᵐ p ∂(α : Measure A).prod (β : Measure B), gap ≤ |target p.2 - source p.1|)
    (π : ℕ → ProbabilityMeasure (A × B))
    (hπ : ∀ n, Vlasov.IsCoupling (π n : Measure (A × B)) (αn n : Measure A) (βn n : Measure B))
    (hI : ∀ n, ∀ᵐ p ∂(π n : Measure (A × B)), source p.1 ∈ range ∧ target p.2 ∈ range)
    (hgapLaw : ∀ n, ∀ᵐ p ∂(π n : Measure (A × B)), gap ≤ target p.2 - source p.1)
    (hsep : ∀ n, ∀ᵐ p ∂(αn n : Measure A).prod (βn n : Measure B),
      gap ≤ |target p.2 - source p.1|)
    (χ : ℕ → Measure (A × B)) (hχ : ∀ n, χ n ≤ (π n : Measure (A × B)))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ1 : ∀ n, δ n < 1)
    (hmass : ∀ n, 1 - δ n ≤ (χ n).real univ)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) :
    ∃ πret : ℕ → ProbabilityMeasure (A × B),
      (∀ n, (πret n : Measure (A × B)) = normalizedFiniteLaw (χ n)) ∧
    ∃ pref : ℝ → ℝ, ∃ p : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ legalMarkedScalePressure q source target
        (α : Measure A) (β : Measure B) kin probe L t) atTop (𝓝 (pref t))) ∧
      (∀ n t, Tendsto (fun L ↦ legalMarkedScalePressure q source target
        ((πret n).map measurable_fst.aemeasurable : Measure A)
        ((πret n).map measurable_snd.aemeasurable : Measure B) kin probe L t) atTop (𝓝 (p n t))) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop, p n t < pref t + ε := by
  letI : ∀ n, IsFiniteMeasure (χ n) := fun n ↦ isFiniteMeasure_of_le (π n : Measure (A × B)) (hχ n)
  have hpos n : 0 < (χ n).real univ := (sub_pos.mpr (hδ1 n)).trans_le (hmass n)
  letI : ∀ n, IsProbabilityMeasure (normalizedFiniteLaw (χ n)) :=
    fun n ↦ normalizedFiniteLaw_probability (χ n) (hpos n)
  let πret : ℕ → ProbabilityMeasure (A × B) := fun n ↦ ⟨normalizedFiniteLaw (χ n),inferInstance⟩
  let αret : ℕ → ProbabilityMeasure A := fun n ↦ (πret n).map measurable_fst.aemeasurable
  let βret : ℕ → ProbabilityMeasure B := fun n ↦ (πret n).map measurable_snd.aemeasurable
  have hdata : ∀ᶠ n in atTop, χ n ≤ (π n : Measure (A × B)) ∧
      0 ≤ δ n ∧ δ n < 1 ∧ 1 - δ n ≤ (χ n).real univ :=
    Filter.Eventually.of_forall fun n ↦ ⟨hχ n,hδ0 n,hδ1 n,hmass n⟩
  have hvarS : Tendsto (fun n ↦
      ((αret n : Measure A).toSignedMeasure - (α : Measure A).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
    apply tendsto_totalVariation_normalized_retained_observation
      (fun n ↦ (π n : Measure (A × B))) χ Prod.fst measurable_fst (α : Measure A)
      atTop δ hδ _ hdata
    simpa only [(hπ _).1] using hvariationS
  have hvarT : Tendsto (fun n ↦
      ((βret n : Measure B).toSignedMeasure - (β : Measure B).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
    apply tendsto_totalVariation_normalized_retained_observation
      (fun n ↦ (π n : Measure (A × B))) χ Prod.snd measurable_snd (β : Measure B)
      atTop δ hδ _ hdata
    simpa only [(hπ _).2] using hvariationT
  have hac n : normalizedFiniteLaw (χ n) ≪ (π n : Measure (A × B)) := by
    exact (Measure.absolutelyContinuous_of_le (hχ n)).smul_left _
  have hIret n : ∀ᵐ p ∂(πret n : Measure (A × B)), source p.1 ∈ range ∧ target p.2 ∈ range :=
    (hac n).ae_le (hI n)
  have hgapRet n : ∀ᵐ p ∂(πret n : Measure (A × B)), gap ≤ target p.2 - source p.1 :=
    (hac n).ae_le (hgapLaw n)
  have hsepRet n : ∀ᵐ p ∂(αret n : Measure A).prod (βret n : Measure B),
      gap ≤ |target p.2 - source p.1| := by
    have hS : (αret n : Measure A) ≪ (αn n : Measure A) := by
      change (normalizedFiniteLaw (χ n)).map Prod.fst ≪ _
      rw [← (hπ n).1]
      exact (hac n).map measurable_fst
    have hT : (βret n : Measure B) ≪ (βn n : Measure B) := by
      change (normalizedFiniteLaw (χ n)).map Prod.snd ≪ _
      rw [← (hπ n).2]
      exact (hac n).map measurable_snd
    exact (hS.prod hT).ae_le (hsep n)
  have hπret n : Vlasov.IsCoupling (πret n : Measure (A × B))
      (αret n : Measure A) (βret n : Measure B) := ⟨rfl,rfl⟩
  obtain ⟨pref,p,href,hpt,hupper⟩ := exists_legalMarkedPressure_upper_of_original_variation
    q hq hrange coarse hgap source target hs ht αret βret α β hvarS hvarT
    πref hπref hIref hgapRef hsepRef πret hπret hIret hgapRet hsepRet
    hC hG kin hk hkn hkb hhom probe hp hpb
  exact ⟨πret,fun _ ↦ rfl,pref,p,href,hpt,hupper⟩

end OTSelector.Reconstruction
