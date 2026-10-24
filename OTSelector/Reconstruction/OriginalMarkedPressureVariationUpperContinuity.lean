import OTSelector.Probability.VariationSamplingSequence
import OTSelector.Reconstruction.OriginalMarkedPressureUpperLawContinuity

/-! Actual original probability-law variation supplies all common-sampling
inputs of the true thermodynamic pressure upper-continuity theorem. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

/-- Original law variation, original feasible pairings, one coarse clock gap,
and the actual kernel data produce all thermodynamic pressures and their upper
continuity. Sampling couplings are constructed internally from the true laws. -/
theorem exists_legalMarkedPressure_upper_of_original_variation
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
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) :
    ∃ pref : ℝ → ℝ, ∃ p : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ legalMarkedScalePressure q source target
        (α : Measure A) (β : Measure B) kin probe L t) atTop (𝓝 (pref t))) ∧
      (∀ n t, Tendsto (fun L ↦ legalMarkedScalePressure q source target
        (αn n : Measure A) (βn n : Measure B) kin probe L t) atTop (𝓝 (p n t))) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop, p n t < pref t + ε := by
  obtain ⟨κS,hSf,hSs,hSdis⟩ := exists_original_probability_variation_sampling_sequence αn α hvariationS
  obtain ⟨κT,hTf,hTs,hTdis⟩ := exists_original_probability_variation_sampling_sequence βn β hvariationT
  have hαI : ∀ᵐ a ∂(α : Measure A), source a ∈ range := by
    rw [← hπref.1]
    exact (ae_map_iff measurable_fst.aemeasurable (hs hrange)).mpr (hIref.mono fun _ h ↦ h.1)
  have hαnI n : ∀ᵐ a ∂(αn n : Measure A), source a ∈ range := by
    rw [← (hπ n).1]
    exact (ae_map_iff measurable_fst.aemeasurable (hs hrange)).mpr ((hI n).mono fun _ h ↦ h.1)
  have hsource n : ∀ᵐ a ∂(κS n : Measure (A × A)), source a.1 ∈ range ∧ source a.2 ∈ range := by
    have hh₀ : ∀ᵐ a ∂(κS n : Measure (A × A)), source a.1 ∈ range := by
      apply (ae_map_iff measurable_fst.aemeasurable (hs hrange)).mp
      rw [hSf n]
      exact hαnI n
    have hh₁ : ∀ᵐ a ∂(κS n : Measure (A × A)), source a.2 ∈ range := by
      apply (ae_map_iff measurable_snd.aemeasurable (hs hrange)).mp
      rw [hSs n]
      exact hαI
    exact hh₀.and hh₁
  have hsepMeas : MeasurableSet {p : A × B | gap ≤ |target p.2 - source p.1|} :=
    measurableSet_le measurable_const ((ht.comp measurable_snd).sub (hs.comp measurable_fst)).abs
  have hsepCoupled n : ∀ᵐ p ∂(κS n : Measure (A × A)).prod (κT n : Measure (B × B)),
      gap ≤ |target p.2.1 - source p.1.1| ∧ gap ≤ |target p.2.2 - source p.1.2| := by
    have hh₀ : ∀ᵐ p ∂(κS n : Measure (A × A)).prod (κT n : Measure (B × B)),
        gap ≤ |target p.2.1 - source p.1.1| := by
      apply (ae_map_iff (measurable_fst.prodMap measurable_fst).aemeasurable hsepMeas).mp
      rw [← Measure.map_prod_map _ _ measurable_fst measurable_fst,hSf n,hTf n]
      exact hsep n
    have hh₁ : ∀ᵐ p ∂(κS n : Measure (A × A)).prod (κT n : Measure (B × B)),
        gap ≤ |target p.2.2 - source p.1.2| := by
      apply (ae_map_iff (measurable_snd.prodMap measurable_snd).aemeasurable hsepMeas).mp
      rw [← Measure.map_prod_map _ _ measurable_snd measurable_snd,hSs n,hTs n]
      exact hsepRef
    exact hh₀.and hh₁
  have hdis : Tendsto (fun n ↦
      ((κS n : Measure (A × A)) {p | p.1 ≠ p.2}).toReal +
      ((κT n : Measure (B × B)) {p | p.1 ≠ p.2}).toReal) atTop (𝓝 0) := by
    simpa only [add_zero] using hSdis.add hTdis
  have hπcoupled n : Vlasov.IsCoupling (π n : Measure (A × B))
      ((κS n).map measurable_fst.aemeasurable : Measure A)
      ((κT n).map measurable_fst.aemeasurable : Measure B) := by
    simpa only [ProbabilityMeasure.toMeasure_map,hSf n,hTf n] using hπ n
  obtain ⟨pref,p,href,hpt,hupper⟩ := exists_legalMarkedPressure_upper_law_continuity q hq hrange coarse hgap
    source target hs ht κS κT (α : Measure A) (β : Measure B) hSs hTs hsource hsepCoupled hdis
    πref hπref hIref hgapRef π hπcoupled hI hgapLaw hC hG kin hk hkn hkb hhom probe hp hpb
  refine ⟨pref,p,href,?_,hupper⟩
  intro n t
  simpa only [ProbabilityMeasure.toMeasure_map,hSf n,hTf n] using hpt n t

end OTSelector.Reconstruction
