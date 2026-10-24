import OTSelector.Reconstruction.OriginalMarkedPressureVariationUpperContinuity
import OTSelector.Reconstruction.OriginalLegalPressureRelativeStability
import OTSelector.Analysis.RelativeErrorUpperLimit

/-! Actual conditional-law and relative geometric/probe variation are assembled
at the true continuous original thermodynamic pressure, with one coarse repair. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

/-- Simultaneous variation of original continuous marginal laws, actual
geometric kernels, and physical probes preserves the true pressure upper
limit. Every pressure and the common Lipschitz control are produced internally.
Kinetic growth may have a different finite constant at every stage. -/
theorem exists_legalMarkedPressure_upper_of_original_law_and_geometry
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
    (reference : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ reference p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ reference a b v)
    (hkb : ∀ a b v, |reference a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      reference a b (fun l ↦ c * v l) = c ^ 2 * reference a b v)
    (refProbe : A → B → ℝ) (hp : Measurable (Function.uncurry refProbe))
    (hpb : ∀ a b, |refProbe a b| ≤ G)
    (kin : ℕ → A → B → (Fin q → ℝ) → ℝ) (probe : ℕ → A → B → ℝ)
    (Kn : ℕ → ℝ) (hKn : ∀ n, 0 ≤ Kn n)
    (hknm : ∀ n, Measurable (Function.uncurry (fun p : A × B ↦ kin n p.1 p.2)))
    (hknn : ∀ n a b v, 0 ≤ kin n a b v)
    (hknb : ∀ n a b v, |kin n a b v| ≤ Kn n * ∑ l, v l ^ 2)
    (hknhom : ∀ n a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin n a b (fun l ↦ c * v l) = c ^ 2 * kin n a b v)
    (hpnm : ∀ n, Measurable (Function.uncurry (probe n)))
    (hpnb : ∀ n a b, |probe n a b| ≤ G)
    (hgeometry : ∀ ε > 0, ε ≤ 1 → ∀ η > 0, ∀ᶠ n in atTop,
      ∀ a b, source a < target b →
        (∀ v, |kin n a b v - reference a b v| ≤ ε * reference a b v) ∧
        |probe n a b - refProbe a b| ≤ η) :
    ∃ pref : ℝ → ℝ, ∃ p : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ legalMarkedScalePressure q source target
        (α : Measure A) (β : Measure B) reference refProbe L t) atTop (𝓝 (pref t))) ∧
      (∀ n t, Tendsto (fun L ↦ legalMarkedScalePressure q source target
        (αn n : Measure A) (βn n : Measure B) (kin n) (probe n) L t) atTop (𝓝 (p n t))) ∧
      (∀ n, LipschitzWith ⟨G,hG⟩ (p n)) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop, p n t < pref t + ε := by
  obtain ⟨pref,r,href,hrt,hrupper⟩ := exists_legalMarkedPressure_upper_of_original_variation
    q hq hrange coarse hgap source target hs ht αn βn α β hvariationS hvariationT
    πref hπref hIref hgapRef hsepRef π hπ hI hgapLaw hsep
    hC hG reference hk hkn hkb hhom refProbe hp hpb
  have hstage n := exists_legalMarkedScalePressure_limit_of_scalarBins coarse hgap hrange
    source target hs ht (π n : Measure (A × B)) (αn n : Measure A) (βn n : Measure B)
    (hπ n) (hI n) (hgapLaw n) (hsep n) q hq (hKn n) hG (hknm n)
    (hknn n) (hknb n) (hknhom n) (hpnm n) (hpnb n)
  choose p hpt _hc hLip using hstage
  refine ⟨pref,p,href,hpt,hLip,?_⟩
  intro t ε hε
  apply eventually_pressure_lt_of_small_relative_errors atTop (fun n ↦ p n t)
    (fun n ↦ r n t) (pref t) (|t| * G) (hrupper t) _ ε hε
  intro e he he1 d hd
  let η := d / (|t| + 1)
  have hη : 0 < η := div_pos hd (by positivity)
  have hscale : |t| * η ≤ d := by
    dsimp only [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < |t| + 1 by positivity)).mpr
    nlinarith only [hd]
  filter_upwards [hgeometry e he he1 η hη] with n hn
  have herror := legalMarkedScalePressure_limits_abs_sub_le_relative q source target hs ht
    (αn n : Measure A) (βn n : Measure B) (hKn n) hC hG hG
    he.le he1 hη.le (kin n) reference (hknm n) hk (hknb n) hkb
    (probe n) refProbe (hpnm n) hp (hpnb n) hpb
    (fun a b hab ↦ (hn a b hab).1) (fun a b hab ↦ (hn a b hab).2)
    (p n) (r n) (hpt n) (hrt n) t
  linarith only [herror,hscale]

end OTSelector.Reconstruction
