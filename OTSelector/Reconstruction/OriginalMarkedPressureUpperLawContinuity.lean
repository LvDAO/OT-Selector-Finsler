import OTSelector.Reconstruction.OriginalMarkedPressureLawConvergence
import OTSelector.Reconstruction.OriginalPressureBoxUpperContinuity
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureLimit

/-! True thermodynamic upper continuity under original common-sampling law
perturbations. The true pressures, finite-box convergence and one uniform
coarse parent repair are all supplied by the original marked population. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

/-- A true original legal pressure limit obeys every fixed-box parent upper. -/
theorem legalMarkedScalePressure_limit_le_of_block_bound
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    (C G t K p : ℝ)
    (hp : Tendsto (fun R ↦ legalMarkedScalePressure q source target α β kin probe R t) atTop (𝓝 p))
    (hblock : ∀ m : ℕ, 0 < m → ∀ L : ℝ, 0 < L →
      legalMarkedScalePressure q source target α β kin probe ((m : ℝ) * L) t ≤
        legalMarkedScalePressure q source target α β kin probe L t + gridRepairError q K C G t L)
    {L : ℝ} (hL : 0 < L) :
    p ≤ legalMarkedScalePressure q source target α β kin probe L t + gridRepairError q K C G t L := by
  have hscale : Tendsto (fun m : ℕ ↦ (m : ℝ) * L) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hL
  apply le_of_tendsto (hp.comp hscale)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact hblock m (by omega) L hL

/-- Original feasible continuous populations and vanishing actual sampling
changes produce their true thermodynamic pressures and the required upper
continuity. No thermodynamic pressure continuity is assumed. -/
theorem exists_legalMarkedPressure_upper_law_continuity
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableEq A] [MeasurableEq B]
    (q : ℕ) (hq : 4 < q) {range : Set ℝ} (hrange : MeasurableSet range) {gap : ℝ}
    (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (source : A → ℝ) (target : B → ℝ) (hs : Measurable source) (ht : Measurable target)
    (κS : ℕ → ProbabilityMeasure (A × A)) (κT : ℕ → ProbabilityMeasure (B × B))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hmapS : ∀ n, (κS n : Measure (A × A)).map Prod.snd = α)
    (hmapT : ∀ n, (κT n : Measure (B × B)).map Prod.snd = β)
    (hsource : ∀ n, ∀ᵐ a ∂(κS n : Measure (A × A)), source a.1 ∈ range ∧ source a.2 ∈ range)
    (hsep : ∀ n, ∀ᵐ p ∂(κS n : Measure (A × A)).prod (κT n : Measure (B × B)),
      gap ≤ |target p.2.1 - source p.1.1| ∧ gap ≤ |target p.2.2 - source p.1.2|)
    (hdisagreement : Tendsto (fun n ↦
      ((κS n : Measure (A × A)) {p | p.1 ≠ p.2}).toReal +
      ((κT n : Measure (B × B)) {p | p.1 ≠ p.2}).toReal) atTop (𝓝 0))
    (πref : ProbabilityMeasure (A × B)) (hπref : Vlasov.IsCoupling (πref : Measure (A × B)) α β)
    (hIref : ∀ᵐ p ∂(πref : Measure (A × B)), source p.1 ∈ range ∧ target p.2 ∈ range)
    (hgapRef : ∀ᵐ p ∂(πref : Measure (A × B)), gap ≤ target p.2 - source p.1)
    (π : ℕ → ProbabilityMeasure (A × B))
    (hπ : ∀ n, Vlasov.IsCoupling (π n : Measure (A × B))
      ((κS n).map measurable_fst.aemeasurable : Measure A)
      ((κT n).map measurable_fst.aemeasurable : Measure B))
    (hI : ∀ n, ∀ᵐ p ∂(π n : Measure (A × B)), source p.1 ∈ range ∧ target p.2 ∈ range)
    (hgapLaw : ∀ n, ∀ᵐ p ∂(π n : Measure (A × B)), gap ≤ target p.2 - source p.1)
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
      (∀ t, Tendsto (fun L ↦ legalMarkedScalePressure q source target α β kin probe L t)
        atTop (𝓝 (pref t))) ∧
      (∀ n t, Tendsto (fun L ↦ legalMarkedScalePressure q source target
        ((κS n).map measurable_fst.aemeasurable : Measure A)
        ((κT n).map measurable_fst.aemeasurable : Measure B) kin probe L t) atTop (𝓝 (p n t))) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop, p n t < pref t + ε := by
  let αn := fun n ↦ (κS n).map measurable_fst.aemeasurable
  let βn := fun n ↦ (κT n).map measurable_fst.aemeasurable
  have hsepMeas : MeasurableSet {p : A × B | gap ≤ |target p.2 - source p.1|} :=
    measurableSet_le measurable_const ((ht.comp measurable_snd).sub (hs.comp measurable_fst)).abs
  have hsepStage n : ∀ᵐ p ∂(αn n : Measure A).prod (βn n : Measure B),
      gap ≤ |target p.2 - source p.1| := by
    have hh := (ae_map_iff (measurable_fst.prodMap measurable_fst).aemeasurable hsepMeas).mpr
      ((hsep n).mono fun _ hp ↦ hp.1)
    rw [← Measure.map_prod_map _ _ measurable_fst measurable_fst] at hh
    simpa only [αn,βn,ProbabilityMeasure.toMeasure_map] using hh
  have hsepRef : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1| := by
    have hh := (ae_map_iff (measurable_snd.prodMap measurable_snd).aemeasurable hsepMeas).mpr
      ((hsep 0).mono fun _ hp ↦ hp.2)
    rw [← Measure.map_prod_map _ _ measurable_snd measurable_snd,hmapS 0,hmapT 0] at hh
    exact hh
  obtain ⟨pref,href,_hcref,_hlref⟩ := exists_legalMarkedScalePressure_limit_of_scalarBins coarse hgap
    hrange source target hs ht (πref : Measure (A × B)) α β hπref hIref hgapRef hsepRef
    q hq hC hG hk hkn hkb hhom hp hpb
  have hstage n := exists_legalMarkedScalePressure_limit_of_scalarBins coarse hgap hrange
    source target hs ht (π n : Measure (A × B)) (αn n : Measure _) (βn n : Measure _)
    (hπ n) (hI n) (hgapLaw n) (hsepStage n) q hq hC hG hk hkn hkb hhom hp hpb
  choose p hpt _hc _hl using hstage
  refine ⟨pref,p,href,hpt,?_⟩
  intro t ε hε
  let K := legalGridRepairConstant q coarse.count (legalClockTypeCount coarse.count)
  apply eventually_pressure_lt_of_fixed_box_upper atTop (fun n ↦ p n t)
    (fun n L ↦ legalMarkedScalePressure q source target (αn n : Measure _) (βn n : Measure _) kin probe L t)
    (fun L ↦ legalMarkedScalePressure q source target α β kin probe L t)
    (fun L ↦ gridRepairError q K C G t L) (pref t) _ _ (href t)
    (tendsto_gridRepairError_atTop hq K C G t) ε hε
  · intro n L hL
    apply legalMarkedScalePressure_limit_le_of_block_bound q source target
      (αn n : Measure _) (βn n : Measure _) kin probe C G t K (p n t) (hpt n t) _ hL
    intro m hm L hL
    apply legalMarkedScalePressure_block_le_of_intensity_bound q m (by omega) hm
      source target (αn n : Measure _) (βn n : Measure _) kin probe C G t K _ hL
    intro r
    exact legalMarkedPressure_le_blockScale_add_repair coarse hgap hrange source target hs ht
      (π n : Measure (A × B)) (αn n : Measure _) (βn n : Measure _) (hπ n) (hI n) (hgapLaw n)
      (hsepStage n) q hq m hm r hC hG hk hkb hhom hp hpb t
  · intro L _hL
    exact tendsto_legalMarkedScalePressure_of_original_mark_couplings q coarse hgap source target
      hs ht κS κT α β hmapS hmapT hsource hsep hdisagreement hC hG kin hk hkb probe hp hpb L t

end OTSelector.Reconstruction
