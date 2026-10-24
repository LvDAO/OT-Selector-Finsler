import OTSelector.Reconstruction.MarkedStationaryValueLegalAllowedEnergyPalm

/-!
# Continuous energy minorants of the actual original legal cost

A continuous nonnegative test need only be dominated by the original shifted
signed cost on actual original legal clock pairs. This permits compact
interior clock cutoffs while retaining the same finite optima, pressure and
joint Palm limit.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalDominatedPalmEnergyInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalDominatedPalmEnergyPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Every continuous actual legal cost minorant has the original finite
pressure energy bound on the very same canonical optimizer. -/
theorem lintegral_legalMarkedNormalizedOptimalPlan_continuous_dominated_shifted_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (F : C(PhysicalPairPalmMark (Fin q), ℝ))
    (hF : ∀ m : PhysicalPairPalmMark (Fin q), m.1 ∈ K →
      F m ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (F ((e.1.2, e.2.2), e.2.1 - e.1.1))
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤
      ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) := by
  apply le_trans ?_ (lintegral_legalMarkedNormalizedOptimalPlan_shifted_signed_le q hq hL
    α β hC hG hk hkn hkb hhom hg hgb t)
  apply lintegral_mono_ae
  filter_upwards [ae_clockPair_mem_legalMarkedNormalizedOptimalPlan_of_forward q L α β kin g t
    hA hB hα hβ hlegal] with ω hω
  apply lintegral_mono_ae
  filter_upwards [hω] with e he
  exact ENNReal.ofReal_le_ofReal (hF ((e.1.2, e.2.2), e.2.1 - e.1.1) he)

/-- The actual weak scene keeps every continuous nonnegative legal cost
minorant below its original limiting pressure, without selecting a new Palm. -/
theorem lintegral_cubePalm_legalMarkedInputPairLaw_continuous_dominated_shifted_le
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t p : ℝ)
    (hp : Tendsto (fun R ↦ legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 p))
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (F : C(PhysicalPairPalmMark (Fin q), ℝ)) (hFn : ∀ m, 0 ≤ F m)
    (hF : ∀ m : PhysicalPairPalmMark (Fin q), m.1 ∈ K →
      F m ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    (∫⁻ m, ENNReal.ofReal (F m) ∂cubePalm (Fin q) (physicalScenePairCampbell
      (legalMarkedInputPairLaw q Q :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) ≤
      ENNReal.ofReal (p + |t| * G) := by
  have hpairweak := legalMarkedInputPairLaw_tendsto q hq α β kin hk g hg t L hL hweak
  have hεbound (ε : ℝ) (hε : 0 < ε) :
      (∫⁻ m, ENNReal.ofReal (F m) ∂cubePalm (Fin q) (physicalScenePairCampbell
        (legalMarkedInputPairLaw q Q :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) ≤
        ENNReal.ofReal (p + ε + |t| * G) := by
    have hev : ∀ᶠ k in atTop, legalMarkedScalePressure q id id α β kin g (L k) t ≤ p + ε :=
      ((hp.comp hlarge).eventually (eventually_lt_nhds (lt_add_of_pos_right p hε))).mono
        (fun k hk ↦ hk.le)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    apply lintegral_cubePalm_le_of_weak_energy_density_bound
      (fun k ↦ legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t (L (k + N)) (hL (k + N)))
      (hpairweak.comp (tendsto_add_atTop_nat N)) F F.continuous hFn
      (ENNReal.ofReal (p + ε + |t| * G))
    intro U hU k
    have hread := lintegral_legalMarkedOptimalRootedSceneLaw_sourceReadout_le q hq (hL (k + N))
      α β kin hk g hg t F.continuous.measurable.ennreal_ofReal hU.measurableSet
    have hglobal := lintegral_legalMarkedNormalizedOptimalPlan_continuous_dominated_shifted_le q hq (hL (k + N))
      α β hC hG hk hkn hkb hhom hg hgb t hA hB hα hβ hlegal F hF
    exact hread.trans (mul_le_mul_right (hglobal.trans
      (ENNReal.ofReal_le_ofReal (add_le_add (hN (k + N) (by omega)) le_rfl))) _)
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (p + 1 / ((n : ℝ) + 1) + |t| * G))
      atTop (𝓝 (ENNReal.ofReal (p + |t| * G))) := by
    have hr : Tendsto (fun n : ℕ ↦ p + 1 / ((n : ℝ) + 1) + |t| * G)
        atTop (𝓝 (p + |t| * G)) := by
      simpa only [add_zero] using
        (((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ p) atTop (𝓝 p)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).add_const (|t| * G))
    exact (ENNReal.continuous_ofReal.tendsto (p + |t| * G)).comp hr
  exact ge_of_tendsto hlim (.of_forall (fun n ↦ hεbound _ (by positivity)))

end OTSelector.Reconstruction
