import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneNormalized
import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedLimit
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureLimit

/-!
# Actual legal finite pressure produces a Haar-rooted stationary pair Palm law

The original independent marked Poisson clouds carry their canonical legal
maximum-cardinality signed optimum. Dividing its literal original edge measure
by the original volume supplies the mass and energy inputs of Haar compactness.
A bounded tail of the proved actual finite pressure limit is chosen internally.
No candidate scene, measurable optimum, tightness, or stationarity is supplied.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalOptimalPalmLimitLocalPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalOptimalPalmLimitLocalNonempty (q : ℕ) : Nonempty
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := ⟨⟨0, inferInstance⟩⟩

/-- The actual canonical legal optimum, rooted uniformly throughout its whole
original physical box after deterministic centering. -/
def legalMarkedOptimalRootedSceneLaw (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t L : ℝ) (hL : 0 < L) :
    ProbabilityMeasure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)) := by
  haveI : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  exact physicalSceneRootedLocalSceneLaw
    (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)))
    (legalMarkedNormalizedOptimalPlan q L kin g t) (legalMarkedNormalizedOptimalPlan q L kin g t)
    (measurable_legalMarkedNormalizedOptimalPlan q L hkin hg t)
    (measurable_legalMarkedNormalizedOptimalPlan q L hkin hg t)
    (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
    Prod.snd measurable_snd (L ^ q) (pow_pos hL q)
    (haarRootCube (Fin q) (haarRootRadius q (L ^ q)))
    (by simpa only [Fintype.card_fin] using
      volume_haarRootCube_radius (Fin q) (by simpa only [Fintype.card_fin] using hq) (pow_pos hL q))

/-- The root cube of the actual canonical optimizer is exactly its full
centered original box, with no overlapping-volume restriction. -/
theorem haarRootRadius_legalMarked_scale (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 ≤ L) :
    haarRootRadius q (L ^ q) = L / 2 := by
  rw [haarRootRadius, one_div, Real.pow_rpow_inv_natCast hL hq.ne']

/-- A genuine actual legal pressure limit produces stationary weak limits of
its own canonical finite optimal plans, with actual qdim Palm mass at most one
and the original kinetic-energy bound. Prescribed independent input retention
is a separate marginal assertion, not included in this compactness conclusion. -/
theorem exists_stationary_cubePalm_of_legalMarkedScalePressure_limit
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Continuous (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t p : ℝ)
    (hp : Tendsto (fun L ↦ legalMarkedScalePressure q id id α β kin g L t) atTop (𝓝 p))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (L : ℕ → ℝ) (hL : ∀ k, 0 < L k), Tendsto L atTop atTop ∧
      ∃ Q : ProbabilityMeasure
          (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)),
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k ↦ legalMarkedOptimalRootedSceneLaw q hq α β kin hk.measurable g hg t
          (L (φ k)) (hL (φ k))) atTop (𝓝 Q) ∧
        (∀ v : Fin q → ℝ, MeasurePreserving (physicalSceneReroot v)
          (Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
          (Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ∧
        cubePalm (Fin q) (physicalScenePairCampbell
          (Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) univ ≤ 1 ∧
        (∫⁻ m, ENNReal.ofReal (kin m.1.1 m.1.2 m.2) ∂cubePalm (Fin q)
          (physicalScenePairCampbell (Q : Measure
            (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) ≤
              ENNReal.ofReal (p + ε + |t| * G) ∧
        physicalScenePairCampbell (Q : Measure
          (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
          (volume : Measure (Fin q → ℝ)).prod (cubePalm (Fin q) (physicalScenePairCampbell
            (Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) := by
  have hev : ∀ᶠ L in atTop, legalMarkedScalePressure q id id α β kin g L t < p + ε :=
    hp.eventually (eventually_lt_nhds (lt_add_of_pos_right p hε))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  let L (k : ℕ) : ℝ := (k : ℝ) + max R₀ 1
  have hL (k) : 0 < L k := by
    dsimp [L]
    have hR : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
    positivity
  have hLlarge : Tendsto L atTop atTop := tendsto_atTop_add_const_right atTop (max R₀ 1) tendsto_natCast_atTop_atTop
  let P (k : ℕ) := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal ((L k) ^ q))
  let Γ (k : ℕ) := legalMarkedNormalizedOptimalPlan q (L k) kin g t
  have : ∀ k, IsProbabilityMeasure (P k) := fun _ ↦ inferInstance
  have : ∀ k ω, IsFiniteMeasure (Γ k ω) := fun k ω ↦
    isFiniteMeasure_legalMarkedNormalizedOptimalPlan q (hL k) kin g t ω
  have hΓ (k) : Measurable (Γ k) :=
    measurable_legalMarkedNormalizedOptimalPlan q (L k) hk.measurable hg t
  have hmass (k) : (∫⁻ ω, Γ k ω univ ∂P k) ≤ 1 :=
    lintegral_legalMarkedNormalizedOptimalPlan_univ_le_one q (hL k) α β kin g t
  have henergy (k) : (∫⁻ ω, ∫⁻ e,
      ENNReal.ofReal (kin e.1.2 e.2.2
        (legalMarkedCenteredCoordinate q (L k) e.2 - legalMarkedCenteredCoordinate q (L k) e.1))
      ∂Γ k ω ∂P k) ≤ ENNReal.ofReal (p + ε + |t| * G) := by
    have h := lintegral_legalMarkedNormalizedOptimalPlan_kinetic_le q hq (hL k)
      α β hC hG hk.measurable hkn hkb hhom hg hgb t
    have hpressure : legalMarkedScalePressure q id id α β kin g (L k) t ≤ p + ε := by
      apply (hR₀ (L k) ?_).le
      dsimp [L]
      exact (le_max_left R₀ 1).trans (le_add_of_nonneg_left (Nat.cast_nonneg k))
    have hpressure' : legalMarkedScalePressure q id id α β kin g (L k) t + |t| * G ≤
        p + ε + |t| * G := by linarith
    have he := h.trans (ENNReal.ofReal_le_ofReal hpressure')
    simpa only [legalMarkedCenteredCoordinate, sub_sub_sub_cancel_right,
      legalMarkedPhysicalKineticEdge] using he
  have hNlarge : Tendsto (fun k ↦ (L k) ^ q) atTop atTop :=
    (tendsto_pow_atTop hq.ne').comp hLlarge
  obtain ⟨Q, φ, hφ, hw, hs, hm, he, hc⟩ :=
    exists_stationary_cubePalm_of_original_finitePlans
      (ι := Fin q) (by simpa only [Fintype.card_fin] using hq)
      P Γ hΓ (fun k ↦ legalMarkedCenteredCoordinate q (L k))
      (fun k ↦ measurable_legalMarkedCenteredCoordinate q (L k)) Prod.snd measurable_snd
      (fun k ↦ (L k) ^ q) (fun k ↦ pow_pos (hL k) q) hNlarge 1 ENNReal.one_ne_top hmass
      (fun m ↦ kin m.1.1 m.1.2 m.2) hk (fun m ↦ hkn _ _ _)
      (ENNReal.ofReal (p + ε + |t| * G)) henergy
  refine ⟨L, hL, hLlarge, Q, φ, hφ, ?_, hs, hm, he, hc⟩
  simpa only [legalMarkedOptimalRootedSceneLaw, Fintype.card_fin, P, Γ] using hw

end OTSelector.Reconstruction
