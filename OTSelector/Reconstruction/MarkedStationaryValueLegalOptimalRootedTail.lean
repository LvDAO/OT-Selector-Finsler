import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneCollarTail
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalPalmLimit
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic

/-!
# Genuine displacement tails of the actual legal rooted optimizers

The rooted local plan is obtained from the same original legal finite optimum.
Haar averaging charges a bounded source window by its actual volume, while
original clock marginal domination and allowed-edge coercivity control the
unbounded target displacement.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalOptimalRootedTailLocalPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Every nonnegative paired-mark readout of the actual rooted optimum keeps
the original source-volume factor and the same original global finite plan. -/
theorem lintegral_legalMarkedOptimalRootedSceneLaw_sourceReadout_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {f : PhysicalPairPalmMark (Fin q) → ℝ≥0∞} (hf : Measurable f)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) :
    (∫⁻ scene, ∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ U},
      f (physicalPairAnchor e).2 ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q))
      ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤
      volume U * ∫⁻ ω, ∫⁻ e, f ((e.1.2, e.2.2), e.2.1 - e.1.1)
        ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)) := by
  have : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  have h := lintegral_physicalSceneRootedLocalSceneLaw_sourceEnergy_le
    (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)))
    (legalMarkedNormalizedOptimalPlan q L kin g t) (legalMarkedNormalizedOptimalPlan q L kin g t)
    (measurable_legalMarkedNormalizedOptimalPlan q L hk hg t)
    (measurable_legalMarkedNormalizedOptimalPlan q L hk hg t)
    (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
    Prod.snd measurable_snd (L ^ q) (pow_pos hL q)
    (haarRootCube (Fin q) (haarRootRadius q (L ^ q)))
    (by simpa only [Fintype.card_fin] using
      volume_haarRootCube_radius (Fin q) (by simpa only [Fintype.card_fin] using hq) (pow_pos hL q))
    hf U hU
  have hcoorddiff (e : LegalMarkedPhysicalEdge q) :
      legalMarkedCenteredCoordinate q L e.2 - legalMarkedCenteredCoordinate q L e.1 =
        e.2.1 - e.1.1 := by
    funext i
    simp only [legalMarkedCenteredCoordinate, Pi.sub_apply]
    ring
  simp_rw [hcoorddiff] at h
  exact h

/-- Actual root-window long edges obey the original clock-collar tail bound.
Coercivity is required only at actual forward clock pairs. -/
theorem lintegral_legalMarkedOptimalRootedSceneLaw_long_le_clock_collars
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
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hcoercive : ∀ a ∈ A, ∀ b ∈ B, a < b → ∀ v, c * ‖v‖ ^ 2 ≤ kin a b v)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) :
    (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖}
      ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤
      volume U * (α Aᶜ + β Bᶜ +
        ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) /
          ENNReal.ofReal (c * R ^ 2)) := by
  let f : PhysicalPairPalmMark (Fin q) → ℝ≥0∞ :=
    {m | R ≤ ‖m.2‖}.indicator (fun _ ↦ 1)
  have hlong : MeasurableSet {m : PhysicalPairPalmMark (Fin q) | R ≤ ‖m.2‖} := by
    exact measurableSet_le measurable_const measurable_snd.norm
  have hf : Measurable f := measurable_const.indicator hlong
  have h := lintegral_legalMarkedOptimalRootedSceneLaw_sourceReadout_le q hq hL
    α β kin hk g hg t hf hU
  have hglobal := lintegral_legalMarkedNormalizedOptimalPlan_long_le_clock_collars
    q hq hL α β hC hG hk hkn hkb hhom hg hgb t hA hB hc hR hcoercive
  have hread (Γ : Measure (LegalMarkedPhysicalEdge q)) :
      (∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ U},
        f (physicalPairAnchor e).2 ∂Γ) =
        Γ {e | e.1.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖} := by
    have hm : MeasurableSet {e : LegalMarkedPhysicalEdge q | R ≤ ‖e.2.1 - e.1.1‖} :=
      measurableSet_le measurable_const (measurable_snd.fst.sub measurable_fst.fst).norm
    change (∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ U},
      {e : LegalMarkedPhysicalEdge q | R ≤ ‖e.2.1 - e.1.1‖}.indicator (fun _ ↦ 1) e ∂Γ) = _
    rw [lintegral_indicator hm, lintegral_one, Measure.restrict_apply_univ,
      Measure.restrict_apply hm]
    congr 1
    ext e
    exact and_comm
  have hglobalread (Γ : Measure (LegalMarkedPhysicalEdge q)) :
      (∫⁻ e, f ((e.1.2, e.2.2), e.2.1 - e.1.1) ∂Γ) =
        Γ {e | R ≤ ‖e.2.1 - e.1.1‖} := by
    have hm : MeasurableSet {e : LegalMarkedPhysicalEdge q | R ≤ ‖e.2.1 - e.1.1‖} :=
      measurableSet_le measurable_const (measurable_snd.fst.sub measurable_fst.fst).norm
    change (∫⁻ e, {e : LegalMarkedPhysicalEdge q | R ≤ ‖e.2.1 - e.1.1‖}.indicator
      (fun _ ↦ 1) e ∂Γ) = _
    rw [lintegral_indicator hm, lintegral_one, Measure.restrict_apply_univ]
  simp_rw [hread, hglobalread] at h
  exact h.trans (mul_le_mul_of_nonneg_left hglobal bot_le)

/-- The actual pressure limit and a genuine compact positive coefficient field
produce uniform nonproper-target control for the same finite rooted optimizers.
The coercive constant is derived from that field; full clock mass comes from
the original input populations, before matching selection. -/
theorem exists_uniform_legalMarkedOptimalRootedSceneLaw_long_bound
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
    (hp : Tendsto (fun L ↦ legalMarkedScalePressure q id id α β kin g L t) atTop (𝓝 p))
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) (hUfin : volume U ≠ ∞) :
    ∃ L₀ : ℝ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R > 0, ∀ L : ℝ, ∀ hL : 0 < L, L₀ ≤ L →
      (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
        {e | e.1.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖}
        ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤ ε := by
  obtain ⟨c, hc, hcoercive⟩ := exists_uniform_matrixQuadratic_lower_bound hK hmatrix hpos
  have hkinlower : ∀ a ∈ A, ∀ b ∈ B, a < b → ∀ v, c * ‖v‖ ^ 2 ≤ kin a b v := by
    intro a ha b hb hab v
    rw [hactual (a, b) (hlegal a ha b hb hab) v]
    exact hcoercive (a, b) (hlegal a ha b hb hab) v
  have hpressure : ∀ᶠ L : ℝ in atTop, legalMarkedScalePressure q id id α β kin g L t ≤ p + 1 :=
    (hp.eventually (gt_mem_nhds (by linarith : p < p + 1))).mono (fun L hL ↦ hL.le)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hpressure
  refine ⟨L₀, fun ε hε ↦ ?_⟩
  have hden : Tendsto (fun R : ℝ ↦ ENNReal.ofReal (c * R ^ 2)) atTop (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop hc)
  have hdiv : Tendsto (fun R : ℝ ↦
      ENNReal.ofReal (p + 1 + |t| * G) / ENNReal.ofReal (c * R ^ 2)) atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      ENNReal.Tendsto.div tendsto_const_nhds (Or.inr (by simp)) hden
        (Or.inr ENNReal.ofReal_ne_top)
  have hterm : Tendsto (fun R : ℝ ↦ volume U *
      (ENNReal.ofReal (p + 1 + |t| * G) / ENNReal.ofReal (c * R ^ 2))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (ENNReal.continuousAt_const_mul (Or.inl hUfin)).tendsto.comp hdiv
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((ENNReal.tendsto_nhds_zero.mp hterm) ε hε)).exists
  refine ⟨R, hR, fun L hL hlarge ↦ ?_⟩
  have h := lintegral_legalMarkedOptimalRootedSceneLaw_long_le_clock_collars
    q hq hL α β hC hG hk hkn hkb hhom hg hgb t hA hB hc hR hkinlower hU
  rw [hα, hβ, zero_add, zero_add] at h
  apply h.trans (le_trans ?_ hsmall)
  gcongr
  exact hL₀ L hlarge

end OTSelector.Reconstruction
