import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalTargetTail
import OTSelector.Transport.CompactClockCoercivity

/-!
# Genuine focal-endpoint escape control for original legal optima

Interior collars are selected in the unchanged original two populations. Their
individual coercivity constants control spatial escape after the discarded
clock mass is made small. This removes any need for a uniform positive bound
on the whole closed clock support.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalFocalEscapePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A target clock collar is charged against the original target law before
matching selection, with the actual source-window volume factor. -/
theorem lintegral_legalMarkedOptimalRootedSceneLaw_sourceWindow_targetClock_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫⁻ scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q), (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ U ∧ e.2.2 ∈ B}
      ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
        (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤
      volume U * β B := by
  let f : PhysicalPairPalmMark (Fin q) → ℝ≥0∞ := {m | m.1.2 ∈ B}.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator (hB.preimage measurable_fst.snd)
  have h := lintegral_legalMarkedOptimalRootedSceneLaw_sourceReadout_le q hq hL α β kin hk g hg t hf hU
  have hread (Γ : Measure (LegalMarkedPhysicalEdge q)) :
      (∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ U},
        f (physicalPairAnchor e).2 ∂Γ) = Γ {e | e.1.1 ∈ U ∧ e.2.2 ∈ B} := by
    change (∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ U},
      {e : LegalMarkedPhysicalEdge q | e.2.2 ∈ B}.indicator (fun _ ↦ 1) e ∂Γ) = _
    have hm : MeasurableSet {e : LegalMarkedPhysicalEdge q | e.2.2 ∈ B} :=
      hB.preimage (measurable_snd.snd : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ e.2.2))
    rw [lintegral_indicator hm, lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hm]
    congr 1
    ext e
    exact and_comm
  have hglobal (Γ : Measure (LegalMarkedPhysicalEdge q)) :
      (∫⁻ e, f ((e.1.2, e.2.2), e.2.1 - e.1.1) ∂Γ) = Γ {e | e.2.2 ∈ B} := by
    exact lintegral_indicator_one (hB.preimage measurable_snd.snd)
  simp_rw [hread, hglobal] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (lintegral_legalMarkedNormalizedOptimalPlan_clock_le q hL α β kin g t MeasurableSet.univ hB).2 bot_le)

/-- The symmetric clock charge keeps the original source law and the same
actual plan while anchoring its original target window. -/
theorem lintegral_legalMarkedOptimalRootedSceneLaw_targetWindow_sourceClock_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q), (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.2.1 ∈ U ∧ e.1.2 ∈ A}
      ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
        (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤
      volume U * α A := by
  let f : PhysicalPairPalmMark (Fin q) → ℝ≥0∞ := {m | m.1.1 ∈ A}.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator (hA.preimage measurable_fst.fst)
  have h := lintegral_legalMarkedOptimalRootedSceneLaw_targetReadout_le q hq hL α β kin hk g hg t hf hU
  have hread (Γ : Measure (LegalMarkedPhysicalEdge q)) :
      (∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.2.1 ∈ U},
        f (physicalPairAnchor e).2 ∂Γ) = Γ {e | e.2.1 ∈ U ∧ e.1.2 ∈ A} := by
    change (∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.2.1 ∈ U},
      {e : LegalMarkedPhysicalEdge q | e.1.2 ∈ A}.indicator (fun _ ↦ 1) e ∂Γ) = _
    have hm : MeasurableSet {e : LegalMarkedPhysicalEdge q | e.1.2 ∈ A} :=
      hA.preimage (measurable_fst.snd : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ e.1.2))
    rw [lintegral_indicator hm, lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hm]
    congr 1
    ext e
    exact and_comm
  have hglobal (Γ : Measure (LegalMarkedPhysicalEdge q)) :
      (∫⁻ e, f ((e.1.2, e.2.2), e.2.1 - e.1.1) ∂Γ) = Γ {e | e.1.2 ∈ A} := by
    exact lintegral_indicator_one (hA.preimage measurable_fst.snd)
  simp_rw [hread, hglobal] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (lintegral_legalMarkedNormalizedOptimalPlan_clock_le q hL α β kin g t hA MeasurableSet.univ).1 bot_le)


/-- Without assuming full retained clock mass, compact target escape splits
into actual long edges and actual target clocks outside the chosen collar. -/
theorem measure_legalMarked_sourceWindow_target_escape_le_long_add_clock
    (q : ℕ) (Γ : Measure (LegalMarkedPhysicalEdge q))
    {U : Set (Fin q → ℝ)} {B : Set ℝ} {b R : ℝ}
    (hU : ∀ x ∈ U, ‖x‖ ≤ b) :
    Γ {e | e.1.1 ∈ U ∧ e.2 ∉ closedBall (0 : Fin q → ℝ) (b + R) ×ˢ B} ≤
      Γ {e | e.1.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖} +
        Γ {e | e.1.1 ∈ U ∧ e.2.2 ∉ B} := by
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro e he
  by_cases hlong : R ≤ ‖e.2.1 - e.1.1‖
  · exact Or.inl ⟨he.1, hlong⟩
  · refine Or.inr ⟨he.1, fun hclock ↦ he.2 ⟨?_, hclock⟩⟩
    have htri : ‖e.2.1‖ ≤ ‖e.2.1 - e.1.1‖ + ‖e.1.1‖ := by
      simpa only [sub_add_cancel] using norm_add_le (e.2.1 - e.1.1) e.1.1
    simp only [mem_closedBall, dist_zero_right]
    linarith [hU e.1.1 he.1, lt_of_not_ge hlong]

/-- The other direction uses the identical original edge and its source
clock collar, so no law is assigned to adaptive unmatched endpoints. -/
theorem measure_legalMarked_targetWindow_source_escape_le_long_add_clock
    (q : ℕ) (Γ : Measure (LegalMarkedPhysicalEdge q))
    {U : Set (Fin q → ℝ)} {A : Set ℝ} {b R : ℝ}
    (hU : ∀ x ∈ U, ‖x‖ ≤ b) :
    Γ {e | e.2.1 ∈ U ∧ e.1 ∉ closedBall (0 : Fin q → ℝ) (b + R) ×ˢ A} ≤
      Γ {e | e.2.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖} +
        Γ {e | e.2.1 ∈ U ∧ e.1.2 ∉ A} := by
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro e he
  by_cases hlong : R ≤ ‖e.2.1 - e.1.1‖
  · exact Or.inl ⟨he.1, hlong⟩
  · refine Or.inr ⟨he.1, fun hclock ↦ he.2 ⟨?_, hclock⟩⟩
    have htri : ‖e.1.1‖ ≤ ‖e.2.1 - e.1.1‖ + ‖e.2.1‖ := by
      have h := norm_add_le (e.1.1 - e.2.1) e.2.1
      simpa only [sub_add_cancel, norm_sub_rev] using h
    simp only [mem_closedBall, dist_zero_right]
    linarith [hU e.2.1 he.1, lt_of_not_ge hlong]

/-- Interior positivity, original null endpoint mass and the actual pressure
limit produce both nonproper compact escape bounds for the very same legal
finite optimizers. The collar is fixed before its spatial radius is enlarged;
no positive bound is assumed at the original support endpoints. -/
theorem exists_uniform_legalMarkedOptimalRootedSceneLaw_compact_bounds_of_interior
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
    {J A₀ B₀ : Set ℝ} (hJ : MeasurableSet J)
    (hA₀ : MeasurableSet A₀) (hB₀ : MeasurableSet B₀)
    (hαJ : α Jᶜ = 0) (hβJ : β Jᶜ = 0)
    (hαA : α A₀ᶜ = 0) (hβB : β B₀ᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ A₀, ∀ b ∈ B₀, δ ≤ |b - a|)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2})
    (hpos : ∀ p, p.1 ∈ J → p.2 ∈ J → p.1 < p.2 → (matrix p).PosDef)
    (hactual : ∀ a ∈ J ∩ A₀, ∀ b ∈ J ∩ B₀, a < b → ∀ v,
      kin a b v = matrixQuadratic (matrix (a, b)) v)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) (hUfin : volume U ≠ ∞)
    {b : ℝ} (hbounded : ∀ x ∈ U, ‖x‖ ≤ b) :
    ∃ L₀ : ℝ, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ S T : Set (LegalMarkedPhysicalPoint q), IsCompact S ∧ IsCompact T ∧
        ∀ L : ℝ, ∀ hL : 0 < L, L₀ ≤ L →
          (∫⁻ scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q), (scene.1 : Measure (LegalMarkedPhysicalEdge q))
            {e | e.1.1 ∈ U ∧ e.2 ∉ T}
            ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
              (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤ ε ∧
          (∫⁻ scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q), (scene.1 : Measure (LegalMarkedPhysicalEdge q))
            {e | e.2.1 ∈ U ∧ e.1 ∉ S}
            ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure
              (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤ ε := by
  have hpressure : ∀ᶠ L : ℝ in atTop, legalMarkedScalePressure q id id α β kin g L t ≤ p + 1 :=
    (hp.eventually (gt_mem_nhds (by linarith : p < p + 1))).mono (fun L hL ↦ hL.le)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hpressure
  refine ⟨L₀, fun ε hε ↦ ?_⟩
  obtain ⟨η, hη, hsmall⟩ := ENNReal.exists_pos_mul_lt
    (a := volume U * 4) (ENNReal.mul_ne_top hUfin (by norm_num)) hε.ne'
  obtain ⟨A, B, hA, hB, _, _, hαsmall, hβsmall, c, hc, hcoercive⟩ :=
    exists_compact_legal_clock_collars q α β hJ hA₀ hB₀ hαJ hβJ hαA hβB hδ hsep
      matrix hmatrix hpos kin hactual hη
  have hden : Tendsto (fun R : ℝ ↦ ENNReal.ofReal (c * R ^ 2)) atTop (𝓝 ∞) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop hc)
  have hdiv : Tendsto (fun R : ℝ ↦
      ENNReal.ofReal (p + 1 + |t| * G) / ENNReal.ofReal (c * R ^ 2)) atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      ENNReal.Tendsto.div tendsto_const_nhds (Or.inr (by simp)) hden
        (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨R, hR, henergy⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((ENNReal.tendsto_nhds_zero.mp hdiv) η hη)).exists
  refine ⟨closedBall (0 : Fin q → ℝ) (b + R) ×ˢ A,
    closedBall (0 : Fin q → ℝ) (b + R) ×ˢ B,
    (isCompact_closedBall 0 (b + R)).prod hA, (isCompact_closedBall 0 (b + R)).prod hB,
    fun L hL hlarge ↦ ?_⟩
  have he : ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) /
      ENNReal.ofReal (c * R ^ 2) ≤ η := by
    apply le_trans ?_ henergy
    gcongr
    exact hL₀ L hlarge
  have hnum : volume U * (α Aᶜ + β Bᶜ +
      ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) /
        ENNReal.ofReal (c * R ^ 2)) + volume U * η ≤ ε := by
    calc
      _ ≤ volume U * (η + η + η) + volume U * η := by gcongr
      _ = η * (volume U * 4) := by ring
      _ ≤ ε := hsmall.le
  constructor
  · have hm : Measurable (fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q)
        (LegalMarkedPhysicalPoint q) ↦ (scene.1 : Measure (LegalMarkedPhysicalEdge q))
          {e | e.1.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖}) :=
      (Measure.measurable_coe ((hU.preimage measurable_fst.fst).inter
        (measurableSet_le measurable_const (measurable_snd.fst.sub measurable_fst.fst).norm))).comp
          (measurable_localFiniteMeasure_coe.comp measurable_fst)
    calc
      _ ≤ ∫⁻ scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q), (scene.1 : Measure (LegalMarkedPhysicalEdge q))
          {e | e.1.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖} +
          (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | e.1.1 ∈ U ∧ e.2.2 ∉ B}
          ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure _) :=
        lintegral_mono (fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦ measure_legalMarked_sourceWindow_target_escape_le_long_add_clock
          q (scene.1 : Measure (LegalMarkedPhysicalEdge q)) hbounded)
      _ = _ := lintegral_add_left hm _
      _ ≤ volume U * (α Aᶜ + β Bᶜ +
          ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) /
            ENNReal.ofReal (c * R ^ 2)) + volume U * η := by
        apply add_le_add (lintegral_legalMarkedOptimalRootedSceneLaw_long_le_clock_collars q hq hL α β
          hC hG hk hkn hkb hhom hg hgb t hA.measurableSet hB.measurableSet hc hR hcoercive hU)
        exact (lintegral_legalMarkedOptimalRootedSceneLaw_sourceWindow_targetClock_le q hq hL α β
          kin hk g hg t hU hB.measurableSet.compl).trans (mul_le_mul_of_nonneg_left hβsmall.le bot_le)
      _ ≤ ε := hnum
  · have hm : Measurable (fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q)
        (LegalMarkedPhysicalPoint q) ↦ (scene.1 : Measure (LegalMarkedPhysicalEdge q))
          {e | e.2.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖}) :=
      (Measure.measurable_coe ((hU.preimage measurable_snd.fst).inter
        (measurableSet_le measurable_const (measurable_snd.fst.sub measurable_fst.fst).norm))).comp
          (measurable_localFiniteMeasure_coe.comp measurable_fst)
    calc
      _ ≤ ∫⁻ scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q), (scene.1 : Measure (LegalMarkedPhysicalEdge q))
          {e | e.2.1 ∈ U ∧ R ≤ ‖e.2.1 - e.1.1‖} +
          (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | e.2.1 ∈ U ∧ e.1.2 ∉ A}
          ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL : Measure _) :=
        lintegral_mono (fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦ measure_legalMarked_targetWindow_source_escape_le_long_add_clock
          q (scene.1 : Measure (LegalMarkedPhysicalEdge q)) hbounded)
      _ = _ := lintegral_add_left hm _
      _ ≤ volume U * (α Aᶜ + β Bᶜ +
          ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) /
            ENNReal.ofReal (c * R ^ 2)) + volume U * η := by
        apply add_le_add (lintegral_legalMarkedOptimalRootedSceneLaw_target_long_le_clock_collars q hq hL α β
          hC hG hk hkn hkb hhom hg hgb t hA.measurableSet hB.measurableSet hc hR hcoercive hU)
        exact (lintegral_legalMarkedOptimalRootedSceneLaw_targetWindow_sourceClock_le q hq hL α β
          kin hk g hg t hU hA.measurableSet.compl).trans (mul_le_mul_of_nonneg_left hαsmall.le bot_le)
      _ ≤ ε := hnum

end OTSelector.Reconstruction
