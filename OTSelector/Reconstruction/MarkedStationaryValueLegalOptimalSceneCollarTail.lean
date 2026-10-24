import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneMarginalDefect
import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedEnergy

/-!
# Original legal optimal plan tails from genuine clock-collar coercivity

The original input empirical measures dominate the actual optimal plan
marginals. Their unchanged Poisson law bounds lost clock collars. On the
retained collars, a genuine quadratic lower bound controls the original full
transverse displacement. No distribution is assigned to selected endpoints.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem lintegral_original_poissonPrefixCount
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {S : Set X} (hS : MeasurableSet S) :
    (∫⁻ z, (poissonPrefixCount S z : ℝ≥0∞)
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
      ENNReal.ofReal (r : ℝ) * ν S := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_poissonPrefixCount ν r hS)
    (.of_forall (fun z ↦ Nat.cast_nonneg (poissonPrefixCount S z)))
  rw [integral_poissonPrefixCount ν r hS] at h
  simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top ν S)] using h.symm

private theorem measurable_poissonPrefixCount_ennreal
    {X : Type*} [MeasurableSpace X] {S : Set X} (hS : MeasurableSet S) :
    Measurable (fun z : ℕ × (ℕ → X) ↦ (poissonPrefixCount S z : ℝ≥0∞)) := by
  have h := ENNReal.measurable_ofReal.comp (measurable_poissonPrefixSum
    (show Measurable (S.indicator (fun _ ↦ (1 : ℝ))) from measurable_const.indicator hS))
  simpa only [Function.comp_def, ← poissonPrefixCount_cast, ENNReal.ofReal_natCast] using h

/-- The original full empirical source has exactly its original expected
clock-subset mass, before any optimizer selection. -/
theorem lintegral_legalMarkedSourceEmpiricalMeasure_clock
    (q : ℕ) (L : ℝ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ ω, legalMarkedSourceEmpiricalMeasure q L ω {p | p.2 ∈ A}
      ∂twoMarkedCloudLaw q ℝ ℝ α β r) = ENNReal.ofReal (r : ℝ) * α A := by
  classical
  have heq (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      legalMarkedSourceEmpiricalMeasure q L ω {p | p.2 ∈ A} =
        (poissonPrefixCount (Prod.snd ⁻¹' A) ω.1 : ℝ≥0∞) := by
    simp only [legalMarkedSourceEmpiricalMeasure, Measure.finsetSum_apply]
    change (∑ i : Fin ω.1.1,
      Measure.dirac (legalMarkedPhysicalEdge q L ω i 0).1 {p | p.2 ∈ A}) =
      ((Finset.univ.filter (fun i : Fin ω.1.1 ↦ (ω.1.2 i).2 ∈ A)).card : ℝ≥0∞)
    rw [Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : (ω.1.2 i).2 ∈ A
    · simp [legalMarkedPhysicalEdge, mSourceMark, h]
    · simp [legalMarkedPhysicalEdge, mSourceMark, h]
  simp_rw [heq]
  have hm := measurable_poissonPrefixCount_ennreal (hA.preimage (measurable_snd :
    Measurable (Prod.snd : (Fin q → ℝ) × ℝ → ℝ)))
  have he := lintegral_map hm measurable_fst (μ := twoMarkedCloudLaw q ℝ ℝ α β r)
  have hmap : (twoMarkedCloudLaw q ℝ ℝ α β r).map Prod.fst = markedPoissonLaw q ℝ α r := by
    change ((markedPoissonLaw q ℝ α r).prod (markedPoissonLaw q ℝ β r)).map Prod.fst = _
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [hmap] at he
  rw [← he]
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := lintegral_original_poissonPrefixCount ((cubeMeasure (Fin q) 1).prod α) r
    (hA.preimage measurable_snd)
  simpa only [markedPoissonLaw, markedSeqLaw, show (Prod.snd ⁻¹' A : Set ((Fin q → ℝ) × ℝ)) =
    univ ×ˢ A from by ext p; simp, Measure.prod_prod, measure_univ, one_mul] using h

/-- The actual input target has its original expected clock-subset mass. -/
theorem lintegral_legalMarkedTargetEmpiricalMeasure_clock
    (q : ℕ) (L : ℝ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) {B : Set ℝ} (hB : MeasurableSet B) :
    (∫⁻ ω, legalMarkedTargetEmpiricalMeasure q L ω {p | p.2 ∈ B}
      ∂twoMarkedCloudLaw q ℝ ℝ α β r) = ENNReal.ofReal (r : ℝ) * β B := by
  classical
  have heq (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      legalMarkedTargetEmpiricalMeasure q L ω {p | p.2 ∈ B} =
        (poissonPrefixCount (Prod.snd ⁻¹' B) ω.2 : ℝ≥0∞) := by
    simp only [legalMarkedTargetEmpiricalMeasure, Measure.finsetSum_apply]
    change (∑ i : Fin ω.2.1,
      Measure.dirac (legalMarkedPhysicalEdge q L ω 0 i).2 {p | p.2 ∈ B}) =
      ((Finset.univ.filter (fun i : Fin ω.2.1 ↦ (ω.2.2 i).2 ∈ B)).card : ℝ≥0∞)
    rw [Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : (ω.2.2 i).2 ∈ B
    · simp [legalMarkedPhysicalEdge, mTargetMark, h]
    · simp [legalMarkedPhysicalEdge, mTargetMark, h]
  simp_rw [heq]
  have hm := measurable_poissonPrefixCount_ennreal (hB.preimage (measurable_snd :
    Measurable (Prod.snd : (Fin q → ℝ) × ℝ → ℝ)))
  have he := lintegral_map hm measurable_snd (μ := twoMarkedCloudLaw q ℝ ℝ α β r)
  have hmap : (twoMarkedCloudLaw q ℝ ℝ α β r).map Prod.snd = markedPoissonLaw q ℝ β r := by
    change ((markedPoissonLaw q ℝ α r).prod (markedPoissonLaw q ℝ β r)).map Prod.snd = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  rw [hmap] at he
  rw [← he]
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have h := lintegral_original_poissonPrefixCount ((cubeMeasure (Fin q) 1).prod β) r
    (hB.preimage measurable_snd)
  simpa only [markedPoissonLaw, markedSeqLaw, show (Prod.snd ⁻¹' B : Set ((Fin q → ℝ) × ℝ)) =
    univ ×ˢ B from by ext p; simp, Measure.prod_prod, measure_univ, one_mul] using h

/-- Actual normalized optimal plans cannot place more expected source or
target clock mass in a collar than the full original input law. -/
theorem lintegral_legalMarkedNormalizedOptimalPlan_clock_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ ω, legalMarkedNormalizedOptimalPlan q L kin g t ω {e | e.1.2 ∈ A}
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ α A ∧
    (∫⁻ ω, legalMarkedNormalizedOptimalPlan q L kin g t ω {e | e.2.2 ∈ B}
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ β B := by
  have hV : 0 < L ^ q := pow_pos hL q
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 := (ENNReal.ofReal_pos.mpr hV).ne'
  constructor
  · calc
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (L ^ q))⁻¹ *
          legalMarkedSourceEmpiricalMeasure q L ω {p | p.2 ∈ A}
          ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)) := by
        apply lintegral_mono
        intro ω
        have h := (legalMarkedNormalizedOptimalPlan_marginals_le_empirical q L kin g t ω).1
          {p | p.2 ∈ A}
        have hSA : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ A} :=
          hA.preimage measurable_snd
        rwa [Measure.map_apply measurable_fst hSA, Measure.smul_apply, smul_eq_mul] at h
      _ = α A := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hV0),
          lintegral_legalMarkedSourceEmpiricalMeasure_clock q L α β _ hA,
          Real.coe_toNNReal _ hV.le, ← mul_assoc,
          ENNReal.inv_mul_cancel hV0 ENNReal.ofReal_ne_top, one_mul]
  · calc
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (L ^ q))⁻¹ *
          legalMarkedTargetEmpiricalMeasure q L ω {p | p.2 ∈ B}
          ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)) := by
        apply lintegral_mono
        intro ω
        have h := (legalMarkedNormalizedOptimalPlan_marginals_le_empirical q L kin g t ω).2
          {p | p.2 ∈ B}
        have hSB : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ B} :=
          hB.preimage measurable_snd
        rwa [Measure.map_apply measurable_snd hSB, Measure.smul_apply, smul_eq_mul] at h
      _ = β B := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hV0),
          lintegral_legalMarkedTargetEmpiricalMeasure_clock q L α β _ hB,
          Real.coe_toNNReal _ hV.le, ← mul_assoc,
          ENNReal.inv_mul_cancel hV0 ENNReal.ofReal_ne_top, one_mul]

/-- Original collar coercivity bounds the actual full-displacement tail for
any actual plan, with its actual source/target collar masses. -/
theorem measure_physicalEdge_long_le_clock_collars_add_energy
    (q : ℕ) (Γ : Measure (LegalMarkedPhysicalEdge q))
    {A B : Set ℝ} {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hforward : ∀ᵐ e ∂Γ, e.1.2 < e.2.2)
    (hcoercive : ∀ a ∈ A, ∀ b ∈ B, a < b → ∀ v, c * ‖v‖ ^ 2 ≤ kin a b v) :
    Γ {e | R ≤ ‖e.2.1 - e.1.1‖} ≤
      Γ {e | e.1.2 ∉ A} + Γ {e | e.2.2 ∉ B} +
        (∫⁻ e, ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e) ∂Γ) /
          ENNReal.ofReal (c * R ^ 2) := by
  let S : Set (LegalMarkedPhysicalEdge q) :=
    {e | ENNReal.ofReal (c * R ^ 2) ≤ ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e)}
  have hsub : ∀ᵐ e ∂Γ, e ∈ {e : LegalMarkedPhysicalEdge q | R ≤ ‖e.2.1 - e.1.1‖} →
      e ∈ ({e | e.1.2 ∉ A} ∪ {e | e.2.2 ∉ B}) ∪ S := by
    filter_upwards [hforward] with e heforward
    intro he
    by_cases ha : e.1.2 ∈ A
    · by_cases hb : e.2.2 ∈ B
      · right
        have he' : R ≤ ‖e.2.1 - e.1.1‖ := he
        apply ENNReal.ofReal_le_ofReal
        exact (mul_le_mul_of_nonneg_left (by nlinarith [he', norm_nonneg (e.2.1 - e.1.1)] :
          R ^ 2 ≤ ‖e.2.1 - e.1.1‖ ^ 2) hc.le).trans (hcoercive _ ha _ hb heforward _)
      · exact Or.inl (Or.inr hb)
    · exact Or.inl (Or.inl ha)
  have hkm : Measurable (fun e : LegalMarkedPhysicalEdge q ↦
      ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e)) :=
    ENNReal.measurable_ofReal.comp (hk.comp
      ((measurable_fst.snd.prodMk measurable_snd.snd).prodMk
        (measurable_snd.fst.sub measurable_fst.fst)))
  calc
    _ ≤ Γ (({e | e.1.2 ∉ A} ∪ {e | e.2.2 ∉ B}) ∪ S) := measure_mono_ae hsub
    _ ≤ Γ {e | e.1.2 ∉ A} + Γ {e | e.2.2 ∉ B} + Γ S :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add le_rfl (meas_ge_le_lintegral_div (μ := Γ) hkm.aemeasurable
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < c * R ^ 2)).ne' ENNReal.ofReal_ne_top)

/-- The original Poisson mark law and actual kinetic expectation produce a
full-displacement tail estimate for the actual original normalized optimum.
Only genuine coercivity on the chosen clock collars is an analytic input. -/
theorem lintegral_legalMarkedNormalizedOptimalPlan_long_le_clock_collars
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
    (hcoercive : ∀ a ∈ A, ∀ b ∈ B, a < b → ∀ v, c * ‖v‖ ^ 2 ≤ kin a b v) :
    (∫⁻ ω, legalMarkedNormalizedOptimalPlan q L kin g t ω {e | R ≤ ‖e.2.1 - e.1.1‖}
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤
      α Aᶜ + β Bᶜ + ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) /
        ENNReal.ofReal (c * R ^ 2) := by
  let Γ := legalMarkedNormalizedOptimalPlan q L kin g t
  let P := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))
  have hΓ : Measurable Γ := measurable_legalMarkedNormalizedOptimalPlan q L hk hg t
  have hSA : MeasurableSet {e : LegalMarkedPhysicalEdge q | e.1.2 ∉ A} :=
    hA.compl.preimage measurable_fst.snd
  have hTB : MeasurableSet {e : LegalMarkedPhysicalEdge q | e.2.2 ∉ B} :=
    hB.compl.preimage measurable_snd.snd
  have hMA : Measurable (fun ω ↦ Γ ω {e | e.1.2 ∉ A}) := (Measure.measurable_coe hSA).comp hΓ
  have hMB : Measurable (fun ω ↦ Γ ω {e | e.2.2 ∉ B}) := (Measure.measurable_coe hTB).comp hΓ
  have hke : Measurable (fun e : LegalMarkedPhysicalEdge q ↦
      ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e)) :=
    ENNReal.measurable_ofReal.comp (hk.comp
      ((measurable_fst.snd.prodMk measurable_snd.snd).prodMk
        (measurable_snd.fst.sub measurable_fst.fst)))
  have hME : Measurable (fun ω ↦ ∫⁻ e, ENNReal.ofReal
      (legalMarkedPhysicalKineticEdge q kin e) ∂Γ ω) :=
    (Measure.measurable_lintegral hke).comp hΓ
  have hforward (ω : TwoMarkedCloudSpace q ℝ ℝ) : ∀ᵐ e ∂Γ ω, e.1.2 < e.2.2 :=
    Measure.ae_smul_measure (ae_forward_legalMarkedOptimalPlan q L (L ^ q) kin g t ω) _
  have hclock := lintegral_legalMarkedNormalizedOptimalPlan_clock_le q hL α β kin g t hA.compl hB.compl
  have henergy := lintegral_legalMarkedNormalizedOptimalPlan_kinetic_le
    q hq hL α β hC hG hk hkn hkb hhom hg hgb t
  have hdivide : (∫⁻ ω, (∫⁻ e, ENNReal.ofReal
      (legalMarkedPhysicalKineticEdge q kin e) ∂Γ ω) / ENNReal.ofReal (c * R ^ 2) ∂P) =
      (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e) ∂Γ ω ∂P) /
        ENNReal.ofReal (c * R ^ 2) := by
    simp only [div_eq_mul_inv]
    exact lintegral_mul_const _ hME
  calc
    _ ≤ ∫⁻ ω, Γ ω {e | e.1.2 ∉ A} + Γ ω {e | e.2.2 ∉ B} +
        (∫⁻ e, ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e) ∂Γ ω) /
          ENNReal.ofReal (c * R ^ 2) ∂P :=
      lintegral_mono (fun ω ↦ measure_physicalEdge_long_le_clock_collars_add_energy
        q (Γ ω) hc hR kin hk (hforward ω) hcoercive)
    _ = (∫⁻ ω, Γ ω {e | e.1.2 ∉ A} ∂P) + (∫⁻ ω, Γ ω {e | e.2.2 ∉ B} ∂P) +
        (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e) ∂Γ ω ∂P) /
          ENNReal.ofReal (c * R ^ 2) := by
      have hMM : Measurable (fun ω ↦ Γ ω {e | e.1.2 ∉ A} + Γ ω {e | e.2.2 ∉ B}) :=
        hMA.add hMB
      rw [lintegral_add_left hMM, lintegral_add_left hMA, hdivide]
    _ ≤ _ := by
      apply add_le_add (add_le_add hclock.1 hclock.2)
      gcongr


end OTSelector.Reconstruction
