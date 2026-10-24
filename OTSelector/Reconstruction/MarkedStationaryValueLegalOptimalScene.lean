import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyOptimal
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Actual atomic physical plan of the first legal signed optimum

The selected matching is the existing exact signed minimum at the actual
legal maximum cardinality. Its plan places unit atoms at the same original
marked physical endpoints. Measurable edge events produce the actual random
measure, including samples with Hall deficits and tied optima.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

abbrev LegalMarkedPhysicalPoint (q : ℕ) := (Fin q → ℝ) × ℝ
abbrev LegalMarkedPhysicalEdge (q : ℕ) :=
  LegalMarkedPhysicalPoint q × LegalMarkedPhysicalPoint q

/-- Literal original physical endpoints at spatial scale `L`, retaining the
original scalar source and target marks. No spatial clamping is used. -/
def legalMarkedPhysicalEdge (q : ℕ) (L : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (i j : ℕ) : LegalMarkedPhysicalEdge q :=
  ((fun l ↦ L * mSourcePoint ω i l, mSourceMark ω i),
    (fun l ↦ L * mTargetPoint ω j l, mTargetMark ω j))

theorem measurable_legalMarkedPhysicalEdge (q : ℕ) (L : ℝ) (i j : ℕ) :
    Measurable (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦ legalMarkedPhysicalEdge q L ω i j) := by
  have hs : Measurable (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦
      fun l ↦ L * mSourcePoint ω i l) := by
    apply measurable_pi_lambda
    intro l
    exact ((measurable_pi_apply l).comp (measurable_mSourcePoint q i)).const_mul L
  have ht : Measurable (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦
      fun l ↦ L * mTargetPoint ω j l) := by
    apply measurable_pi_lambda
    intro l
    exact ((measurable_pi_apply l).comp (measurable_mTargetPoint q j)).const_mul L
  exact (hs.prodMk (measurable_mSourceMark q i)).prodMk
    (ht.prodMk (measurable_mTargetMark q j))

/-- The actual finite physical edge measure of the first legal signed optimum
on fixed prefixes of the original two marked clouds. -/
def legalMarkedFixedOptimalPlan (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Measure (LegalMarkedPhysicalEdge q) :=
  ∑ e ∈ (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).edges,
    Measure.dirac (legalMarkedPhysicalEdge q L ω e.1 e.2)

/-- Actual optimal edge events and original endpoint coordinates discharge
measurability of the entire finite physical plan as an actual measure. -/
theorem measurable_legalMarkedFixedOptimalPlan (q m n : ℕ) (L r : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (legalMarkedFixedOptimalPlan q m n L r kin g t) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have heq : (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦
      legalMarkedFixedOptimalPlan q m n L r kin g t ω S) = fun ω ↦
      ∑ e : Fin m × Fin n,
        if e ∈ (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).edges then
          Measure.dirac (legalMarkedPhysicalEdge q L ω e.1 e.2) S else 0 := by
    funext ω
    rw [legalMarkedFixedOptimalPlan, Measure.finsetSum_apply]
    have hfilter : (Finset.univ.filter fun e : Fin m × Fin n ↦
        e ∈ (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).edges) =
        (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).edges := by ext e; simp
    rw [← Finset.sum_filter, hfilter]
  rw [heq]
  exact Finset.measurable_sum _ fun e _ ↦ Measurable.ite
    (measurableSet_mem_firstLegalMarkedOptimalMatching q m n
      measurable_id measurable_id hkin hg r t e)
    ((Measure.measurable_coe hS).comp
      (Measure.measurable_dirac.comp (measurable_legalMarkedPhysicalEdge q L e.1 e.2)))
    measurable_const

instance legalMarkedFixedOptimalPlanIsFinite (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    IsFiniteMeasure (legalMarkedFixedOptimalPlan q m n L r kin g t ω) := by
  unfold legalMarkedFixedOptimalPlan
  infer_instance

/-- Its total actual edge mass is exactly the original graph's legal maximum
cardinality, including every original Hall deficit. -/
theorem legalMarkedFixedOptimalPlan_univ (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedFixedOptimalPlan q m n L r kin g t ω univ =
      (PartialMatching.legalMaximumCard (legalMarkedGraph q m n id id ω) : ℝ≥0∞) := by
  classical
  have hc := (firstLegalMarkedOptimalMatching_isLegalOptimal
    q m n id id r kin g t ω).2.1
  rw [← hc]
  simp [legalMarkedFixedOptimalPlan, Measure.finsetSum_apply, OTSelector.PartialMatching.card]

/-- Every real readout is integrable for this actual finite atomic plan. -/
theorem integrable_legalMarkedFixedOptimalPlan (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (f : LegalMarkedPhysicalEdge q → ℝ) :
    Integrable f (legalMarkedFixedOptimalPlan q m n L r kin g t ω) := by
  unfold legalMarkedFixedOptimalPlan
  exact integrable_finsetSum_measure.mpr (fun e he ↦ integrable_dirac (by simp))

/-- Integration against the actual optimal plan is the literal sum over the
selected original edges, with no replacement candidate matching. -/
theorem integral_legalMarkedFixedOptimalPlan (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (f : LegalMarkedPhysicalEdge q → ℝ) :
    (∫ e, f e ∂legalMarkedFixedOptimalPlan q m n L r kin g t ω) =
      ∑ e ∈ (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).edges,
        f (legalMarkedPhysicalEdge q L ω e.1 e.2) := by
  unfold legalMarkedFixedOptimalPlan
  rw [integral_finsetSum_measure (fun e he ↦ integrable_dirac (by simp))]
  simp only [integral_dirac]

/-- Every atom remains an original strictly forward edge. -/
theorem ae_forward_legalMarkedFixedOptimalPlan (q m n : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ∀ᵐ e ∂legalMarkedFixedOptimalPlan q m n L r kin g t ω, e.1.2 < e.2.2 := by
  classical
  unfold legalMarkedFixedOptimalPlan
  rw [ae_finsetSum_measure_iff]
  intro e he
  rw [ae_dirac_iff (measurableSet_lt measurable_fst.snd measurable_snd.snd)]
  have hlegal := (firstLegalMarkedOptimalMatching_isLegalOptimal
    q m n id id r kin g t ω).1 he
  simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and,
    legalMarkedPhysicalEdge, id_eq] using hlegal

/-- The physical signed paired-edge readout retains both original scalar
clocks and the complete original transverse displacement. -/
def legalMarkedPhysicalTiltedEdge (q : ℕ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (e : LegalMarkedPhysicalEdge q) : ℝ :=
  kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2

/-- The original cube-support event removes only the global auxiliary clamp;
actual homogeneous spatial scaling gives the exact original kinetic score. -/
theorem legalMarkedPhysicalTiltedEdge_eq_marked_score (q : ℕ) (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) (i j : ℕ)
    (hS : mSourcePoint ω i ∈ unitCube q) (hT : mTargetPoint ω j ∈ unitCube q) :
    legalMarkedPhysicalTiltedEdge q kin g t (legalMarkedPhysicalEdge q L ω i j) =
      mKineticCost q (L ^ q) kin ω i j + t * mProbe g ω i j := by
  have hpow : (L ^ q) ^ (2 / (q : ℝ)) = L ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have he : (q : ℝ) * (2 / (q : ℝ)) = 2 := by field_simp
    rw [he, Real.rpow_two]
  have hdisp : (fun l ↦ L * mTargetPoint ω j l) - (fun l ↦ L * mSourcePoint ω i l) =
      fun l ↦ L * mDisplacement (mSourcePoint ω i) (mTargetPoint ω j) l := by
    funext l
    simp only [Pi.sub_apply, mDisplacement, cubeTruncPoint_eq_of_mem hS,
      cubeTruncPoint_eq_of_mem hT]
    ring
  simp only [legalMarkedPhysicalTiltedEdge, legalMarkedPhysicalEdge,
    mKineticCost, mProbe, hdisp, hhom _ _ L hL, hpow]

/-- The actual physical plan's signed cost equals the true signed legal
minimum at its actual legal maximum cardinality. -/
theorem integral_legalMarkedFixedOptimalPlan_eq_legalMarkedFixedValue
    (q m n : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 ≤ L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hS : ∀ i : Fin m, mSourcePoint ω i ∈ unitCube q)
    (hT : ∀ j : Fin n, mTargetPoint ω j ∈ unitCube q) :
    (∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedFixedOptimalPlan q m n L (L ^ q) kin g t ω) =
        legalMarkedFixedValue q m n id id (L ^ q) kin g t ω := by
  rw [integral_legalMarkedFixedOptimalPlan]
  calc
    _ = (firstLegalMarkedOptimalMatching q m n id id (L ^ q) kin g t ω).cost
        (fun i j ↦ mKineticCost q (L ^ q) kin ω i j + t * mProbe g ω i j) := by
      apply Finset.sum_congr rfl
      intro e he
      exact legalMarkedPhysicalTiltedEdge_eq_marked_score q hq hL kin hhom g t ω
        e.1 e.2 (hS e.1) (hT e.2)
    _ = _ := (firstLegalMarkedOptimalMatching_isLegalOptimal
      q m n id id (L ^ q) kin g t ω).2.2

/-- The actual first legal signed optimum at the realized original source
and target counts, represented by its original physical edge atoms. -/
def legalMarkedOptimalPlan (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Measure (LegalMarkedPhysicalEdge q) :=
  legalMarkedFixedOptimalPlan q (mSourceCount ω) (mTargetCount ω) L r kin g t ω

/-- Count strata select the canonical actual finite optimum measurably.
No separate measurable-optimizer or measurable-plan assumption is supplied. -/
theorem measurable_legalMarkedOptimalPlan (q : ℕ) (L r : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (legalMarkedOptimalPlan q L r kin g t) := by
  have hfixed (mn : ℕ × ℕ) :
      Measurable (legalMarkedFixedOptimalPlan q mn.1 mn.2 L r kin g t) :=
    measurable_legalMarkedFixedOptimalPlan q mn.1 mn.2 L r hkin hg t
  have hprod : Measurable (fun p : (ℕ × ℕ) × TwoMarkedCloudSpace q ℝ ℝ ↦
      legalMarkedFixedOptimalPlan q p.1.1 p.1.2 L r kin g t p.2) :=
    measurable_from_prod_countable_right hfixed
  have h := hprod.comp (((measurable_mSourceCount q).prodMk
    (measurable_mTargetCount q)).prodMk measurable_id)
  change Measurable (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦
    legalMarkedFixedOptimalPlan q (mSourceCount ω) (mTargetCount ω) L r kin g t ω)
  simpa only [Function.comp_def, id_eq] using h

instance legalMarkedOptimalPlanIsFinite (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    IsFiniteMeasure (legalMarkedOptimalPlan q L r kin g t ω) := by
  unfold legalMarkedOptimalPlan
  infer_instance

theorem legalMarkedOptimalPlan_univ (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedOptimalPlan q L r kin g t ω univ =
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) :=
  legalMarkedFixedOptimalPlan_univ q _ _ L r kin g t ω

theorem ae_forward_legalMarkedOptimalPlan (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ∀ᵐ e ∂legalMarkedOptimalPlan q L r kin g t ω, e.1.2 < e.2.2 :=
  ae_forward_legalMarkedFixedOptimalPlan q _ _ L r kin g t ω

/-- The original Poisson cloud law supplies the complete cube-support event
internally, so its actual physical optimal plan has exactly the true legal
signed value almost surely. -/
theorem ae_integral_legalMarkedOptimalPlan_eq_legalMarkedTilted
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 ≤ L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β r,
      (∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
        ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω) =
          legalMarkedTilted q id id (L ^ q) kin g t ω := by
  filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q α β r] with ω hω
  exact integral_legalMarkedFixedOptimalPlan_eq_legalMarkedFixedValue
    q (mSourceCount ω) (mTargetCount ω) hq hL kin hhom g t ω
      (fun i ↦ hω.1 i) (fun j ↦ hω.2 j)

/-- The true original pressure is the expected signed physical cost of the
constructed actual legal optimal plan. Its integrability follows from the
original count moment and the original kernel/probe bounds. -/
theorem integrable_and_integral_legalMarkedOptimalPlan_eq_pressure
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 ≤ L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (fun ω ↦ ∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ∧
    (∫ ω, ∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) =
      legalMarkedPressure q id id α β (Real.toNNReal (L ^ q)) kin g t := by
  have hr : (Real.toNNReal (L ^ q) : ℝ) = L ^ q :=
    Real.coe_toNNReal _ (pow_nonneg hL q)
  have heq : (fun ω ↦ ∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω)
      =ᵐ[twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))]
        legalMarkedTilted q id id (L ^ q) kin g t :=
    ae_integral_legalMarkedOptimalPlan_eq_legalMarkedTilted
      q hq hL kin hhom g t α β (Real.toNNReal (L ^ q))
  have hint := integrable_legalMarkedTilted q measurable_id measurable_id
    α β (Real.toNNReal (L ^ q)) hC hG hkin hkb hg hgb t
  rw [hr] at hint
  refine ⟨hint.congr heq.symm, ?_⟩
  rw [legalMarkedPressure, hr]
  exact integral_congr_ae heq

end OTSelector.Reconstruction
