import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalScene
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootPhysicalScene
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLaw
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Original normalized legal optimal plans and their actual rooted energies

The global plan is the literal original optimal edge measure divided by the
original physical volume. Its original Poisson mean controls its expected
mass, while actual root observation cancels this normalization exactly.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The literal original optimal physical plan per original volume. -/
def legalMarkedNormalizedOptimalPlan (q : ℕ) (L : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Measure (LegalMarkedPhysicalEdge q) :=
  (ENNReal.ofReal (L ^ q))⁻¹ • legalMarkedOptimalPlan q L (L ^ q) kin g t ω

theorem measurable_legalMarkedNormalizedOptimalPlan (q : ℕ) (L : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (legalMarkedNormalizedOptimalPlan q L kin g t) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [legalMarkedNormalizedOptimalPlan, Measure.smul_apply, smul_eq_mul]
  exact ((Measure.measurable_coe hS).comp
    (measurable_legalMarkedOptimalPlan q L (L ^ q) hkin hg t)).const_mul _

theorem isFiniteMeasure_legalMarkedNormalizedOptimalPlan (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) := by
  constructor
  rw [legalMarkedNormalizedOptimalPlan, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top
    (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hL q)))
    (measure_lt_top _ _)

/-- The unchanged original Poisson source-count first moment, in nonnegative
integral form. -/
theorem lintegral_mSourceCount_ennreal (q : ℕ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (r : ℝ≥0) :
    (∫⁻ ω, (mSourceCount ω : ℝ≥0∞) ∂twoMarkedCloudLaw q ℝ ℝ α β r) =
      ENNReal.ofReal (r : ℝ) := by
  have h := ofReal_integral_eq_lintegral_ofReal
    (integrable_mSourceCount q α β r) (.of_forall (fun ω ↦ Nat.cast_nonneg (mSourceCount ω)))
  rw [integral_mSourceCount_eq] at h
  simpa only [ENNReal.ofReal_natCast] using h.symm

/-- The original legal maximum-cardinality bound and the unchanged original
Poisson source-count mean give expected normalized mass at most one. -/
theorem lintegral_legalMarkedNormalizedOptimalPlan_univ_le_one
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) :
    (∫⁻ ω, legalMarkedNormalizedOptimalPlan q L kin g t ω univ
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ 1 := by
  have hV : 0 < L ^ q := pow_pos hL q
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 := (ENNReal.ofReal_pos.mpr hV).ne'
  calc
    _ = (ENNReal.ofReal (L ^ q))⁻¹ * ∫⁻ ω,
        legalMarkedOptimalPlan q L (L ^ q) kin g t ω univ
          ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)) := by
      simp_rw [legalMarkedNormalizedOptimalPlan, Measure.smul_apply, smul_eq_mul]
      exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hV0)
    _ ≤ (ENNReal.ofReal (L ^ q))⁻¹ * ∫⁻ ω, (mSourceCount ω : ℝ≥0∞)
          ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)) := by
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      apply lintegral_mono
      intro ω
      change legalMarkedOptimalPlan q L (L ^ q) kin g t ω univ ≤
        (mSourceCount ω : ℝ≥0∞)
      rw [legalMarkedOptimalPlan_univ]
      exact_mod_cast (PartialMatching.legalMaximumCard_le_min
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω)).trans (min_le_left _ _)
    _ = 1 := by
      rw [lintegral_mSourceCount_ennreal, Real.coe_toNNReal _ hV.le]
      exact ENNReal.inv_mul_cancel hV0 ENNReal.ofReal_ne_top

/-- Original physical rooting cancels the original volume normalization
exactly and produces the raw original optimal plan's actual spatial reroot. -/
theorem physicalSceneRootedPlan_legalMarkedNormalizedOptimalPlan
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    physicalSceneRootedPlan (legalMarkedNormalizedOptimalPlan q L kin g t ω)
      Prod.fst Prod.snd (L ^ q) z =
        (legalMarkedOptimalPlan q L (L ^ q) kin g t ω).map (physicalSceneEdgeReroot z) := by
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hL q)).ne'
  rw [physicalSceneRootedPlan, legalMarkedNormalizedOptimalPlan,
    Measure.map_smul, smul_smul, ENNReal.mul_inv_cancel hV0 ENNReal.ofReal_ne_top, one_smul]
  rfl

/-- Deterministically center the same original physical box. Original plans
and original clocks remain unchanged. -/
def legalMarkedCenteredCoordinate (q : ℕ) (L : ℝ)
    (p : LegalMarkedPhysicalPoint q) : Fin q → ℝ := p.1 - (fun _ ↦ L / 2)

theorem measurable_legalMarkedCenteredCoordinate (q : ℕ) (L : ℝ) :
    Measurable (legalMarkedCenteredCoordinate q L) := measurable_fst.sub measurable_const

/-- The centered Haar root cube has exactly the original physical volume. -/
theorem volume_haarRootCube_half_legalMarked_scale (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    volume (haarRootCube (Fin q) (L / 2)) = ENNReal.ofReal (L ^ q) := by
  rw [volume_haarRootCube (Fin q) (by positivity : 0 ≤ L / 2), Fintype.card_fin]
  have heq : 2 * (L / 2) = L := by ring
  rw [heq]

/-- Actual original cube points cover the same complete centered root box
under deterministic centering, without any resampling. -/
theorem legalMarkedCenteredCoordinate_scaledPoint_mem_haarRootCube
    (q : ℕ) {L : ℝ} (hL : 0 ≤ L) {x : Fin q → ℝ} (hx : x ∈ unitCube q) (a : ℝ) :
    legalMarkedCenteredCoordinate q L (fun l ↦ L * x l, a) ∈
      haarRootCube (Fin q) (L / 2) := by
  change (fun _ ↦ -(L / 2)) ≤ (fun l ↦ L * x l - L / 2) ∧
    (fun l ↦ L * x l - L / 2) ≤ (fun _ ↦ L / 2)
  constructor
  · intro l
    have hl := hx l (mem_univ l)
    have hp := mul_nonneg hL hl.1.le
    dsimp
    linarith
  · intro l
    have hl := hx l (mem_univ l)
    have hp := mul_le_mul_of_nonneg_left hl.2.le hL
    dsimp
    linarith

/-- Centered physical rooting retains the same original optimal plan and is
exactly its spatial reroot by the deterministic center plus the chosen root. -/
theorem physicalSceneRootedPlan_legalMarkedNormalizedOptimalPlan_centered
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    physicalSceneRootedPlan (legalMarkedNormalizedOptimalPlan q L kin g t ω)
      (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) z =
      (legalMarkedOptimalPlan q L (L ^ q) kin g t ω).map
        (physicalSceneEdgeReroot ((fun _ ↦ L / 2) + z)) := by
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hL q)).ne'
  rw [physicalSceneRootedPlan, legalMarkedNormalizedOptimalPlan,
    Measure.map_smul, smul_smul, ENNReal.mul_inv_cancel hV0 ENNReal.ofReal_ne_top, one_smul]
  congr 1
  funext e
  change (((e.1.1 - (fun _ ↦ L / 2)) - z, e.1.2),
    ((e.2.1 - (fun _ ↦ L / 2)) - z, e.2.2)) =
      ((e.1.1 - ((fun _ ↦ L / 2) + z), e.1.2),
        (e.2.1 - ((fun _ ↦ L / 2) + z), e.2.2))
  congr 2 <;> abel

/-- The actual original paired-edge kinetic readout. -/
def legalMarkedPhysicalKineticEdge (q : ℕ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (e : LegalMarkedPhysicalEdge q) : ℝ :=
  kin e.1.2 e.2.2 (e.2.1 - e.1.1)

/-- The actual original paired-clock probe on the same physical edge. -/
def legalMarkedPhysicalProbeEdge (q : ℕ)
    (g : ℝ → ℝ → ℝ) (e : LegalMarkedPhysicalEdge q) : ℝ := g e.1.2 e.2.2

/-- Deterministic centering and actual rooting preserve the entire original
paired-edge kinetic readout exactly. -/
theorem legalMarkedPhysicalKineticEdge_rootedCenteredObservation
    (q : ℕ) (L : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (z : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q) :
    legalMarkedPhysicalKineticEdge q kin
      (physicalSceneRootedObservation (legalMarkedCenteredCoordinate q L) Prod.snd z e) =
        legalMarkedPhysicalKineticEdge q kin e := by
  simp only [legalMarkedPhysicalKineticEdge, physicalSceneRootedObservation,
    legalMarkedCenteredCoordinate, sub_sub_sub_cancel_right]

theorem integral_legalMarkedNormalizedOptimalPlan (q : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (f : LegalMarkedPhysicalEdge q → ℝ) :
    (∫ e, f e ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) =
      (L ^ q)⁻¹ * ∫ e, f e ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω := by
  rw [legalMarkedNormalizedOptimalPlan, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg hL q), smul_eq_mul]

theorem integral_legalMarkedOptimalPlan_tilted_decomposition (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedOptimalPlan q L r kin g t ω) =
        (∫ e, legalMarkedPhysicalKineticEdge q kin e
          ∂legalMarkedOptimalPlan q L r kin g t ω) +
        t * ∫ e, legalMarkedPhysicalProbeEdge q g e
          ∂legalMarkedOptimalPlan q L r kin g t ω := by
  change (∫ e, legalMarkedPhysicalKineticEdge q kin e +
      t * legalMarkedPhysicalProbeEdge q g e ∂legalMarkedOptimalPlan q L r kin g t ω) = _
  unfold legalMarkedOptimalPlan
  rw [integral_add
    (integrable_legalMarkedFixedOptimalPlan q _ _ L r kin g t ω _)
    ((integrable_legalMarkedFixedOptimalPlan q _ _ L r kin g t ω _).const_mul t),
    integral_const_mul]

/-- The actual selected probe is controlled by the original source count,
including every legal maximum-cardinality deficiency. -/
theorem abs_integral_legalMarkedOptimalPlan_probe_le_sourceCount
    (q : ℕ) (L r : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    {g : ℝ → ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G) (hgb : ∀ a b, |g a b| ≤ G)
    (t : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    |∫ e, legalMarkedPhysicalProbeEdge q g e ∂legalMarkedOptimalPlan q L r kin g t ω| ≤
      (mSourceCount ω : ℝ) * G := by
  classical
  unfold legalMarkedOptimalPlan
  rw [integral_legalMarkedFixedOptimalPlan]
  let σ := firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
    id id r kin g t ω
  change |∑ e ∈ σ.edges, g (mSourceMark ω e.1) (mTargetMark ω e.2)| ≤ _
  calc
    _ ≤ ∑ e ∈ σ.edges, |g (mSourceMark ω e.1) (mTargetMark ω e.2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ σ.edges, G := Finset.sum_le_sum (fun e he ↦ hgb _ _)
    _ = (σ.card : ℝ) * G := by simp [OTSelector.PartialMatching.card]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (σ.card_le.trans (min_le_left _ _))) hG

theorem integrable_legalMarkedOptimalPlan_probe (q : ℕ) (L r : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    {G : ℝ} (hG : 0 ≤ G) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rLaw : ℝ≥0) :
    Integrable (fun ω ↦ ∫ e, legalMarkedPhysicalProbeEdge q g e
      ∂legalMarkedOptimalPlan q L r kin g t ω) (twoMarkedCloudLaw q ℝ ℝ α β rLaw) := by
  let K : Kernel (TwoMarkedCloudSpace q ℝ ℝ) (LegalMarkedPhysicalEdge q) :=
    ⟨legalMarkedOptimalPlan q L r kin g t,
      measurable_legalMarkedOptimalPlan q L r hkin hg t⟩
  have hprobe : Measurable (legalMarkedPhysicalProbeEdge q g) := by
    change Measurable (fun e : LegalMarkedPhysicalEdge q ↦ g e.1.2 e.2.2)
    exact hg.comp (measurable_fst.snd.prodMk measurable_snd.snd)
  have hread : StronglyMeasurable (fun ω ↦ ∫ e, legalMarkedPhysicalProbeEdge q g e
      ∂legalMarkedOptimalPlan q L r kin g t ω) :=
    hprobe.stronglyMeasurable.integral_kernel (κ := K)
  apply ((integrable_mSourceCount q α β rLaw).mul_const G).mono'
    hread.aestronglyMeasurable
  exact .of_forall (fun ω ↦ by
    rw [Real.norm_eq_abs]
    exact abs_integral_legalMarkedOptimalPlan_probe_le_sourceCount q L r kin hG hgb t ω)

theorem abs_integral_integral_legalMarkedOptimalPlan_probe_le
    (q : ℕ) (L r : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    {G : ℝ} (hG : 0 ≤ G) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rLaw : ℝ≥0) :
    |∫ ω, ∫ e, legalMarkedPhysicalProbeEdge q g e
      ∂legalMarkedOptimalPlan q L r kin g t ω ∂twoMarkedCloudLaw q ℝ ℝ α β rLaw| ≤
        (rLaw : ℝ) * G := by
  have hint := integrable_legalMarkedOptimalPlan_probe q L r hkin hg hG hgb t α β rLaw
  calc
    _ ≤ ∫ ω, |∫ e, legalMarkedPhysicalProbeEdge q g e
        ∂legalMarkedOptimalPlan q L r kin g t ω|
          ∂twoMarkedCloudLaw q ℝ ℝ α β rLaw := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (mSourceCount ω : ℝ) * G
          ∂twoMarkedCloudLaw q ℝ ℝ α β rLaw :=
      integral_mono hint.abs ((integrable_mSourceCount q α β rLaw).mul_const G)
        (abs_integral_legalMarkedOptimalPlan_probe_le_sourceCount q L r kin hG hgb t)
    _ = _ := by rw [integral_mul_const, integral_mSourceCount_eq]

/-- Actual signed optimal pressure and the bounded original probe control
the normalized original kinetic energy, on the same original cloud law. -/
theorem integrable_and_integral_legalMarkedNormalizedOptimalPlan_kinetic_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (fun ω ↦ ∫ e, legalMarkedPhysicalKineticEdge q kin e
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ∧
    (∫ ω, ∫ e, legalMarkedPhysicalKineticEdge q kin e
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤
      legalMarkedScalePressure q id id α β kin g L t + |t| * G := by
  let P := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))
  let K : TwoMarkedCloudSpace q ℝ ℝ → ℝ := fun ω ↦
    ∫ e, legalMarkedPhysicalKineticEdge q kin e
      ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω
  let B : TwoMarkedCloudSpace q ℝ ℝ → ℝ := fun ω ↦
    ∫ e, legalMarkedPhysicalProbeEdge q g e
      ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω
  let T : TwoMarkedCloudSpace q ℝ ℝ → ℝ := fun ω ↦
    ∫ e, legalMarkedPhysicalTiltedEdge q kin g t e
      ∂legalMarkedOptimalPlan q L (L ^ q) kin g t ω
  have ht := integrable_and_integral_legalMarkedOptimalPlan_eq_pressure
    q hq hL.le α β hC hG hkin hkb hhom hg hgb t
  have hb : Integrable B P :=
    integrable_legalMarkedOptimalPlan_probe q L (L ^ q) hkin hg hG hgb t α β _
  have hkt (ω) : K ω = T ω - t * B ω := by
    have h := integral_legalMarkedOptimalPlan_tilted_decomposition q L (L ^ q) kin g t ω
    change T ω = K ω + t * B ω at h
    linarith
  have hk : Integrable K P := (ht.1.sub (hb.const_mul t)).congr
    (.of_forall (fun ω ↦ (hkt ω).symm))
  have hkeq : (∫ ω, K ω ∂P) =
      legalMarkedPressure q id id α β (Real.toNNReal (L ^ q)) kin g t -
        t * ∫ ω, B ω ∂P := by
    simp_rw [hkt]
    rw [integral_sub ht.1 (hb.const_mul t), integral_const_mul]
    exact congrArg (fun x ↦ x - t * ∫ ω, B ω ∂P) ht.2
  have hV : 0 < L ^ q := pow_pos hL q
  have hbmean : |∫ ω, B ω ∂P| ≤ L ^ q * G := by
    have h := abs_integral_integral_legalMarkedOptimalPlan_probe_le
      q L (L ^ q) hkin hg hG hgb t α β (Real.toNNReal (L ^ q))
    rwa [Real.coe_toNNReal _ hV.le] at h
  have hupper : (∫ ω, K ω ∂P) ≤
      legalMarkedPressure q id id α β (Real.toNNReal (L ^ q)) kin g t +
        |t| * (L ^ q * G) := by
    rw [hkeq]
    have hmul : -(t * ∫ ω, B ω ∂P) ≤ |t| * (L ^ q * G) := by
      calc
        _ ≤ |t * ∫ ω, B ω ∂P| := neg_le_abs _
        _ = |t| * |∫ ω, B ω ∂P| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hbmean (abs_nonneg t)
    linarith
  have hnorm (ω) : (∫ e, legalMarkedPhysicalKineticEdge q kin e
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) = (L ^ q)⁻¹ * K ω :=
    integral_legalMarkedNormalizedOptimalPlan q hL.le kin g t ω _
  constructor
  · have h := hk.const_mul (L ^ q)⁻¹
    exact h.congr (.of_forall (fun ω ↦ (hnorm ω).symm))
  · simp_rw [hnorm]
    rw [integral_const_mul]
    calc
      _ ≤ (L ^ q)⁻¹ *
          (legalMarkedPressure q id id α β (Real.toNNReal (L ^ q)) kin g t +
            |t| * (L ^ q * G)) := mul_le_mul_of_nonneg_left hupper (inv_nonneg.mpr hV.le)
      _ = legalMarkedScalePressure q id id α β kin g L t + |t| * G := by
        simp only [legalMarkedScalePressure, hL, ↓reduceIte]
        field_simp

/-- Nonnegative original kinetic energy has the same bound as an actual
nonnegative double integral on the original normalized optimal plans. -/
theorem lintegral_legalMarkedNormalizedOptimalPlan_kinetic_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e)
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤
      ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) := by
  have h := integrable_and_integral_legalMarkedNormalizedOptimalPlan_kinetic_le
    q hq hL α β hC hG hkin hkb hhom hg hgb t
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hL q)).ne'
  have hinner (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      Integrable (legalMarkedPhysicalKineticEdge q kin)
        (legalMarkedNormalizedOptimalPlan q L kin g t ω) := by
    exact (integrable_legalMarkedFixedOptimalPlan q (mSourceCount ω) (mTargetCount ω)
      L (L ^ q) kin g t ω _).smul_measure (ENNReal.inv_ne_top.mpr hV0)
  have hnonneg (e : LegalMarkedPhysicalEdge q) :
      0 ≤ legalMarkedPhysicalKineticEdge q kin e := hkn _ _ _
  have hinner_eq (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      (∫⁻ e, ENNReal.ofReal (legalMarkedPhysicalKineticEdge q kin e)
        ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) =
      ENNReal.ofReal (∫ e, legalMarkedPhysicalKineticEdge q kin e
        ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    (ofReal_integral_eq_lintegral_ofReal (hinner ω) (.of_forall hnonneg)).symm
  simp_rw [hinner_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal h.1
    (.of_forall (fun ω ↦ integral_nonneg hnonneg))]
  exact ENNReal.ofReal_le_ofReal h.2

end OTSelector.Reconstruction
