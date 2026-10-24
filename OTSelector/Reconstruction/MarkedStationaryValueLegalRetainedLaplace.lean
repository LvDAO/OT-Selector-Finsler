import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplace

/-!
# Actual retained endpoint Laplace tests

The same actual legal optimizer loses only the original unmatched endpoint
mass. Nonnegative local endpoint tests turn that exact loss into a joint
Laplace error, without assigning an iid law to retained or missing points.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem exp_neg_sub_le_sub_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp (-x) - Real.exp (-y) ≤ y - x := by
  have hf : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hsecond : 1 - Real.exp (-(y - x)) ≤ y - x := by
    linarith [Real.one_sub_le_exp_neg (y - x)]
  have hsecond0 : 0 ≤ 1 - Real.exp (-(y - x)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  calc
    Real.exp (-x) - Real.exp (-y) = Real.exp (-x) * (1 - Real.exp (-(y - x))) := by
      rw [hf]
      ring
    _ ≤ 1 * (y - x) := mul_le_mul hfirst hsecond hsecond0 zero_le_one
    _ = y - x := one_mul _

/-- A nonnegative endpoint readout has a globally bounded Laplace sensitivity. -/
theorem abs_exp_neg_sub_exp_neg_le_abs_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hxy))),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    exact (exp_neg_sub_le_sub_of_le hx hxy).trans_eq (by ring)
  · rw [abs_sub_comm (Real.exp (-x)), abs_sub_comm x]
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hyx))),
      abs_of_nonpos (sub_nonpos.mpr hyx)]
    exact (exp_neg_sub_le_sub_of_le hy hyx).trans_eq (by ring)

/-- Joint Laplace test of the actual retained endpoints of the same canonical
legal finite optimum and its same Haar root. -/
def legalMarkedRootedRetainedLaplace (q : ℕ) (L : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (h k : LegalMarkedPhysicalPoint q → ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) : ℝ :=
  Real.exp (-(legalMarkedRootedSourceTest q L kin g t h p.1 p.2 +
    legalMarkedRootedTargetTest q L kin g t k p.1 p.2))

/-- Only the original unused source and target tests are charged. -/
theorem abs_legalMarkedRootedRetainedLaplace_sub_input_le
    (q : ℕ) (L : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (h k : LegalMarkedPhysicalPoint q → ℝ)
    (hh : ∀ x, 0 ≤ h x) (hk : ∀ x, 0 ≤ k x)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    |legalMarkedRootedRetainedLaplace q L kin g t h k p -
      legalMarkedRootedInputLaplace q L h k p| ≤
      |legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
        legalMarkedRootedSourceInputTest q L h p.1 p.2| +
      |legalMarkedRootedTargetTest q L kin g t k p.1 p.2 -
        legalMarkedRootedTargetInputTest q L k p.1 p.2| := by
  have hsrc : 0 ≤ legalMarkedRootedSourceTest q L kin g t h p.1 p.2 :=
    Finset.sum_nonneg (fun e _ ↦ hh _)
  have htgt : 0 ≤ legalMarkedRootedTargetTest q L kin g t k p.1 p.2 :=
    Finset.sum_nonneg (fun e _ ↦ hk _)
  have hsrcin : 0 ≤ legalMarkedRootedSourceInputTest q L h p.1 p.2 :=
    Finset.sum_nonneg (fun _ _ ↦ hh _)
  have htgtin : 0 ≤ legalMarkedRootedTargetInputTest q L k p.1 p.2 :=
    Finset.sum_nonneg (fun _ _ ↦ hk _)
  have he := abs_exp_neg_sub_exp_neg_le_abs_sub (add_nonneg hsrc htgt) (add_nonneg hsrcin htgtin)
  apply he.trans
  convert abs_add_le (legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
    legalMarkedRootedSourceInputTest q L h p.1 p.2)
    (legalMarkedRootedTargetTest q L kin g t k p.1 p.2 -
      legalMarkedRootedTargetInputTest q L k p.1 p.2) using 1
  congr 1
  ring

/-- Actual expectation retains the same original local missing-mass budget. -/
theorem lintegral_legalMarkedRootedRetainedLaplace_error_le
    (q : ℕ) {L : ℝ} (hL : 0 < L) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h k : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x) :
    (∫⁻ p, ENNReal.ofReal |legalMarkedRootedRetainedLaplace q L kin g t h k p -
      legalMarkedRootedInputLaplace q L h k p|
      ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
        (legalMarkedHaarRootLaw q L)) ≤
      legalMarkedRootedSourceTestError q L α β kin g t h +
        legalMarkedRootedTargetTestError q L α β kin g t k := by
  obtain ⟨hsrc, hsrcin⟩ := measurable_legalMarkedRooted_sourceTests q L hkin hg t hh
  obtain ⟨htgt, htgtin⟩ := measurable_legalMarkedRooted_targetTests q L hkin hg t hk
  let : IsProbabilityMeasure (legalMarkedHaarRootLaw q L) :=
    isProbabilityMeasure_legalMarkedHaarRootLaw q hL
  have hMs : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      ENNReal.ofReal |legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
        legalMarkedRootedSourceInputTest q L h p.1 p.2|) :=
    ENNReal.measurable_ofReal.comp (hsrc.sub hsrcin).abs
  have hMt : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      ENNReal.ofReal |legalMarkedRootedTargetTest q L kin g t k p.1 p.2 -
        legalMarkedRootedTargetInputTest q L k p.1 p.2|) :=
    ENNReal.measurable_ofReal.comp (htgt.sub htgtin).abs
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal
        (|legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
          legalMarkedRootedSourceInputTest q L h p.1 p.2| +
        |legalMarkedRootedTargetTest q L kin g t k p.1 p.2 -
          legalMarkedRootedTargetInputTest q L k p.1 p.2|)
        ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
          (legalMarkedHaarRootLaw q L) := lintegral_mono (fun p ↦
      ENNReal.ofReal_le_ofReal (abs_legalMarkedRootedRetainedLaplace_sub_input_le
        q L kin g t h k hh0 hk0 p))
    _ = _ := by
      simp_rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      rw [lintegral_add_left hMs, lintegral_prod _ hMs.aemeasurable,
        lintegral_prod _ hMt.aemeasurable]
      rfl

private theorem abs_integral_sub_le_lintegral_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r i : Ω → ℝ} (hr : Measurable r) (hi : Measurable i)
    (hbr : ∀ x, |r x| ≤ 1) (hbi : ∀ x, |i x| ≤ 1) :
    |(∫ x, r x ∂P) - ∫ x, i x ∂P| ≤
      (∫⁻ x, ENNReal.ofReal |r x - i x| ∂P).toReal := by
  have hri : Integrable r P := ⟨hr.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (.of_forall hbr)⟩
  have hii : Integrable i P := ⟨hi.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (.of_forall hbi)⟩
  have hd := hri.sub hii
  have he := ofReal_integral_eq_lintegral_ofReal hd.abs
    (.of_forall (fun x ↦ abs_nonneg (r x - i x)))
  have he' := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x ↦ abs_nonneg _))] at he'
  simp only [Pi.sub_apply] at he'
  rw [← he', ← integral_sub hri hii]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun x ↦ r x - i x)

private theorem measurable_and_bounded_legalMarkedRootedLaplace
    (q : ℕ) (L : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h k : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x) :
    (Measurable (legalMarkedRootedRetainedLaplace q L kin g t h k) ∧
      ∀ x, |legalMarkedRootedRetainedLaplace q L kin g t h k x| ≤ 1) ∧
    (Measurable (legalMarkedRootedInputLaplace q L h k) ∧
      ∀ x, |legalMarkedRootedInputLaplace q L h k x| ≤ 1) := by
  obtain ⟨hrs, his⟩ := measurable_legalMarkedRooted_sourceTests q L hkin hg t hh
  obtain ⟨hrt, hit⟩ := measurable_legalMarkedRooted_targetTests q L hkin hg t hk
  constructor
  · refine ⟨(hrs.add hrt).neg.exp, fun x ↦ ?_⟩
    rw [legalMarkedRootedRetainedLaplace, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (add_nonneg (Finset.sum_nonneg (fun _ _ ↦ hh0 _))
      (Finset.sum_nonneg (fun _ _ ↦ hk0 _)))
  · refine ⟨(his.add hit).neg.exp, fun x ↦ ?_⟩
    rw [legalMarkedRootedInputLaplace, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (add_nonneg (Finset.sum_nonneg (fun _ _ ↦ hh0 _))
      (Finset.sum_nonneg (fun _ _ ↦ hk0 _)))

/-- The actual scalar-bin coupling removes the Laplace loss of both endpoint
colors under the original environment and original independent Haar root. -/
theorem scalarBins_tendsto_legalMarkedRootedRetainedLaplace_error
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ p.2 - p.1) (q : ℕ) (hq : 0 < q)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h k : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x) {H K : ℝ}
    (hhb : ∀ p, |h p| ≤ H) (hkb : ∀ p, |k p| ≤ K)
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (hUfin : volume U ≠ ∞)
    (hhzero : ∀ p, p.1 ∉ U → h p = 0) (hkzero : ∀ p, p.1 ∉ U → k p = 0) :
    Tendsto (fun L : ℝ ↦ ∫⁻ p, ENNReal.ofReal
      |legalMarkedRootedRetainedLaplace q L kin g t h k p - legalMarkedRootedInputLaplace q L h k p|
      ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
        (legalMarkedHaarRootLaw q L)) atTop (𝓝 0) := by
  have hs := (scalarBins_tendsto_legalMarkedRooted_spatialTestErrors D hδ π α β hπ hI hgap
    q hq hkin hg t hh hhb U hU hUfin hhzero).1
  have ht := (scalarBins_tendsto_legalMarkedRooted_spatialTestErrors D hδ π α β hπ hI hgap
    q hq hkin hg t hk hkb U hU hUfin hkzero).2
  have hsum : Tendsto (fun L ↦ legalMarkedRootedSourceTestError q L α β kin g t h +
      legalMarkedRootedTargetTestError q L α β kin g t k) atTop (𝓝 0) := by
    simpa only [add_zero] using hs.add ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (.of_forall (fun _ ↦ bot_le))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact lintegral_legalMarkedRootedRetainedLaplace_error_le q hL α β hkin hg t hh hk hh0 hk0

/-- The literal retained source and target endpoints of the actual canonical
legal optimum have the original independent Poisson joint Laplace functional
in every fixed physical window, along all real box scales. -/
theorem scalarBins_tendsto_integral_legalMarkedRootedRetainedLaplace
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ p.2 - p.1) (q : ℕ) (hq : 0 < q)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {S : ℝ} (hS : 0 ≤ S) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    {h k : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x) {H K : ℝ}
    (hhb : ∀ p, |h p| ≤ H) (hkb : ∀ p, |k p| ≤ K)
    (hhzero : ∀ p, p.1 ∉ U → h p = 0) (hkzero : ∀ p, p.1 ∉ U → k p = 0) :
    Tendsto (fun L : ℝ ↦ ∫ p, legalMarkedRootedRetainedLaplace q L kin g t h k p
      ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
        (legalMarkedHaarRootLaw q L)) atTop
      (𝓝 (∫ b, legalInputBlockLaplace h k b ∂legalInputPoissonWindowLaw q U α β)) := by
  have hUfin : volume U ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono hsub)
      (show volume (haarRootCube (Fin q) S) < ∞ from isCompact_Icc.measure_lt_top)).ne
  have hnn := scalarBins_tendsto_legalMarkedRootedRetainedLaplace_error D hδ π α β hπ hI hgap
    q hq hkin hg t hh hk hh0 hk0 hhb hkb U hU hUfin hhzero hkzero
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hnn
  simp only [Function.comp_def, ENNReal.toReal_zero] at hreal
  have hdiff : Tendsto (fun L : ℝ ↦
      (∫ p, legalMarkedRootedRetainedLaplace q L kin g t h k p
        ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
          (legalMarkedHaarRootLaw q L)) -
      (∫ p, legalMarkedRootedInputLaplace q L h k p
        ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
          (legalMarkedHaarRootLaw q L))) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero' (.of_forall (fun L ↦ norm_nonneg _)) ?_ hreal
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    let : IsProbabilityMeasure (legalMarkedHaarRootLaw q L) :=
      isProbabilityMeasure_legalMarkedHaarRootLaw q hL
    obtain ⟨⟨hr, hbr⟩, ⟨hi, hbi⟩⟩ :=
      measurable_and_bounded_legalMarkedRootedLaplace q L hkin hg t hh hk hh0 hk0
    simpa only [Real.norm_eq_abs] using abs_integral_sub_le_lintegral_error _ hr hi hbr hbi
  have hinput := tendsto_integral_legalMarkedRootedInputLaplace q hS hU hsub hpos α β
    hh hk hh0 hk0 hhzero hkzero
  have h := hdiff.add hinput
  simpa only [sub_add_cancel, zero_add] using h

end OTSelector.Reconstruction
