import OTSelector.Reconstruction.MarkedStationaryValueLegalInputColoredScene

/-! Original Haar-rooted input first moments, before any matching selection. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

instance legalInputRootMomentsSourceEmpiricalFinite (q : ℕ) (L : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : IsFiniteMeasure (legalMarkedSourceEmpiricalMeasure q L ω) := by
  unfold legalMarkedSourceEmpiricalMeasure
  infer_instance

instance legalInputRootMomentsTargetEmpiricalFinite (q : ℕ) (L : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : IsFiniteMeasure (legalMarkedTargetEmpiricalMeasure q L ω) := by
  unfold legalMarkedTargetEmpiricalMeasure
  infer_instance

theorem integral_legalMarkedSourceEmpiricalMeasure_rooted_test
    (q : ℕ) (L : ℝ) (h : LegalMarkedPhysicalPoint q → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    (∫ p, h (legalMarkedCenteredCoordinate q L p - z, p.2)
      ∂legalMarkedSourceEmpiricalMeasure q L ω) =
        legalMarkedRootedSourceInputTest q L h ω z := by
  rw [legalMarkedSourceEmpiricalMeasure,
    integral_finsetSum_measure (fun i _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac]
  rfl

theorem integral_legalMarkedTargetEmpiricalMeasure_rooted_test
    (q : ℕ) (L : ℝ) (h : LegalMarkedPhysicalPoint q → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    (∫ p, h (legalMarkedCenteredCoordinate q L p - z, p.2)
      ∂legalMarkedTargetEmpiricalMeasure q L ω) =
        legalMarkedRootedTargetInputTest q L h ω z := by
  rw [legalMarkedTargetEmpiricalMeasure,
    integral_finsetSum_measure (fun i _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac]
  rfl

/-- The actual full original source input has the correct uniform local first
moment under its same original Haar root. No count clipping is needed. -/
theorem lintegral_legalMarkedRootedSourceInputTest_abs_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {h : LegalMarkedPhysicalPoint q → ℝ} {G : ℝ} (hbound : ∀ p, |h p| ≤ G)
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (hUfin : volume U ≠ ∞)
    (hzero : ∀ p, p.1 ∉ U → h p = 0) :
    (∫⁻ ω, ∫⁻ z, ENNReal.ofReal |legalMarkedRootedSourceInputTest q L h ω z|
      ∂legalMarkedHaarRootLaw q L
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ ENNReal.ofReal G * volume U := by
  have hV : 0 < L ^ q := pow_pos hL q
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 := (ENNReal.ofReal_pos.mpr hV).ne'
  have hconst : ((ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal G * volume U) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV0)
      ENNReal.ofReal_ne_top) hUfin
  have hmean : (∫⁻ ω, legalMarkedSourceEmpiricalMeasure q L ω univ
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) = ENNReal.ofReal (L ^ q) := by
    simpa only [mem_univ, ofPred_true, measure_univ, mul_one, Real.coe_toNNReal _ hV.le] using
      lintegral_legalMarkedSourceEmpiricalMeasure_clock q L α β (Real.toNNReal (L ^ q)) MeasurableSet.univ
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal G * volume U *
        legalMarkedSourceEmpiricalMeasure q L ω univ
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)) := by
      apply lintegral_mono
      intro ω
      simp_rw [← integral_legalMarkedSourceEmpiricalMeasure_rooted_test]
      exact lintegral_cavityRoot_abs_rootedPointReadout_le _
        (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
        Prod.snd hbound U hU hzero (haarRootCube (Fin q) (L / 2)) (L ^ q)
    _ = ENNReal.ofReal G * volume U := by
      rw [lintegral_const_mul' _ _ hconst, hmean]
      calc
        _ = ((ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal (L ^ q)) *
            (ENNReal.ofReal G * volume U) := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel hV0 ENNReal.ofReal_ne_top, one_mul]

/-- The original target uses the same local first moment normalization. -/
theorem lintegral_legalMarkedRootedTargetInputTest_abs_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {h : LegalMarkedPhysicalPoint q → ℝ} {G : ℝ} (hbound : ∀ p, |h p| ≤ G)
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (hUfin : volume U ≠ ∞)
    (hzero : ∀ p, p.1 ∉ U → h p = 0) :
    (∫⁻ ω, ∫⁻ z, ENNReal.ofReal |legalMarkedRootedTargetInputTest q L h ω z|
      ∂legalMarkedHaarRootLaw q L
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤ ENNReal.ofReal G * volume U := by
  have hV : 0 < L ^ q := pow_pos hL q
  have hV0 : ENNReal.ofReal (L ^ q) ≠ 0 := (ENNReal.ofReal_pos.mpr hV).ne'
  have hconst : ((ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal G * volume U) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV0)
      ENNReal.ofReal_ne_top) hUfin
  have hmean : (∫⁻ ω, legalMarkedTargetEmpiricalMeasure q L ω univ
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) = ENNReal.ofReal (L ^ q) := by
    simpa only [mem_univ, ofPred_true, measure_univ, mul_one, Real.coe_toNNReal _ hV.le] using
      lintegral_legalMarkedTargetEmpiricalMeasure_clock q L α β (Real.toNNReal (L ^ q)) MeasurableSet.univ
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal G * volume U *
        legalMarkedTargetEmpiricalMeasure q L ω univ
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)) := by
      apply lintegral_mono
      intro ω
      simp_rw [← integral_legalMarkedTargetEmpiricalMeasure_rooted_test]
      exact lintegral_cavityRoot_abs_rootedPointReadout_le _
        (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
        Prod.snd hbound U hU hzero (haarRootCube (Fin q) (L / 2)) (L ^ q)
    _ = ENNReal.ofReal G * volume U := by
      rw [lintegral_const_mul' _ _ hconst, hmean]
      calc
        _ = ((ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal (L ^ q)) *
            (ENNReal.ofReal G * volume U) := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel hV0 ENNReal.ofReal_ne_top, one_mul]

/-- Actual colored local mass is exactly the sum of the two original rooted
input count tests, before optimizer selection. -/
theorem legalMarkedRootedColoredInputMeasure_spatialWindow
    (q : ℕ) {L : ℝ} (hL : 0 < L) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    legalMarkedRootedColoredInputMeasure q L p {x | x.1.1 ∈ U} =
      ENNReal.ofReal (legalMarkedRootedSourceInputTest q L
        ((Prod.fst ⁻¹' U).indicator (fun _ ↦ 1)) p.1 p.2) +
      ENNReal.ofReal (legalMarkedRootedTargetInputTest q L
        ((Prod.fst ⁻¹' U).indicator (fun _ ↦ 1)) p.1 p.2) := by
  let S : Set (LegalColoredInputPoint q) := {x | x.1.1 ∈ U}
  have hS : MeasurableSet S := hU.preimage measurable_fst.fst
  let F : LegalColoredInputPoint q → ℝ := S.indicator (fun _ ↦ 1)
  have hF : Measurable F := measurable_const.indicator hS
  have hF0 : ∀ x, 0 ≤ F x := fun x ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) x
  have hFi : Integrable F (legalMarkedRootedColoredInputMeasure q L p) :=
    Integrable.of_bound hF.aestronglyMeasurable 1 (.of_forall (fun x ↦ by
      by_cases hx : x ∈ S <;> simp [F, hx]))
  have he := ofReal_integral_eq_lintegral_ofReal hFi (.of_forall hF0)
  have hFpoint (x : LegalColoredInputPoint q) : ENNReal.ofReal (F x) =
      S.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ S <;> simp [F, hx]
  simp_rw [hFpoint] at he
  rw [lintegral_indicator hS, lintegral_one, Measure.restrict_apply_univ,
    integral_legalMarkedRootedColoredInputMeasure q hL F p] at he
  have hzero (x : LegalMarkedPhysicalPoint q) : F (x, 0) =
      (Prod.fst ⁻¹' U).indicator (fun _ ↦ (1 : ℝ)) x := rfl
  have hone (x : LegalMarkedPhysicalPoint q) : F (x, 1) =
      (Prod.fst ⁻¹' U).indicator (fun _ ↦ (1 : ℝ)) x := rfl
  simp_rw [hzero, hone] at he
  have hn (x : LegalMarkedPhysicalPoint q) : 0 ≤ (Prod.fst ⁻¹' U).indicator (fun _ ↦ (1 : ℝ)) x :=
    indicator_nonneg (fun _ _ ↦ zero_le_one) x
  have hsrc0 : 0 ≤ legalMarkedRootedSourceInputTest q L
      ((Prod.fst ⁻¹' U).indicator (fun _ ↦ 1)) p.1 p.2 := Finset.sum_nonneg (fun i _ ↦ hn _)
  have htgt0 : 0 ≤ legalMarkedRootedTargetInputTest q L
      ((Prod.fst ⁻¹' U).indicator (fun _ ↦ 1)) p.1 p.2 := Finset.sum_nonneg (fun i _ ↦ hn _)
  rw [ENNReal.ofReal_add hsrc0 htgt0] at he
  exact he.symm

/-- The full original colored inputs have uniformly bounded local mass under
their actual Haar root, independently of physical scale and matching choice. -/
theorem lintegral_legalMarkedRootedColoredInputMeasure_spatialWindow_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) (hUfin : volume U ≠ ∞) :
    (∫⁻ p, legalMarkedRootedColoredInputMeasure q L p {x | x.1.1 ∈ U}
      ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
        (legalMarkedHaarRootLaw q L)) ≤ 2 * volume U := by
  let h : LegalMarkedPhysicalPoint q → ℝ := (Prod.fst ⁻¹' U).indicator (fun _ ↦ 1)
  have hh : Measurable h := measurable_const.indicator (hU.preimage measurable_fst)
  have hbound : ∀ p, |h p| ≤ 1 := fun p ↦ by
    by_cases hp : p.1 ∈ U <;> simp [h, hp]
  have hzero : ∀ p, p.1 ∉ U → h p = 0 := fun p hp ↦ by simp [h, hp]
  have hnonneg : ∀ p, 0 ≤ h p := fun p ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) p
  let kin : ℝ → ℝ → (Fin q → ℝ) → ℝ := fun _ _ _ ↦ 0
  let g : ℝ → ℝ → ℝ := fun _ _ ↦ 0
  have hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)) := measurable_const
  have hg : Measurable (Function.uncurry g) := measurable_const
  obtain ⟨_, hMs⟩ := measurable_legalMarkedRooted_sourceTests q L hk hg 0 hh
  obtain ⟨_, hMt⟩ := measurable_legalMarkedRooted_targetTests q L hk hg 0 hh
  have hs : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      ENNReal.ofReal (legalMarkedRootedSourceInputTest q L h p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hMs
  have ht : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      ENNReal.ofReal (legalMarkedRootedTargetInputTest q L h p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hMt
  let : IsProbabilityMeasure (legalMarkedHaarRootLaw q L) :=
    isProbabilityMeasure_legalMarkedHaarRootLaw q hL
  simp_rw [legalMarkedRootedColoredInputMeasure_spatialWindow q hL hU]
  rw [lintegral_add_left hs, lintegral_prod _ hs.aemeasurable,
    lintegral_prod _ ht.aemeasurable]
  have hsbound := lintegral_legalMarkedRootedSourceInputTest_abs_le q hL α β hbound U hU hUfin hzero
  have htbound := lintegral_legalMarkedRootedTargetInputTest_abs_le q hL α β hbound U hU hUfin hzero
  have hsn : ∀ ω z, 0 ≤ legalMarkedRootedSourceInputTest q L h ω z :=
    fun _ _ ↦ Finset.sum_nonneg (fun i _ ↦ hnonneg _)
  have htn : ∀ ω z, 0 ≤ legalMarkedRootedTargetInputTest q L h ω z :=
    fun _ _ ↦ Finset.sum_nonneg (fun i _ ↦ hnonneg _)
  simp_rw [abs_of_nonneg (hsn _ _), ENNReal.ofReal_one, one_mul] at hsbound
  simp_rw [abs_of_nonneg (htn _ _), ENNReal.ofReal_one, one_mul] at htbound
  exact (add_le_add hsbound htbound).trans_eq (by rw [two_mul])

end OTSelector.Reconstruction
