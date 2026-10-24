import OTSelector.Reconstruction.MarkedStationaryValueLegalInputRootLaw
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneSpatialDefect

/-!
# Literal original window sums and their Poisson Laplace tests

Every retained finite-prefix sum uses the original observations in their
original index order. Compact spatial support removes discarded observations
exactly, before the Haar-rooted physical Poisson law is applied.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Sum a physical endpoint test on the actual finite window enumeration. -/
def legalInputBlockTest {X : Type*} (h : X → ℝ) (b : BlockData X) : ℝ := ∑ i, h (b.2 i)

theorem measurable_legalInputBlockTest {X : Type*} [MeasurableSpace X]
    {h : X → ℝ} (hh : Measurable h) : Measurable (legalInputBlockTest h) := by
  intro T hT
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  exact (Finset.measurable_sum Finset.univ
    (fun i _ ↦ hh.comp (measurable_pi_apply i))) hT

/-- Restriction keeps exactly all contributions of a test supported on the
chosen window. No omitted original observation receives a new mark or law. -/
theorem legalInputBlockTest_restrictedPrefix
    {X : Type*} [MeasurableSpace X] (h : X → ℝ) (S : Set X)
    (hzero : ∀ x, x ∉ S → h x = 0) (z : ℕ × (ℕ → X)) :
    legalInputBlockTest h (restrictedPrefix S z) = ∑ i : Fin z.1, h (z.2 i) := by
  classical
  let s := Finset.univ.filter (fun i : Fin z.1 ↦ restrictionLabel S (z.2 i) = true)
  let e : Fin s.card ≃ ↥s := (s.orderIsoOfFin rfl).toEquiv
  change (∑ j : Fin s.card, h (z.2 (e j).1)) = _
  calc
    _ = ∑ i : ↥s, h (z.2 i.1) := e.sum_comp (fun i : ↥s ↦ h (z.2 i.1))
    _ = ∑ i ∈ s, h (z.2 i) := Finset.sum_coe_sort s (fun i : Fin z.1 ↦ h (z.2 i))
    _ = ∑ i : Fin z.1, h (z.2 i) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      apply hzero
      intro hmem
      apply hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [restrictionLabel, hmem, ↓reduceIte]

/-- The same supported test can be evaluated after physical placement or
before restriction of the original used prefix. -/
theorem legalInputBlockTest_map_restrictedPrefix
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (h : Y → ℝ) (f : X → Y) (S : Set Y)
    (hzero : ∀ y, y ∉ S → h y = 0) (z : ℕ × (ℕ → X)) :
    legalInputBlockTest h (mapBlockData f (restrictedPrefix (f ⁻¹' S) z)) =
      ∑ i : Fin z.1, h (f (z.2 i)) := by
  rw [mapBlockData_restrictedPrefix]
  exact legalInputBlockTest_restrictedPrefix h S hzero (z.1, fun i ↦ f (z.2 i))

/-- Joint Laplace test of the two original finite physical point clouds. -/
def legalInputBlockLaplace {X : Type*} (h k : X → ℝ) (b : BlockData X × BlockData X) : ℝ :=
  Real.exp (-(legalInputBlockTest h b.1 + legalInputBlockTest k b.2))

theorem measurable_legalInputBlockLaplace {X : Type*} [MeasurableSpace X]
    {h k : X → ℝ} (hh : Measurable h) (hk : Measurable k) :
    Measurable (legalInputBlockLaplace h k) :=
  (((measurable_legalInputBlockTest hh).comp measurable_fst).add
    ((measurable_legalInputBlockTest hk).comp measurable_snd)).neg.exp

theorem abs_legalInputBlockLaplace_le_one {X : Type*}
    {h k : X → ℝ} (hh : ∀ x, 0 ≤ h x) (hk : ∀ x, 0 ≤ k x)
    (b : BlockData X × BlockData X) : |legalInputBlockLaplace h k b| ≤ 1 := by
  rw [legalInputBlockLaplace, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (add_nonneg (Finset.sum_nonneg (fun i _ ↦ hh _))
    (Finset.sum_nonneg (fun i _ ↦ hk _)))

/-- Original actual Haar-rooted inputs have the joint physical Poisson
Laplace functional on each fixed physical window. -/
theorem tendsto_integral_legalInputRootAverageLaw_laplace (q : ℕ)
    {S : ℝ} (hS : 0 ≤ S) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {h k : ((Fin q → ℝ) × ℝ) → ℝ} (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x) :
    Tendsto (fun L : ℝ ↦ ∫ b, legalInputBlockLaplace h k b
      ∂legalInputRootAverageLaw q L U α β) atTop
      (𝓝 (∫ b, legalInputBlockLaplace h k b ∂legalInputPoissonWindowLaw q U α β)) :=
  tendsto_integral_legalInputRootAverageLaw q hS hU hsub hpos α β
    (measurable_legalInputBlockLaplace hh hk) zero_le_one
    (abs_legalInputBlockLaplace_le_one hh0 hk0)

/-- The source input test in the actual optimizer's coordinates is precisely
the sum on its same original physical window prefix. -/
theorem legalInputBlockTest_rootWindow_sourceInput
    (q : ℕ) {L : ℝ} (hL : 0 < L) (U : Set (Fin q → ℝ))
    (h : LegalMarkedPhysicalPoint q → ℝ) (hzero : ∀ p, p.1 ∉ U → h p = 0)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    legalInputBlockTest h (legalInputRootWindowPrefix q (Real.toNNReal L) U (z, ω.1)) =
      legalMarkedRootedSourceInputTest q L h ω z := by
  rw [legalInputRootWindowPrefix,
    legalInputBlockTest_map_restrictedPrefix h (legalInputRootPoint q (Real.toNNReal L))
      (Prod.fst ⁻¹' U) (fun p hp ↦ hzero p hp) (legalInputTaggedOriginalCloud q (z, ω.1))]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Prod.ext
  · funext j
    simp only [legalInputTaggedOriginalCloud, legalInputRootPoint, legalInputPhysicalPoint,
      legalMarkedRootedSourcePoint, legalMarkedCenteredCoordinate, legalMarkedPhysicalEdge,
      mSourcePoint, Real.coe_toNNReal _ hL.le, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · rfl

/-- The target uses the same root and the same literal physical restriction. -/
theorem legalInputBlockTest_rootWindow_targetInput
    (q : ℕ) {L : ℝ} (hL : 0 < L) (U : Set (Fin q → ℝ))
    (h : LegalMarkedPhysicalPoint q → ℝ) (hzero : ∀ p, p.1 ∉ U → h p = 0)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    legalInputBlockTest h (legalInputRootWindowPrefix q (Real.toNNReal L) U (z, ω.2)) =
      legalMarkedRootedTargetInputTest q L h ω z := by
  rw [legalInputRootWindowPrefix,
    legalInputBlockTest_map_restrictedPrefix h (legalInputRootPoint q (Real.toNNReal L))
      (Prod.fst ⁻¹' U) (fun p hp ↦ hzero p hp) (legalInputTaggedOriginalCloud q (z, ω.2))]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Prod.ext
  · funext j
    simp only [legalInputTaggedOriginalCloud, legalInputRootPoint, legalInputPhysicalPoint,
      legalMarkedRootedTargetPoint, legalMarkedCenteredCoordinate, legalMarkedPhysicalEdge,
      mTargetPoint, Real.coe_toNNReal _ hL.le, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · rfl

/-- The full original empirical inputs, rooted at the same Haar observation
as their actual legal optimum, with no matching selection. -/
def legalMarkedRootedInputLaplace (q : ℕ) (L : ℝ)
    (h k : LegalMarkedPhysicalPoint q → ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) : ℝ :=
  Real.exp (-(legalMarkedRootedSourceInputTest q L h p.1 p.2 +
    legalMarkedRootedTargetInputTest q L k p.1 p.2))

/-- The physical-prefix law is exactly the same environment/root test as the
original full inputs of the canonical legal optimizer. -/
theorem integral_legalInputRootAverageLaw_laplace_eq_input
    (q : ℕ) {L : ℝ} (hL : 0 < L) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {h k : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) (hk : Measurable k)
    (hhzero : ∀ p, p.1 ∉ U → h p = 0) (hkzero : ∀ p, p.1 ∉ U → k p = 0) :
    (∫ b, legalInputBlockLaplace h k b ∂legalInputRootAverageLaw q L U α β) =
      ∫ p, legalMarkedRootedInputLaplace q L h k p
        ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
          (legalMarkedHaarRootLaw q L) := by
  let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) (L / 2)) :=
    isProbabilityMeasure_haarCubeRootLaw (Fin q) (by linarith)
  have hroot : legalMarkedHaarRootLaw q L = haarCubeRootLaw (Fin q) (L / 2) := by
    simp only [legalMarkedHaarRootLaw, haarCubeRootLaw, Fintype.card_fin,
      show 2 * (L / 2) = L by ring]
  rw [hroot, legalInputRootAverageLaw, integral_map
    (measurable_legalInputRootWindows q (Real.toNNReal L) hU).aemeasurable
    (measurable_legalInputBlockLaplace hh hk).aestronglyMeasurable]
  rw [← integral_prod_swap]
  apply integral_congr_ae
  exact .of_forall (fun p ↦ by
    change Real.exp (-(legalInputBlockTest h
      (legalInputRootWindowPrefix q (Real.toNNReal L) U (p.2, p.1.1)) +
      legalInputBlockTest k
        (legalInputRootWindowPrefix q (Real.toNNReal L) U (p.2, p.1.2)))) = _
    rw [legalInputBlockTest_rootWindow_sourceInput q hL U h hhzero,
      legalInputBlockTest_rootWindow_targetInput q hL U k hkzero]
    rfl)

/-- Full original empirical source and target inputs have the joint physical
Poisson Laplace functional along all real scales in the optimizer's own rooted
coordinates. -/
theorem tendsto_integral_legalMarkedRootedInputLaplace (q : ℕ)
    {S : ℝ} (hS : 0 ≤ S) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {h k : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) (hk : Measurable k)
    (hh0 : ∀ x, 0 ≤ h x) (hk0 : ∀ x, 0 ≤ k x)
    (hhzero : ∀ p, p.1 ∉ U → h p = 0) (hkzero : ∀ p, p.1 ∉ U → k p = 0) :
    Tendsto (fun L : ℝ ↦ ∫ p, legalMarkedRootedInputLaplace q L h k p
      ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
        (legalMarkedHaarRootLaw q L)) atTop
      (𝓝 (∫ b, legalInputBlockLaplace h k b ∂legalInputPoissonWindowLaw q U α β)) := by
  apply (tendsto_integral_legalInputRootAverageLaw_laplace q hS hU hsub hpos α β
    hh hk hh0 hk0).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact integral_legalInputRootAverageLaw_laplace_eq_input q hL hU α β hh hk hhzero hkzero

end OTSelector.Reconstruction
