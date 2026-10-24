import OTSelector.Reconstruction.MarkedStationaryValueLegalInputRootWindow
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowBoundary

/-!
# Actual Haar-rooted local input laws

Bounded tests of the same original two-color prefixes have their exact physical
Poisson window expectation at every interior original Haar root. Averaging over
that same root charges only its actual vanishing boundary probability.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A measurable mixture whose original conditional laws agree on a root set
has a bounded-observable error paid only by its complement. -/
theorem abs_integral_prod_sub_le_of_map_eq_on
    {X Ω Y : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Ω) (κ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {f : X × Ω → Y} (hf : Measurable f)
    {A : Set X} (hA : MeasurableSet A)
    (hmap : ∀ x ∈ A, ν.map (fun ω ↦ f (x, ω)) = κ)
    {F : Y → ℝ} (hF : Measurable F) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ y, |F y| ≤ B) :
    |(∫ p, F (f p) ∂μ.prod ν) - ∫ y, F y ∂κ| ≤
      2 * B * (μ Aᶜ).toReal := by
  have hi : Integrable (fun p ↦ F (f p)) (μ.prod ν) :=
    ⟨(hF.comp hf).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (.of_forall (fun p ↦ hbound (f p)))⟩
  have hFi : Integrable F κ :=
    ⟨hF.aestronglyMeasurable, HasFiniteIntegral.of_bounded (.of_forall hbound)⟩
  have hFb : |∫ y, F y ∂κ| ≤ B := by
    simpa using norm_integral_le_of_norm_le_const (μ := κ) (f := F) (C := B)
      (.of_forall (fun y ↦ by simpa only [Real.norm_eq_abs] using hbound y))
  have hinner : ∀ x, |∫ ω, F (f (x, ω)) ∂ν| ≤ B := by
    intro x
    simpa using norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun ω ↦ F (f (x, ω))) (C := B) (.of_forall (fun ω ↦ by
        simpa only [Real.norm_eq_abs] using hbound (f (x, ω))))
  have hzero : ∀ x ∈ A, (∫ ω, F (f (x, ω)) ∂ν) - ∫ y, F y ∂κ = 0 := by
    intro x hx
    have hfx : Measurable (fun ω ↦ f (x, ω)) := hf.comp measurable_prodMk_left
    rw [← hmap x hx, integral_map hfx.aemeasurable hF.aestronglyMeasurable, sub_self]
  rw [integral_prod _ hi]
  have hsub : (∫ x, ∫ ω, F (f (x, ω)) ∂ν ∂μ) - (∫ y, F y ∂κ) =
      ∫ x, (∫ ω, F (f (x, ω)) ∂ν) - ∫ y, F y ∂κ ∂μ := by
    rw [integral_sub hi.integral_prod_left (integrable_const _)]
    simp
  rw [hsub]
  have heq : (∫ x, (∫ ω, F (f (x, ω)) ∂ν) - ∫ y, F y ∂κ ∂μ) =
      ∫ x in Aᶜ, (∫ ω, F (f (x, ω)) ∂ν) - ∫ y, F y ∂κ ∂μ := by
    rw [← integral_indicator hA.compl]
    apply integral_congr_ae
    exact .of_forall (fun x ↦ by
      by_cases hx : x ∈ A
      · rw [indicator_of_notMem (show x ∉ Aᶜ from not_not_intro hx)]
        exact hzero x hx
      · rw [indicator_of_mem (show x ∈ Aᶜ from hx)])
  rw [heq]
  have hdiff : ∀ x, |(∫ ω, F (f (x, ω)) ∂ν) - ∫ y, F y ∂κ| ≤ 2 * B := by
    intro x
    calc
      _ ≤ |∫ ω, F (f (x, ω)) ∂ν| + |∫ y, F y ∂κ| := abs_sub _ _
      _ ≤ B + B := add_le_add (hinner x) hFb
      _ = 2 * B := by ring
  simpa only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] using
    norm_integral_le_of_norm_le_const (μ := μ.restrict Aᶜ)
      (f := fun x ↦ (∫ ω, F (f (x, ω)) ∂ν) - ∫ y, F y ∂κ) (C := 2 * B)
      (.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using hdiff x))

/-- Two independent original clock populations on one actual physical Poisson
window. The finite arrays enumerate exactly the retained original prefixes. -/
def legalInputPoissonWindowLaw (q : ℕ) (U : Set (Fin q → ℝ))
    (α β : Measure ℝ) :
    Measure (BlockData ((Fin q → ℝ) × ℝ) × BlockData ((Fin q → ℝ) × ℝ)) :=
  let pointLaw := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  let oneColor := fun γ : Measure ℝ ↦ Measure.sum (fun n : ℕ ↦
    (poissonMeasure (volume U).toNNReal {n}) •
      (Measure.pi (fun _ : Fin n ↦ pointLaw.prod γ)).map
        (fun y ↦ (⟨n, y⟩ : BlockData ((Fin q → ℝ) × ℝ))))
  (oneColor α).prod (oneColor β)

/-- The same original two-color environment and its actual independent Haar
root, restricted to the root's physical window. -/
def legalInputRootAverageLaw (q : ℕ) (L : ℝ) (U : Set (Fin q → ℝ))
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :=
  ((haarCubeRootLaw (Fin q) (L / 2)).prod
    (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)))).map
      (legalInputRootWindows q (Real.toNNReal L) U)

/-- At every root with the actual fixed observation window inside the box,
the original input restriction has exactly the physical Poisson window law. -/
theorem map_legalInputRootWindows_eq_of_inner_root (q : ℕ)
    {L S : ℝ} (hS : 0 ≤ S) (hmargin : S + 1 < L / 2)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {z : Fin q → ℝ} (hz : z ∈ haarRootCube (Fin q) (L / 2 - S - 1)) :
    (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).map
      (fun ω ↦ legalInputRootWindows q (Real.toNNReal L) U (z, ω)) =
      legalInputPoissonWindowLaw q U α β := by
  have hL : 0 < L := by linarith
  have hr : Real.toNNReal (L ^ q) = (Real.toNNReal L) ^ q := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_pow, Real.coe_toNNReal _ hL.le,
      Real.coe_toNNReal _ (pow_nonneg hL.le q)]
  rw [hr]
  have hinside := hsub.trans
    (haarRootCube_subset_legalInputPhysicalBox_of_inner_root q hS hmargin hz)
  simpa only [legalInputPoissonWindowLaw, blockDataLaw, Real.coe_toNNReal _ hL.le] using
    map_legalInputRootWindows_twoMarkedCloudLaw q (Real.toNNReal_pos.mpr hL)
      z hU (by simpa only [Real.coe_toNNReal _ hL.le] using hinside) hpos α β

/-- The original physical Poisson window law is a probability law, produced
from restriction of an original finite cloud at an actual interior Haar root. -/
theorem isProbabilityMeasure_legalInputPoissonWindowLaw (q : ℕ)
    {S : ℝ} (hS : 0 ≤ S) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    IsProbabilityMeasure (legalInputPoissonWindowLaw q U α β) := by
  let L := 4 * (S + 1)
  have hmargin : S + 1 < L / 2 := by dsimp [L]; linarith
  have hz : (0 : Fin q → ℝ) ∈ haarRootCube (Fin q) (L / 2 - S - 1) := by
    constructor <;> intro i <;> dsimp <;> linarith
  rw [← map_legalInputRootWindows_eq_of_inner_root q hS hmargin hU hsub hpos α β hz]
  exact Measure.isProbabilityMeasure_map
    ((measurable_legalInputRootWindows q (Real.toNNReal L) hU).comp
      measurable_prodMk_left).aemeasurable

/-- A bounded observable of the literal original rooted window differs from
its physical Poisson expectation only through the actual boundary root event. -/
theorem abs_integral_legalInputRootAverageLaw_sub_le (q : ℕ)
    {L S : ℝ} (hS : 0 ≤ S) (hmargin : S + 1 < L / 2)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {F : BlockData ((Fin q → ℝ) × ℝ) × BlockData ((Fin q → ℝ) × ℝ) → ℝ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ y, |F y| ≤ B) :
    |(∫ y, F y ∂legalInputRootAverageLaw q L U α β) -
      ∫ y, F y ∂legalInputPoissonWindowLaw q U α β| ≤
      2 * B * ((haarCubeRootLaw (Fin q) (L / 2))
        (haarRootCube (Fin q) (L / 2 - S - 1))ᶜ).toReal := by
  have hL : 0 < L := by linarith
  let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) (L / 2)) :=
    isProbabilityMeasure_haarCubeRootLaw (Fin q) (by linarith)
  let : IsProbabilityMeasure (legalInputPoissonWindowLaw q U α β) :=
    isProbabilityMeasure_legalInputPoissonWindowLaw q hS hU hsub hpos α β
  have hw := measurable_legalInputRootWindows q (Real.toNNReal L) hU
  rw [legalInputRootAverageLaw, integral_map hw.aemeasurable hF.aestronglyMeasurable]
  exact abs_integral_prod_sub_le_of_map_eq_on _ _ _ hw measurableSet_Icc
    (fun z hz ↦ map_legalInputRootWindows_eq_of_inner_root q hS hmargin hU hsub hpos α β hz)
    hF hB hbound

/-- Along all real physical box scales, every bounded measurable test of the
same original rooted finite input windows converges to its true Poisson-window
expectation, with both original colors independent and their marks unchanged. -/
theorem tendsto_integral_legalInputRootAverageLaw (q : ℕ)
    {S : ℝ} (hS : 0 ≤ S) {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {F : BlockData ((Fin q → ℝ) × ℝ) × BlockData ((Fin q → ℝ) × ℝ) → ℝ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ y, |F y| ≤ B) :
    Tendsto (fun L : ℝ ↦ ∫ y, F y ∂legalInputRootAverageLaw q L U α β)
      atTop (𝓝 (∫ y, F y ∂legalInputPoissonWindowLaw q U α β)) := by
  have hsmall : Tendsto (fun L : ℝ ↦
      (haarCubeRootLaw (Fin q) (L / 2)
        (haarRootCube (Fin q) (L / 2 - S - 1))ᶜ).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
      (tendsto_legalInput_inner_root_compl q hS)
    simpa only [Function.comp_def, ENNReal.toReal_zero, haarCubeRootLaw,
      Fintype.card_fin, show ∀ L : ℝ, 2 * (L / 2) = L from fun L ↦ by ring] using h
  have hlim : Tendsto (fun L : ℝ ↦ 2 * B *
      (haarCubeRootLaw (Fin q) (L / 2)
        (haarRootCube (Fin q) (L / 2 - S - 1))ᶜ).toReal) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hsmall
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall (fun L ↦ norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_gt_atTop (2 * (S + 1))] with L hL
  simpa only [Real.norm_eq_abs] using abs_integral_legalInputRootAverageLaw_sub_le q
    hS (show S + 1 < L / 2 by linarith) hU hsub hpos α β hF hB hbound

end OTSelector.Reconstruction
