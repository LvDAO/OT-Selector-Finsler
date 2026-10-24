import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteRootedWitness
import OTSelector.Probability.CavitySemidiscretePlanMeasurable

/-!
# Actual translated plan witnesses in a homogeneous local model

A spatial root translates both physical endpoints and leaves their marks fixed.
For a cost depending on the spatial difference and the two marks, the actual
cycle gap is translation invariant. All moving source and target blocks in the
grid estimate are therefore produced from fixed measurable rectangles.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

/-- Translate a spatially marked endpoint by minus the chosen root. -/
def cavitySpatialTranslate (z : ι → ℝ) (x : (ι → ℝ) × A) : (ι → ℝ) × A :=
  (x.1 - z, x.2)

/-- The actual homogeneous local cost reads the two marks and spatial difference. -/
def cavitySpatialDifferenceCost (k : A → B → (ι → ℝ) → ℝ)
    (x : (ι → ℝ) × A) (y : (ι → ℝ) × B) : ℝ :=
  k x.2 y.2 (y.1 - x.1)

omit [Fintype ι] in
theorem measurable_cavitySpatialTranslate :
    Measurable (fun z : (ι → ℝ) × ((ι → ℝ) × A) ↦ cavitySpatialTranslate z.1 z.2) :=
  (measurable_snd.fst.sub measurable_fst).prodMk measurable_snd.snd

omit [Fintype ι] [MeasurableSpace A] [MeasurableSpace B] in
theorem cavitySpatialDifferenceCost_translate (k : A → B → (ι → ℝ) → ℝ)
    (z : ι → ℝ) (x : (ι → ℝ) × A) (y : (ι → ℝ) × B) :
    cavitySpatialDifferenceCost k (cavitySpatialTranslate z x) (cavitySpatialTranslate z y) =
      cavitySpatialDifferenceCost k x y := by
  simp only [cavitySpatialDifferenceCost, cavitySpatialTranslate, sub_sub_sub_cancel_right]

/-- The original allocation coupling after mass scaling and translation of both endpoints. -/
def cavitySpatialRootedPlan {m : ℕ} (μ : Measure ((ι → ℝ) × A))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ) :
    Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)) :=
  ENNReal.ofReal N • (semidiscreteAllocationMeasure μ a).map
    (Prod.map (cavitySpatialTranslate z) (fun j ↦ cavitySpatialTranslate z (Y j)))

omit [Fintype ι] in
/-- Joint rooting is a measurable map into actual source-target plan measures. -/
theorem measurable_cavitySpatialRootedPlan {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun s ↦ a s j))
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) :
    Measurable (cavitySpatialRootedPlan μ a Y N) := by
  exact measurable_scaled_parameterizedSemidiscretePlan μ
    (fun v ↦ a v.2) (fun j ↦ (ha j).comp measurable_snd)
    (fun v ↦ cavitySpatialTranslate v.1 v.2) measurable_cavitySpatialTranslate
    (fun z j ↦ cavitySpatialTranslate z (Y j))
    (fun _ ↦ measurable_cavitySpatialTranslate.comp (measurable_id.prodMk measurable_const))
    (fun _ ↦ ENNReal.ofReal N) measurable_const

/-- The exact spatially rooted rectangle witness of opposite-tilt optimizers obeys the
phase-averaged estimate. Moving blocks, target-label screens, and cube disjointness
are all produced from the original fixed rectangles. -/
theorem lintegral_actual_rooted_cycle_rectangle_le {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Fin (m + 1) → ℝ) (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (k : A → B → (ι → ℝ) → ℝ)
    (g a₀ aplus aminus : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (t G : ℝ) (ht : 0 ≤ t)
    (h₀ : IsOptimalSemidiscreteAllocation μ p
      (fun s j ↦ cavitySpatialDifferenceCost k s (Y j)) a₀)
    (hplus : IsOptimalSemidiscreteAllocation μ p
      (fun s j ↦ cavitySpatialDifferenceCost k s (Y j) + t * g s j) aplus)
    (hminus : IsOptimalSemidiscreteAllocation μ p
      (fun s j ↦ cavitySpatialDifferenceCost k s (Y j) + (-t) * g s j) aminus)
    (hc : ∀ j, Integrable (fun s ↦ cavitySpatialDifferenceCost k s (Y j)) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (hbound : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G)
    (hplusm : ∀ j, Measurable (fun s ↦ aplus s j))
    (hminusm : ∀ j, Measurable (fun s ↦ aminus s j))
    (A₀ A₁ : Set ((ι → ℝ) × A)) (B₀ B₁ : Set ((ι → ℝ) × B))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁)
    (hdisj : Disjoint A₀ A₁) (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ s ∈ A₀, ∀ s' ∈ A₁, ∀ y ∈ B₀, ∀ y' ∈ B₁,
      ε ≤ cavitySpatialDifferenceCost k s y + cavitySpatialDifferenceCost k s' y' -
        cavitySpatialDifferenceCost k s y' - cavitySpatialDifferenceCost k s' y)
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    (∫⁻ z, ENNReal.ofReal ε * min 1 (min
      (cavitySpatialRootedPlan μ (fun s j ↦ (aplus s j + aminus s j) / 2) Y N z (A₀ ×ˢ B₀))
      (cavitySpatialRootedPlan μ (fun s j ↦ (aplus s j + aminus s j) / 2) Y N z (A₁ ×ˢ B₁)))
      ∂cavityRootMeasure volume D N) ≤
      ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  let AA (z : ι → ℝ) := cavitySpatialTranslate z ⁻¹' A₀
  let AB (z : ι → ℝ) := cavitySpatialTranslate z ⁻¹' A₁
  let J (z : ι → ℝ) := Finset.univ.filter (fun j ↦ cavitySpatialTranslate z (Y j) ∈ B₀)
  let L (z : ι → ℝ) := Finset.univ.filter (fun j ↦ cavitySpatialTranslate z (Y j) ∈ B₁)
  have hJA : MeasurableSet {x : (ι → ℝ) × ((ι → ℝ) × A) | x.2 ∈ AA x.1} :=
    hA₀.preimage measurable_cavitySpatialTranslate
  have hJB : MeasurableSet {x : (ι → ℝ) × ((ι → ℝ) × A) | x.2 ∈ AB x.1} :=
    hA₁.preimage measurable_cavitySpatialTranslate
  have hJ (j : Fin (m + 1)) : MeasurableSet {z | j ∈ J z} := by
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hB₀.preimage (show Measurable (fun z : ι → ℝ ↦ cavitySpatialTranslate z (Y j)) from
        measurable_cavitySpatialTranslate.comp (measurable_id.prodMk measurable_const))
  have hL (j : Fin (m + 1)) : MeasurableSet {z | j ∈ L z} := by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hB₁.preimage (show Measurable (fun z : ι → ℝ ↦ cavitySpatialTranslate z (Y j)) from
        measurable_cavitySpatialTranslate.comp (measurable_id.prodMk measurable_const))
  have hcell (z : ι → ℝ) : AA z ∪ AB z ⊆
      (fun s ↦ s.1 - offset) ⁻¹' cavityGridCube ι K z := by
    intro s hs
    have hb := hbox (cavitySpatialTranslate z s) hs
    change (s.1 - offset) - z ∈ cavityGridPhaseCell ι K
    change (s.1 - z) - offset ∈ cavityGridPhaseCell ι K at hb
    simpa only [sub_right_comm] using hb
  have hgap' : ∀ z, ∀ s ∈ AA z, ∀ s' ∈ AB z, ∀ j ∈ J z, ∀ l ∈ L z,
      ε ≤ cavitySpatialDifferenceCost k s (Y j) + cavitySpatialDifferenceCost k s' (Y l) -
        cavitySpatialDifferenceCost k s (Y l) - cavitySpatialDifferenceCost k s' (Y j) := by
    intro z s hs s' hs' j hj l hl
    have h := hgap _ hs _ hs' _ (Finset.mem_filter.mp hj).2 _ (Finset.mem_filter.mp hl).2
    simpa only [cavitySpatialDifferenceCost_translate] using h
  have hb := lintegral_cavityRoot_opposite_tilt_cycle_witness_le μ p
    (fun s j ↦ cavitySpatialDifferenceCost k s (Y j)) g a₀ aplus aminus
    t G ht h₀ hplus hminus hc hg hbound hplusm hminusm
    (fun s ↦ s.1 - offset) K hK AA AB hJA hJB
    (fun z ↦ hdisj.preimage (cavitySpatialTranslate z)) hcell J L hJ hL ε hε hgap' D N hN
  convert hb using 1
  apply lintegral_congr
  intro z
  simp only [cavitySpatialRootedPlan]
  rw [(hplus.1.average hminus.1).scaled_map_cycle_witness
    (cavitySpatialTranslate z)
    (measurable_cavitySpatialTranslate.comp (measurable_const.prodMk measurable_id))
    (fun j ↦ cavitySpatialTranslate z (Y j)) A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ N hN.le, ← ENNReal.ofReal_mul hε]

end OTSelector.Probability
