import OTSelector.Probability.CavitySemidiscreteSpatialRooting
import OTSelector.Probability.CavitySemidiscreteRootedWitnessLimit

/-!
# Vanishing witnesses from actual rooted opposite-tilt plans

Original measurable allocation coefficients and target clouds produce the joint
rooted plan law. The actual phase bound, with its exact mass normalization, yields
vanishing expected rectangle witnesses for varying original environments and
sample sizes.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A B Ω : Type*} [Fintype ι]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Ω]

omit [Fintype ι] in
/-- The original random target cloud and allocation are translated by the same root. -/
theorem measurable_joint_cavitySpatialRootedPlan {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (a : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun v ↦ a v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) (N : ℝ) :
    Measurable (fun v : Ω × (ι → ℝ) ↦
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2) := by
  exact measurable_scaled_parameterizedSemidiscretePlan (V := Ω × (ι → ℝ)) μ
    (fun v ↦ a (v.1.1, v.2))
    (fun j ↦ (ha j).comp (measurable_fst.fst.prodMk measurable_snd))
    (fun v ↦ cavitySpatialTranslate v.1.2 v.2)
    (measurable_cavitySpatialTranslate.comp (measurable_fst.snd.prodMk measurable_snd))
    (fun v j ↦ cavitySpatialTranslate v.2 (Y v.1 j))
    (fun j ↦ measurable_cavitySpatialTranslate.comp
      (measurable_snd.prodMk ((hY j).comp measurable_fst)))
    (fun _ ↦ ENNReal.ofReal N) measurable_const

/-- Actual zero/positive/negative tilt optima force every fixed strict rectangle
witness to vanish in expectation. The source law, target sample size, probability
space and root domain may all vary with the sequence index. -/
theorem tendsto_actual_rooted_cycle_rectangle_expectation_zero
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (k : A → B → (ι → ℝ) → ℝ)
    (g a₀ aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (htzero : Tendsto t atTop (𝓝 0)) (G : ℝ)
    (hopt : ∀ n, ∀ᵐ ω ∂P n,
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (fun s ↦ a₀ n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + t n * g n (ω, s) j)
        (fun s ↦ aplus n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + (-t n) * g n (ω, s) j)
        (fun s ↦ aminus n (ω, s)) ∧
      (∀ j, Integrable (fun s ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (μ n)) ∧
      (∀ j, Integrable (fun s ↦ g n (ω, s) j) (μ n)) ∧
      (∀ᵐ s ∂μ n, ∀ j, |g n (ω, s) j| ≤ G))
    (A₀ A₁ : Set ((ι → ℝ) × A)) (B₀ B₁ : Set ((ι → ℝ) × B))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁)
    (hdisj : Disjoint A₀ A₁) (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ s ∈ A₀, ∀ s' ∈ A₁, ∀ y ∈ B₀, ∀ y' ∈ B₁,
      ε ≤ cavitySpatialDifferenceCost k s y + cavitySpatialDifferenceCost k s' y' -
        cavitySpatialDifferenceCost k s y' - cavitySpatialDifferenceCost k s' y)
    (D : ℕ → Set (ι → ℝ)) (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) :
    Tendsto (fun n ↦ ∫⁻ v : Ωn n × (ι → ℝ), min 1 (min
      (cavitySpatialRootedPlan (μ n)
        (fun s j ↦ (aplus n (v.1, s) j + aminus n (v.1, s) j) / 2)
        (Y n v.1) (N n) v.2 (A₀ ×ˢ B₀))
      (cavitySpatialRootedPlan (μ n)
        (fun s j ↦ (aplus n (v.1, s) j + aminus n (v.1, s) j) / 2)
        (Y n v.1) (N n) v.2 (A₁ ×ˢ B₁)))
      ∂(P n).prod (cavityRootMeasure volume (D n) (N n))) atTop (𝓝 0) := by
  let W (n : ℕ) (v : Ωn n × (ι → ℝ)) := min 1 (min
    (cavitySpatialRootedPlan (μ n)
      (fun s j ↦ (aplus n (v.1, s) j + aminus n (v.1, s) j) / 2)
      (Y n v.1) (N n) v.2 (A₀ ×ˢ B₀))
    (cavitySpatialRootedPlan (μ n)
      (fun s j ↦ (aplus n (v.1, s) j + aminus n (v.1, s) j) / 2)
      (Y n v.1) (N n) v.2 (A₁ ×ˢ B₁)))
  have hW (n : ℕ) : Measurable (W n) := by
    have hplan := measurable_joint_cavitySpatialRootedPlan (μ n)
      (fun v j ↦ (aplus n v j + aminus n v j) / 2)
      (fun j ↦ ((hplusm n j).add (hminusm n j)).div_const 2) (Y n) (hY n) (N n)
    exact measurable_const.min (((Measure.measurable_coe (hA₀.prod hB₀)).comp hplan).min
      ((Measure.measurable_coe (hA₁.prod hB₁)).comp hplan))
  have hroot (n : ℕ) : SFinite (cavityRootMeasure volume (D n) (N n)) := by
    unfold cavityRootMeasure
    infer_instance
  apply tendsto_lintegral_rooted_witness_zero_of_fiber_bound P
    (fun n ↦ cavityRootMeasure volume (D n) (N n)) W hW
    (ENNReal.ofReal ε) (ENNReal.ofReal G * ENNReal.ofReal K ^ Fintype.card ι)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by finiteness))
    (fun n ↦ ENNReal.ofReal (t n)) (by simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp htzero)
  intro n
  filter_upwards [hopt n] with ω ho
  have hb := lintegral_actual_rooted_cycle_rectangle_le (μ n) (p n ω) (Y n ω) k
    (fun s ↦ g n (ω, s)) (fun s ↦ a₀ n (ω, s))
    (fun s ↦ aplus n (ω, s)) (fun s ↦ aminus n (ω, s)) (t n) G (ht n)
    ho.1 ho.2.1 ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2.1 ho.2.2.2.2.2
    (fun j ↦ (hplusm n j).comp (measurable_const.prodMk measurable_id))
    (fun j ↦ (hminusm n j).comp (measurable_const.prodMk measurable_id))
    A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj K hK offset hbox ε hε.le hgap (D n) (N n) (hN n)
  change (∫⁻ z, ENNReal.ofReal ε * W n (ω, z)
    ∂cavityRootMeasure volume (D n) (N n)) ≤ _ at hb
  convert hb using 1
  rw [ENNReal.ofReal_mul (ht n)]
  ac_rfl

end OTSelector.Probability
