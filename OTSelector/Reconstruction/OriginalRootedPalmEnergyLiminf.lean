import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedEnergy
import Mathlib.Order.Filter.AtTopBot.Basic
import OTSelector.MeasureTheory.Integral.CountableFatouBudget

/-! The true original Palm energy is bounded by the liminf of the actual
physical energies, without replacing them by a common per-seed constant. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local instance originalRootedPalmEnergyLiminfPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- The actual limiting Palm retains the local liminf energy, rather than an
independent uniform bound for each seed. This follows along a subsequence
selected from the original energy sequence and the same prescribed weak limit. -/
theorem lintegral_cubePalm_le_liminf_sourceWindow_energy
    (P : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hweak : Tendsto P atTop (𝓝 Q))
    (f : PhysicalPairPalmMark ι → ℝ) (hf : Continuous f) (hf0 : ∀ m, 0 ≤ f m)
    (energy : ℕ → ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, ∀ (U : Set (ι → ℝ)), IsOpen U →
      (∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
        ENNReal.ofReal (f (physicalPairAnchor e).2)
        ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        ∂(P n : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤
        volume U * energy n) :
    (∫⁻ m, ENNReal.ofReal (f m) ∂cubePalm ι (physicalScenePairCampbell
      (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ) ≤
        liminf energy atTop := by
  by_contra hnot
  obtain ⟨B, hB, hbelow⟩ := exists_between (lt_of_not_ge hnot)
  have hfreq : ∃ᶠ n in atTop, energy n < B := frequently_lt_of_liminf_lt (h := hB)
  obtain ⟨φ, hφ, hφB⟩ := extraction_of_frequently_atTop (hfreq.and_eventually hbound)
  have hupper := lintegral_cubePalm_le_of_weak_energy_density_bound
    (fun n ↦ P (φ n)) (hweak.comp hφ.tendsto_atTop) f hf hf0 B (by
      intro U hU n
      exact ((hφB n).2 U hU).trans
        (mul_le_mul_of_nonneg_left (hφB n).1.le bot_le))
  exact hbelow.not_ge hupper

/-- The exact original environment, finite physical plans, coordinates and
Haar roots give a true Palm lower bound by their own original mean energies.
No uniform-integrability or energy-measure absolute-continuity input is used. -/
theorem lintegral_cubePalm_le_liminf_original_physical_energy
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Γ : ∀ n, Ω n → Measure (M × M)) [∀ n w, IsFiniteMeasure (Γ n w)]
    (hΓ : ∀ n, Measurable (Γ n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    {Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hweak : Tendsto (fun n ↦ physicalSceneRootedLocalSceneLaw
      (P n) (Γ n) (Γ n) (hΓ n) (hΓ n) (coord n) (hcoord n) u hu
      (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q))
    (f : PhysicalPairPalmMark ι → ℝ) (hf : Continuous f) (hf0 : ∀ m, 0 ≤ f m) :
    (∫⁻ m, ENNReal.ofReal (f m) ∂cubePalm ι (physicalScenePairCampbell
      (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ) ≤
        liminf (fun n ↦ ∫⁻ w, ∫⁻ p,
          ENNReal.ofReal (f ((u p.1, u p.2), coord n p.2 - coord n p.1))
          ∂Γ n w ∂P n) atTop := by
  apply lintegral_cubePalm_le_liminf_sourceWindow_energy _ hweak f hf hf0
  filter_upwards [] with n
  intro U hU
  exact lintegral_physicalSceneRootedLocalSceneLaw_sourceEnergy_le
    (P n) (Γ n) (Γ n) (hΓ n) (hΓ n) (coord n) (hcoord n) u hu
    (N n) (hN n) (D n) (hD n) (ENNReal.measurable_ofReal.comp hf.measurable)
    U hU.measurableSet

/-- Actual countably many prescribed Palm limits share one global original
energy budget. Each source-window comparison may begin at its own deterministic
sample threshold; no common majorant over seeds is introduced. -/
theorem tsum_cubePalm_energy_le_of_original_global_budget
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)]
    (P : ∀ j, ℕ → ProbabilityMeasure
      (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ)))
    (Q : ∀ j, ProbabilityMeasure
      (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ)))
    (hweak : ∀ j, Tendsto (P j) atTop (𝓝 (Q j)))
    (f : ∀ j, PhysicalPairPalmMark (axes j) → ℝ)
    (hf : ∀ j, Continuous (f j)) (hf0 : ∀ j m, 0 ≤ f j m)
    (energy : ℕ → ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hbudget : ∀ n, ∑' j, energy n j ≤ C)
    (hbound : ∀ j, ∀ᶠ n in atTop, ∀ (U : Set ((axes j) → ℝ)), IsOpen U →
      (∫⁻ scene, ∫⁻ e in
        {e : ((((axes j) → ℝ) × ℝ) × (((axes j) → ℝ) × ℝ)) | e.1.1 ∈ U},
        ENNReal.ofReal (f j (physicalPairAnchor e).2)
        ∂(scene.1 : Measure ((((axes j) → ℝ) × ℝ) × (((axes j) → ℝ) × ℝ)))
        ∂(P j n : Measure
          (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ)))) ≤
        volume U * energy n j) :
    (∑' j, ∫⁻ m, ENNReal.ofReal (f j m) ∂cubePalm (axes j) (physicalScenePairCampbell
      (Q j : Measure
        (CavityLocalScene (((axes j) → ℝ) × ℝ) (((axes j) → ℝ) × ℝ))))) ≤ C := by
  apply tsum_le_of_local_liminf_and_global_energy_budget energy _ C hbudget
  intro j
  exact lintegral_cubePalm_le_liminf_sourceWindow_energy (P j) (hweak j)
    (f j) (hf j) (hf0 j) (fun n ↦ energy n j) (hbound j)

end OTSelector.Reconstruction
