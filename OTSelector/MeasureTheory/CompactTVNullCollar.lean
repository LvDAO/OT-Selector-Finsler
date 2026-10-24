import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Topology.UniformSpace.Dini

/-!
## Lemma skeleton

* **Conditions:** Finite scalar laws on a compact parameter set with continuous norm parameters controlling full signed total variation; finitely many threshold singletons are null.
* **Objects:** Event-mass continuity, uniform shrinking-collar nullity and common positive collar widths for one or two law families.
* **Proof detail:** Total variation bounds each event-mass difference. Continuity from above gives pointwise collar mass tending to zero; monotone continuous functions on the compact parameter set converge uniformly by Dini. Choose a common width, splitting epsilon for two colors.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
  https://measure.axler.net/MIRA.pdf#page=275
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).
  https://measure.axler.net/MIRA.pdf#page=59
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 2E, Exercise 7, p. 71 (Dini’s theorem).
  https://measure.axler.net/MIRA.pdf#page=86

**Relationship to the sources:** Derived compact-family collar theorem combining total variation and Dini. Finite law masses are not normalized; singleton-nullness is sufficient for its atomless-named wrapper.
-/

/-!
# Uniform null-level collars in a compact family of original clock laws

A norm-continuous parametrization controlling the actual total variation makes
every measurable event mass continuous. Dini's theorem then makes shrinking
collars of finitely many null clock levels uniformly small on a compact root
set. The clock laws retain their original mass and are never normalized.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The original event mass changes by at most the full signed variation. -/
theorem abs_measureReal_sub_le_totalVariation
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set X} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ := by
  have h := SignedMeasure.norm_le_totalVariation
    (μ.toSignedMeasure - ν.toSignedMeasure) A
  rw [Measure.toSignedMeasure_sub_apply hA, Real.norm_eq_abs] at h
  exact h.trans (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (subset_univ A)))

section Parametrized

variable {Z V : Type*} [TopologicalSpace Z] [NormedAddCommGroup V]
  {K : Set Z} (μ : Z → Measure ℝ) [∀ z, IsFiniteMeasure (μ z)]
  (L : Z → V)

omit [TopologicalSpace Z] in
/-- A genuine norm control of total variation controls every original event. -/
theorem abs_measureReal_sub_le_norm_of_totalVariation
    (htv : ∀ z ∈ K, ∀ w ∈ K,
      ((μ z).toSignedMeasure - (μ w).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal ‖L z - L w‖)
    {A : Set ℝ} (hA : MeasurableSet A)
    {z w : Z} (hz : z ∈ K) (hw : w ∈ K) :
    |(μ z).real A - (μ w).real A| ≤ ‖L z - L w‖ := by
  apply (abs_measureReal_sub_le_totalVariation (μ z) (μ w) hA).trans
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htv z hz w hw)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h

/-- The original mass of any fixed measurable clock set is root-continuous. -/
theorem continuousOn_measureReal_of_totalVariation
    (hL : ContinuousOn L K)
    (htv : ∀ z ∈ K, ∀ w ∈ K,
      ((μ z).toSignedMeasure - (μ w).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal ‖L z - L w‖)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ContinuousOn (fun z => (μ z).real A) K := by
  intro z hz
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  have he := (Metric.continuousWithinAt_iff'.mp (hL z hz)) ε hε
  filter_upwards [he, self_mem_nhdsWithin] with w hw hwK
  rw [Real.dist_eq]
  exact (abs_measureReal_sub_le_norm_of_totalVariation μ L htv hA hwK hz).trans_lt
    (by simpa only [dist_eq_norm] using hw)

/-- Uniform shrinking-collar convergence on one fixed compact root core.
Only the finitely many actual endpoint levels need be null at each root. -/
theorem tendstoUniformlyOn_measureReal_clock_collar
    (hK : IsCompact K) (hL : ContinuousOn L K)
    (htv : ∀ z ∈ K, ∀ w ∈ K,
      ((μ z).toSignedMeasure - (μ w).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal ‖L z - L w‖)
    (thresholds : Finset ℝ)
    (hnull : ∀ z ∈ K, ∀ t ∈ thresholds, μ z {t} = 0) :
    TendstoUniformlyOn
      (fun n : ℕ => fun z =>
        (μ z).real (Metric.cthickening (1 / ((n : ℝ) + 1)) (↑thresholds : Set ℝ)))
      (fun _ => 0) atTop K := by
  let A : ℕ → Set ℝ := fun n =>
    Metric.cthickening (1 / ((n : ℝ) + 1)) (↑thresholds : Set ℝ)
  have hA (n : ℕ) : MeasurableSet (A n) := Metric.isClosed_cthickening.measurableSet
  have hanti : Antitone A := by
    intro m n hmn
    apply Metric.cthickening_mono
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
    exact add_le_add (Nat.cast_le.mpr hmn) le_rfl
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun n => continuousOn_measureReal_of_totalVariation μ L hL htv (hA n))
    (fun z _ m n hmn => measureReal_mono (hanti hmn)) continuousOn_const
  intro z hz
  have hfinite : μ z (↑thresholds : Set ℝ) = 0 := by
    rw [show (↑thresholds : Set ℝ) = ⋃ t : thresholds, ({t.val} : Set ℝ) by
      ext x
      simp]
    exact measure_iUnion_null fun t => hnull z hz t.val t.property
  have hmeasure :=
    (tendsto_measure_cthickening_of_isCompact (μ := μ z)
      thresholds.finite_toSet.isCompact).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [hfinite] at hmeasure
  simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def, A] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hmeasure

/-- One strictly positive collar width works for all roots in the same
compact core; it is obtained from the actual pointwise null levels. -/
theorem exists_uniform_clock_collar_measure_lt
    (hK : IsCompact K) (hL : ContinuousOn L K)
    (htv : ∀ z ∈ K, ∀ w ∈ K,
      ((μ z).toSignedMeasure - (μ w).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal ‖L z - L w‖)
    (thresholds : Finset ℝ)
    (hnull : ∀ z ∈ K, ∀ t ∈ thresholds, μ z {t} = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∀ z ∈ K,
      μ z (Metric.cthickening h (↑thresholds : Set ℝ)) < ENNReal.ofReal ε := by
  have hunif := tendstoUniformlyOn_measureReal_clock_collar μ L hK hL htv thresholds hnull
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp hunif) ε hε).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  intro z hz
  have hreal := hn z hz
  simp only [Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg measureReal_nonneg] at hreal
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    (by simpa only [measureReal_def, ENNReal.toReal_ofReal hε.le] using hreal)

/-- Atomless clock laws give the uniform collar bound around any finite
family of endpoints without an assumed uniform collar estimate. -/
theorem exists_uniform_clock_collar_measure_lt_of_atomless
    (hK : IsCompact K) (hL : ContinuousOn L K)
    (htv : ∀ z ∈ K, ∀ w ∈ K,
      ((μ z).toSignedMeasure - (μ w).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal ‖L z - L w‖)
    (hnull : ∀ z ∈ K, NullSingletonClass (μ z))
    (thresholds : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∀ z ∈ K,
      μ z (Metric.cthickening h (↑thresholds : Set ℝ)) < ENNReal.ofReal ε := by
  apply exists_uniform_clock_collar_measure_lt μ L hK hL htv thresholds _ hε
  intro z hz t _
  let _ := hnull z hz
  exact measure_singleton t

end Parametrized

/-- A common positive width makes the total missed endpoint-collar mass of
both original colors uniformly small on the same fixed compact root core. -/
theorem exists_uniform_twoColor_clock_collar_measure_add_lt
    {Z V : Type*} [TopologicalSpace Z] [NormedAddCommGroup V]
    {K : Set Z} (μ : Fin 2 → Z → Measure ℝ)
    [∀ i z, IsFiniteMeasure (μ i z)] (L : Fin 2 → Z → V)
    (hK : IsCompact K) (hL : ∀ i, ContinuousOn (L i) K)
    (htv : ∀ i, ∀ z ∈ K, ∀ w ∈ K,
      ((μ i z).toSignedMeasure - (μ i w).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal ‖L i z - L i w‖)
    (thresholds : Finset ℝ)
    (hnull : ∀ i, ∀ z ∈ K, ∀ t ∈ thresholds, μ i z {t} = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∀ z ∈ K,
      μ 0 z (Metric.cthickening h (↑thresholds : Set ℝ)) +
        μ 1 z (Metric.cthickening h (↑thresholds : Set ℝ)) < ENNReal.ofReal ε := by
  obtain ⟨h₀, hh₀, hmass₀⟩ := exists_uniform_clock_collar_measure_lt
    (μ 0) (L 0) hK (hL 0) (htv 0) thresholds (hnull 0) (half_pos hε)
  obtain ⟨h₁, hh₁, hmass₁⟩ := exists_uniform_clock_collar_measure_lt
    (μ 1) (L 1) hK (hL 1) (htv 1) thresholds (hnull 1) (half_pos hε)
  refine ⟨min h₀ h₁, lt_min hh₀ hh₁, ?_⟩
  intro z hz
  have h₀bound := (measure_mono
    (Metric.cthickening_mono (min_le_left h₀ h₁) (↑thresholds : Set ℝ))).trans_lt
      (hmass₀ z hz)
  have h₁bound := (measure_mono
    (Metric.cthickening_mono (min_le_right h₀ h₁) (↑thresholds : Set ℝ))).trans_lt
      (hmass₁ z hz)
  apply (ENNReal.add_lt_add h₀bound h₁bound).trans_eq
  rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

end OTSelector.Reconstruction
