import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# MeasureTheory.NormalizedIntervalDensity

## Lemma skeleton

* **Conditions:** A jointly continuous scalar interval density (and continuous factors for the weighted readout), compact label core, and nonzero interval mass for normalization.

* **Objects:** The reference density, interval-integrated label mass, compact retention bounds and L1 continuity of normalized conditionals.

* **Proof detail:** Compose and multiply the continuous factors, integrate on the fixed compact interval, and bound the reference mass on a low-density subset by threshold times volume. Near a positive-mass label keep the denominator away from zero and apply dominated convergence to normalized densities.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/html/sec_diffunderint.html): Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters).
- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38): Section 1.6.2, Theorems 1.6.5–1.6.7 (Fatou, monotone convergence, dominated convergence), p. 30.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Generic analytic statements under the explicit scalar hypotheses; the module does not derive the physical chart Jacobian or equality of two separately supplied marginals.
-/

/-!
# Reference intensity of the finite upper-atlas labels

This file supplies the quantitative paper-fidelity content of the finite
upper-atlas reference intensity that complements the qualitative compact-core
skeleton of the atlas interiority file.

The actual finite upper-atlas labels carry, in the paper's order-two Whitney
coordinates, a common quotient measure `Lambda` with a Lebesgue density
`theta(z) = int_J g_A(r,z) dr = int_J g_B(r,z) dr`, where `g_A, g_B` are the
physical coordinate marginals of the two conditional populations. The file
proves, at the level of the actual characteristic-map readouts:

* the joint continuity of a Jacobian-weighted reference density
  `rho(Y) * omega(Y) * |Jac|` from the C^1 characteristic map, the continuous
  physical weight and the continuous Jacobian factor (the paper's
  `J_m = omega(Y) |det D Y|` structure);
* the continuity of `theta` from a genuine parametric interval integral
  (Mathlib `continuous_parametric_intervalIntegral_of_continuous'`);
* the quantitative removal bound `Lambda{theta < c} <= c * volume K` on a
  compact label core, and hence the paper's core-retention statement
  `Lambda((K cap {theta >= c})^c) <= epsilon + c * volume K` whenever the
  compact core loses at most `epsilon` of `Lambda`;
* the `L^1` (total-variation density) continuity of the normalized conditional
  laws `theta^{-1} g_A` on the positive set `{theta > 0}`.

The paper's total-variation statement follows from this `L^1` continuity through
the library identity `totalVariation_sub_eq_norm_L1_of_withDensity`.
-/
open Set MeasureTheory MeasureTheory.Measure Function Filter
open scoped ENNReal Topology Interval

noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι]

/-- **The paper's Jacobian-weighted reference density.** Given the actual C^1
characteristic-map readouts, a continuous physical weight `omega`, a continuous
population density `rho` and the continuous Jacobian factor supplied by the
certified compact core, the paper's density
`f_C(r,z) = rho_C(Y(r,z)) * (omega(Y(r,z)) * |Jac(r,z)|)` is jointly continuous.
This is the interface at which the compact-core C^1 data plugs in. -/
theorem continuous_uncurry_jacobianWeightedDensity
    {E : Type*} [TopologicalSpace E]
    {Y : ℝ → (ι → ℝ) → E} {ω ρ : E → ℝ} {Jac : ℝ → (ι → ℝ) → ℝ}
    (hY : Continuous (uncurry Y)) (hω : Continuous ω) (hρ : Continuous ρ)
    (hJac : Continuous (uncurry Jac)) :
    Continuous (uncurry fun r (z : ι → ℝ) => ρ (Y r z) * (ω (Y r z) * |Jac r z|)) := by
  have hY' : Continuous (fun p : ℝ × (ι → ℝ) => Y p.1 p.2) := hY
  have hJac' : Continuous (fun p : ℝ × (ι → ℝ) => Jac p.1 p.2) := hJac
  exact (hρ.comp hY').mul ((hω.comp hY').mul hJac'.abs)

/-- The physical readout of one population marginal. -/
def atlasReferenceDensityReadout (gA : ℝ → (ι → ℝ) → ℝ) : ℝ → (ι → ℝ) → ℝ := gA

/-- The common quotient density `theta(z) = int_J g_A(r,z) dr`. -/
def atlasTheta (gA : ℝ → (ι → ℝ) → ℝ) (a b : ℝ) : (ι → ℝ) → ℝ :=
  fun z => ∫ r in a..b, gA r z

/-- **Continuity of the common quotient density.** Joint continuity of the
physical readout gives a genuine parametric interval integral, hence `theta` is
continuous everywhere. -/
theorem continuous_atlasTheta {gA : ℝ → (ι → ℝ) → ℝ} {a b : ℝ}
    (hgA : Continuous (uncurry gA)) :
    Continuous (atlasTheta gA a b) := by
  have hswap : Continuous (uncurry fun z (r : ℝ) => gA r z) := by
    show Continuous (fun p : (ι → ℝ) × ℝ => gA p.2 p.1)
    exact hgA.comp continuous_swap
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hswap a b

/-- **Nonnegativity of the common quotient density.** -/
theorem atlasTheta_nonneg {gA : ℝ → (ι → ℝ) → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hgA_nonneg : ∀ r z, 0 ≤ gA r z) (z : ι → ℝ) :
    0 ≤ atlasTheta gA a b z := by
  rw [atlasTheta, intervalIntegral.integral_of_le hab]
  exact integral_nonneg_of_ae (ae_of_all _ fun r => hgA_nonneg r z)

/-- **Boundedness of the common quotient density on a compact label core.** -/
theorem atlasTheta_bound_on_compact {gA : ℝ → (ι → ℝ) → ℝ} {a b : ℝ}
    (hgA : Continuous (uncurry gA)) {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ z ∈ K, ‖atlasTheta gA a b z‖ ≤ C :=
  hK.exists_bound_of_continuousOn (continuous_atlasTheta hgA).continuousOn

/-- The reference measure with density `theta` against label volume. -/
def atlasReferenceMeasure (gA : ℝ → (ι → ℝ) → ℝ) (a b : ℝ) : Measure (ι → ℝ) :=
  volume.withDensity (fun z => ENNReal.ofReal (atlasTheta gA a b z))

/-- **Quantitative removal bound on a compact label core.** On a compact label
core `K`, deleting the set where the common quotient density is below `c`
costs at most `c` times the label volume of the core. This is the paper's
`{theta < c}` removal cost. -/
theorem atlasReferenceMeasure_removal_cost
    {gA : ℝ → (ι → ℝ) → ℝ} {a b : ℝ} (hgA : Continuous (uncurry gA))
    {K : Set (ι → ℝ)} (hK : IsCompact K) (hKvol : volume K ≠ ⊤)
    {c : ℝ} (hc : 0 < c) :
    atlasReferenceMeasure gA a b ({z | atlasTheta gA a b z < c} ∩ K) ≤
      ENNReal.ofReal (c * (volume K).toReal) := by
  have hθ : Continuous (atlasTheta gA a b) := continuous_atlasTheta hgA
  set A : Set (ι → ℝ) := {z | atlasTheta gA a b z < c} ∩ K with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_lt hθ.measurable measurable_const).inter hK.measurableSet
  rw [atlasReferenceMeasure, withDensity_apply _ hA]
  have hle : ∫⁻ z in A, ENNReal.ofReal (atlasTheta gA a b z) ∂volume ≤
      ∫⁻ z in A, ENNReal.ofReal c ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hA] with z hz
    exact ENNReal.ofReal_le_ofReal (le_of_lt hz.1)
  have hconst : ∫⁻ z in A, ENNReal.ofReal c ∂volume = ENNReal.ofReal c * volume A := by
    rw [lintegral_const, Measure.restrict_apply_univ]
  have hvolA : volume A ≤ volume K := measure_mono (inter_subset_right)
  calc ∫⁻ z in A, ENNReal.ofReal (atlasTheta gA a b z) ∂volume
      ≤ ENNReal.ofReal c * volume A := hle.trans hconst.le
    _ ≤ ENNReal.ofReal c * volume K := by gcongr
    _ = ENNReal.ofReal c * ENNReal.ofReal ((volume K).toReal) := by
        exact congrArg (fun t => ENNReal.ofReal c * t) (ENNReal.ofReal_toReal hKvol).symm
    _ = ENNReal.ofReal (c * (volume K).toReal) := (ENNReal.ofReal_mul hc.le).symm

/-- **The paper's quantitative core retention.** If a compact label core loses
at most `epsilon` of the reference measure, then the retained good set
`K cap {theta >= c}` loses at most `epsilon + c * volume K`. -/
theorem atlasReferenceMeasure_core_retention
    {gA : ℝ → (ι → ℝ) → ℝ} {a b : ℝ} (hgA : Continuous (uncurry gA))
    {K : Set (ι → ℝ)} (hK : IsCompact K) (hKvol : volume K ≠ ⊤)
    {ε c : ℝ} (hc : 0 < c)
    (hcore : atlasReferenceMeasure gA a b (Kᶜ) ≤ ENNReal.ofReal ε) :
    atlasReferenceMeasure gA a b ((K ∩ {z | c ≤ atlasTheta gA a b z})ᶜ) ≤
      ENNReal.ofReal ε + ENNReal.ofReal (c * (volume K).toReal) := by
  have hbad : (K ∩ {z | c ≤ atlasTheta gA a b z})ᶜ ⊆
      Kᶜ ∪ ({z | atlasTheta gA a b z < c} ∩ K) := by
    intro z hz
    simp only [mem_compl_iff, mem_inter_iff, mem_ofPred_eq] at hz ⊢
    by_cases hzK : z ∈ K
    · exact Or.inr ⟨not_le.mp fun h => hz ⟨hzK, h⟩, hzK⟩
    · exact Or.inl hzK
  calc atlasReferenceMeasure gA a b ((K ∩ {z | c ≤ atlasTheta gA a b z})ᶜ)
      ≤ atlasReferenceMeasure gA a b (Kᶜ ∪ ({z | atlasTheta gA a b z < c} ∩ K)) :=
        measure_mono hbad
    _ ≤ atlasReferenceMeasure gA a b (Kᶜ) +
          atlasReferenceMeasure gA a b ({z | atlasTheta gA a b z < c} ∩ K) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal (c * (volume K).toReal) :=
        add_le_add hcore
          (atlasReferenceMeasure_removal_cost hgA hK hKvol hc)

/-- **L^1 (total-variation density) continuity of the normalized conditional
density.** On the positive set of the common quotient density, at every label
with positive density, the normalized density `theta^{-1} g_A` is continuous in
the `L^1` distance over the compact time interval. The paper's total-variation
continuity of the conditional laws follows through the library identity
`totalVariation_sub_eq_norm_L1_of_withDensity`. -/
theorem atlasNormalizedDensity_l1_continuous
    {gA : ℝ → (ι → ℝ) → ℝ} {a b : ℝ} (hgA : Continuous (uncurry gA))
    (z₀ : ι → ℝ) (hz₀ : atlasTheta gA a b z₀ ≠ 0) :
    Tendsto (fun z => ∫ r in a..b,
        ‖gA r z / atlasTheta gA a b z - gA r z₀ / atlasTheta gA a b z₀‖)
      (𝓝[{z | atlasTheta gA a b z ≠ 0}] z₀) (𝓝 0) := by
  have hθ : Continuous (atlasTheta gA a b) := continuous_atlasTheta hgA
  set S : Set (ι → ℝ) := {z | atlasTheta gA a b z ≠ 0} with hS
  have hSopen : IsOpen S := isOpen_ne.preimage hθ
  have hnum : Continuous (fun p : S × ℝ => gA p.2 p.1.1) :=
    hgA.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  have hden : Continuous (fun p : S × ℝ => atlasTheta gA a b p.1.1) :=
    hθ.comp (continuous_subtype_val.comp continuous_fst)
  have hQ : Continuous (uncurry fun (z : S) (r : ℝ) =>
      gA r z.1 / atlasTheta gA a b z.1 - gA r z₀ / atlasTheta gA a b z₀) := by
    have h1 : Continuous (fun p : S × ℝ => gA p.2 p.1.1 / atlasTheta gA a b p.1.1) :=
      Continuous.div hnum hden (fun p => p.1.2)
    have h2 : Continuous (fun p : S × ℝ => gA p.2 z₀ / atlasTheta gA a b z₀) :=
      Continuous.div
        (hgA.comp (continuous_snd.prodMk
          (continuous_const : Continuous fun _ : S × ℝ => z₀)))
        (continuous_const : Continuous fun _ : S × ℝ => atlasTheta gA a b z₀)
        (fun _ => hz₀)
    exact h1.sub h2
  have hparam : Continuous (fun z : S => ∫ r in a..b,
      ‖gA r z.1 / atlasTheta gA a b z.1 - gA r z₀ / atlasTheta gA a b z₀‖) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (X := S) (f := fun (z : S) (r : ℝ) =>
        ‖gA r z.1 / atlasTheta gA a b z.1 - gA r z₀ / atlasTheta gA a b z₀‖)
      hQ.norm a b
  have hcontOn : ContinuousOn (fun z : ι → ℝ => ∫ r in a..b,
      ‖gA r z / atlasTheta gA a b z - gA r z₀ / atlasTheta gA a b z₀‖) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous (fun z : S => ∫ r in a..b,
      ‖gA r z.1 / atlasTheta gA a b z.1 - gA r z₀ / atlasTheta gA a b z₀‖)
    exact hparam
  have hzw : ContinuousWithinAt (fun z : ι → ℝ => ∫ r in a..b,
      ‖gA r z / atlasTheta gA a b z - gA r z₀ / atlasTheta gA a b z₀‖) S z₀ :=
    hcontOn.continuousWithinAt hz₀
  have hzero : (fun z : ι → ℝ => ∫ r in a..b,
      ‖gA r z / atlasTheta gA a b z - gA r z₀ / atlasTheta gA a b z₀‖) z₀ = 0 := by
    simp only [sub_self, norm_zero, intervalIntegral.integral_zero]
  have hzw' : Tendsto (fun z : ι → ℝ => ∫ r in a..b,
      ‖gA r z / atlasTheta gA a b z - gA r z₀ / atlasTheta gA a b z₀‖) (𝓝[S] z₀)
      (𝓝 ((fun z : ι → ℝ => ∫ r in a..b,
        ‖gA r z / atlasTheta gA a b z - gA r z₀ / atlasTheta gA a b z₀‖) z₀)) :=
    hzw
  simpa only [hzero] using hzw'

end OTSelector.Reconstruction
