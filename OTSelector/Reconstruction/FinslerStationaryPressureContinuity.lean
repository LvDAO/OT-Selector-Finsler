import OTSelector.Reconstruction.FinslerStationaryPressureValue
import OTSelector.Reconstruction.FinslerPopulationAtlasPressure
import OTSelector.Reconstruction.FinslerPopulationPressureCore

/-!
# Continuity, core intensity bounds and complement bookkeeping for the atlas

This module closes three concrete gaps left by
`FinslerStationaryPressureValue` and `FinslerPopulationAtlasPressure`.

## Root continuity of the stationary value

For a common admissible class `C`, if the kinetic/probe data converge uniformly
on `C` to their values at `z₀`, then the stationary values converge.  The proof
compares the two infima directly: uniform closeness of the candidates transfers
to the value sets, and `le_csInf`/`csInf_le` give the two-sided inequality
`|I z v - I z₀ v| ≤ (1 + |v|) ε`.  This is then combined with the Lipschitz
continuity in the tilt to obtain joint continuity of
`(z, v) ↦ stationaryValue (K z) (P z) (Cw z) v`, under eventual local constancy
of the classes (equivalently, the two eventual inclusions) and uniform
convergence on each class.  The final corollary discharges the explicit
continuity hypothesis `hcont` of
`PopulationSeedIntensityCore.exists_weighted_sum_approximation_stationary`.

## Uniform theta bound on an intensity core

`PopulationSeedIntensityCore.bounds` is stated on the actual label image; reading
it at the inverse label of a retained root gives
`populationAtlasTheta ... j z ≤ D.upper` for every `z ∈ D.roots`.  This yields a
core-local population integrand bound using `D.lower^(-2/q)`. The lower
constant is produced by compact-core restriction. Global summability uses actual
Haar L1 majorants, with no global lower density restriction.

## Core-complement bookkeeping

A finite weighted-sum approximation on a measurable core `K` and the uniform
complement estimate combine to a full-atlas approximation with error
`η * λ(K) + B * λ(Kᶜ)`, and `λ(Kᶜ) ≤ ε` gives the stated `η * mass + B * ε`
form.  `PopulationPressureCore.complement_small` supplies the small complement
`λ rootsᶜ < ε`, and `PopulationPressureCore.remainder_mass` identifies it with
the two physical label-complement masses.

The concrete construction of the matching classes and the Campbell finite
domination remain out of scope as before.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Filter
open scoped Topology ContDiff ENNReal

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace OTSelector.Reconstruction

/-! ## Infimum comparison under uniform closeness -/

/-- A value set is bounded below when the kinetic energy is bounded below by
`-c` and the probe is bounded by `G`. -/
theorem bddBelow_stationaryValue_of_lower_bound {X : Type*} {K P : X → ℝ}
    {admissible : Set X} {v G c : ℝ}
    (hK : ∀ w ∈ admissible, -c ≤ K w)
    (hP : ∀ w ∈ admissible, |P w| ≤ G) :
    BddBelow ((fun w ↦ K w + v * P w) '' admissible) := by
  refine ⟨-c - |v| * G, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  have hPw := abs_le.mp (hP w hw)
  have h2 : -(|v| * G) ≤ v * P w := by
    rcases le_total 0 v with hv | hv
    · have hvabs : |v| = v := abs_of_nonneg hv
      rw [hvabs]
      nlinarith [hPw.1]
    · have hvabs : |v| = -v := abs_of_nonpos hv
      rw [hvabs]
      nlinarith [hPw.2]
  linarith [hK w hw]

/-- One-sided transfer of uniform closeness to the stationary infimum:
`sInf S ≤ sInf S' + (1 + |v|) ε` when the data are `ε`-close on the class. -/
theorem stationaryValue_le_add_of_uniform_close {X : Type*} {C : Set X}
    {K K' P P' : X → ℝ} {v ε : ℝ}
    (hne : C.Nonempty)
    (hbdd : BddBelow ((fun w ↦ K w + v * P w) '' C))
    (hclose : ∀ w ∈ C, |K w - K' w| ≤ ε ∧ |P w - P' w| ≤ ε) :
    stationaryValue K P C v ≤ stationaryValue K' P' C v + (1 + |v|) * ε := by
  have hlow : stationaryValue K P C v - (1 + |v|) * ε ≤
      stationaryValue K' P' C v := by
    apply le_csInf (hne.image _)
    rintro y ⟨w, hw, rfl⟩
    have hle := stationaryValue_le (K := K) (P := P) (admissible := C) (v := v) hbdd hw
    have hclosew := hclose w hw
    have hKle : K w ≤ K' w + ε := by
      have := abs_le.mp hclosew.1
      linarith
    have hPle : v * P w ≤ v * P' w + |v| * ε := by
      have hdiff : v * (P w - P' w) ≤ |v| * |P w - P' w| := by
        calc v * (P w - P' w) ≤ |v * (P w - P' w)| := le_abs_self _
          _ = |v| * |P w - P' w| := abs_mul v _
      have hdiff' : v * (P w - P' w) ≤ |v| * ε :=
        hdiff.trans (mul_le_mul_of_nonneg_left hclosew.2 (abs_nonneg v))
      nlinarith
    linarith
  linarith

/-- Uniform closeness on a common class gives closeness of the stationary
values, with constant `1 + |v|`. -/
theorem abs_stationaryValue_sub_le_of_uniform_close {X : Type*} {C : Set X}
    {K K' P P' : X → ℝ} {v ε : ℝ}
    (hne : C.Nonempty)
    (hbdd : BddBelow ((fun w ↦ K w + v * P w) '' C))
    (hbdd' : BddBelow ((fun w ↦ K' w + v * P' w) '' C))
    (hclose : ∀ w ∈ C, |K w - K' w| ≤ ε ∧ |P w - P' w| ≤ ε) :
    |stationaryValue K P C v - stationaryValue K' P' C v| ≤ (1 + |v|) * ε := by
  have h12 := stationaryValue_le_add_of_uniform_close hne hbdd hclose
  have h21 := stationaryValue_le_add_of_uniform_close hne hbdd'
    (fun w hw ↦ by
      obtain ⟨h1, h2⟩ := hclose w hw
      refine ⟨?_, ?_⟩
      · rw [abs_sub_comm]
        exact h1
      · rw [abs_sub_comm]
        exact h2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Uniform convergence of the kinetic and probe data on a common nonempty
class implies convergence of the stationary values at every fixed tilt. -/
theorem tendsto_stationaryValue_of_uniform_convergence {W Z : Type*} {l : Filter Z}
    {C : Set W} {K : Z → W → ℝ} {P : Z → W → ℝ} {z₀ : Z} {G v : ℝ}
    (hne : C.Nonempty)
    (hK0 : ∀ w ∈ C, 0 ≤ K z₀ w)
    (hP0 : ∀ w ∈ C, |P z₀ w| ≤ G)
    (hconv : ∀ ε > 0, ∀ᶠ z in l, ∀ w ∈ C,
      |K z w - K z₀ w| ≤ ε ∧ |P z w - P z₀ w| ≤ ε) :
    Tendsto (fun z ↦ stationaryValue (K z) (P z) C v) l
      (𝓝 (stationaryValue (K z₀) (P z₀) C v)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hden : 0 < 1 + |v| := by positivity
  have hεpos : 0 < η / (2 * (1 + |v|)) := by positivity
  filter_upwards [hconv 1 one_pos, hconv (η / (2 * (1 + |v|))) hεpos] with z hz1 hzε
  have hPz : ∀ w ∈ C, |P z w| ≤ G + 1 := by
    intro w hw
    have h1 : |P z w - P z₀ w| ≤ 1 := (hz1 w hw).2
    have h0 : |P z₀ w| ≤ G := hP0 w hw
    calc |P z w| = |(P z w - P z₀ w) + P z₀ w| := by
          congr 1
          ring
      _ ≤ |P z w - P z₀ w| + |P z₀ w| := abs_add_le _ _
      _ ≤ 1 + G := by linarith
      _ = G + 1 := by ring
  have hKz : ∀ w ∈ C, -(1 : ℝ) ≤ K z w := by
    intro w hw
    have h1 : |K z w - K z₀ w| ≤ 1 := (hz1 w hw).1
    have h0 : 0 ≤ K z₀ w := hK0 w hw
    have hle : K z w - K z₀ w ≤ |K z w - K z₀ w| := le_abs_self _
    have hge : -|K z w - K z₀ w| ≤ K z w - K z₀ w := neg_abs_le _
    linarith
  have hbddz : BddBelow ((fun w ↦ K z w + v * P z w) '' C) :=
    bddBelow_stationaryValue_of_lower_bound (c := 1) (G := G + 1) (v := v) hKz hPz
  have hbdd0 : BddBelow ((fun w ↦ K z₀ w + v * P z₀ w) '' C) :=
    bddBelow_stationaryValue_of_lower_bound (c := 0) (G := G) (v := v)
      (fun w hw ↦ by simpa using hK0 w hw) hP0
  have hclose := abs_stationaryValue_sub_le_of_uniform_close hne hbddz hbdd0 hzε
  have hmul : (1 + |v|) * (η / (2 * (1 + |v|))) = η / 2 := by
    field_simp
  rw [Real.dist_eq]
  have hle : |stationaryValue (K z) (P z) C v - stationaryValue (K z₀) (P z₀) C v| ≤
      η / 2 := by
    simpa only [hmul] using hclose
  linarith

/-! ## Joint continuity in the root and the tilt -/

/-- Joint continuity at `(z₀, v₀)` from root continuity at every fixed tilt and
a uniform Lipschitz bound in the tilt. -/
theorem continuousAt_uncurry_of_continuousAt_fst_of_lipschitz_snd
    {Z : Type*} [TopologicalSpace Z] {f : Z → ℝ → ℝ} {z₀ : Z} {v₀ G : ℝ}
    (_hG : 0 ≤ G)
    (hcont : ∀ v, ContinuousAt (fun z ↦ f z v) z₀)
    (hlip : ∀ z v v', |f z v - f z v'| ≤ G * |v - v'|) :
    ContinuousAt (fun p : Z × ℝ ↦ f p.1 p.2) (z₀, v₀) := by
  change Tendsto (fun p : Z × ℝ ↦ f p.1 p.2) (𝓝 (z₀, v₀)) (𝓝 (f z₀ v₀))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : Z × ℝ ↦ G * |p.2 - v₀|) (𝓝 (z₀, v₀)) (𝓝 0) := by
    have hsnd : Tendsto (fun p : Z × ℝ ↦ p.2) (𝓝 (z₀, v₀)) (𝓝 v₀) :=
      continuous_snd.tendsto _
    have hconst : Tendsto (fun _ : Z × ℝ ↦ v₀) (𝓝 (z₀, v₀)) (𝓝 v₀) :=
      tendsto_const_nhds
    have hsub : Tendsto (fun p : Z × ℝ ↦ p.2 - v₀) (𝓝 (z₀, v₀)) (𝓝 0) := by
      simpa using hsnd.sub hconst
    have habs : Tendsto (fun p : Z × ℝ ↦ |p.2 - v₀|) (𝓝 (z₀, v₀)) (𝓝 0) := by
      simpa using hsub.abs
    simpa using (tendsto_const_nhds.mul habs :
      Tendsto (fun p : Z × ℝ ↦ G * |p.2 - v₀|) (𝓝 (z₀, v₀)) (𝓝 (G * 0)))
  have h2 : Tendsto (fun p : Z × ℝ ↦ |f p.1 v₀ - f z₀ v₀|)
      (𝓝 (z₀, v₀)) (𝓝 0) := by
    have hfst : Tendsto (fun p : Z × ℝ ↦ p.1) (𝓝 (z₀, v₀)) (𝓝 z₀) :=
      continuous_fst.tendsto _
    have hf : Tendsto (fun p : Z × ℝ ↦ f p.1 v₀) (𝓝 (z₀, v₀)) (𝓝 (f z₀ v₀)) :=
      (hcont v₀).tendsto.comp hfst
    have hconst : Tendsto (fun _ : Z × ℝ ↦ f z₀ v₀) (𝓝 (z₀, v₀)) (𝓝 (f z₀ v₀)) :=
      tendsto_const_nhds
    have hsub : Tendsto (fun p : Z × ℝ ↦ f p.1 v₀ - f z₀ v₀)
        (𝓝 (z₀, v₀)) (𝓝 0) := by
      simpa using hf.sub hconst
    simpa using hsub.abs
  have hsum : Tendsto
      (fun p : Z × ℝ ↦ G * |p.2 - v₀| + |f p.1 v₀ - f z₀ v₀|)
      (𝓝 (z₀, v₀)) (𝓝 0) := by
    simpa using h1.add h2
  refine squeeze_zero (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hsum
  calc ‖f p.1 p.2 - f z₀ v₀‖ = |f p.1 p.2 - f z₀ v₀| := Real.norm_eq_abs _
    _ = |(f p.1 p.2 - f p.1 v₀) + (f p.1 v₀ - f z₀ v₀)| := by ring_nf
    _ ≤ |f p.1 p.2 - f p.1 v₀| + |f p.1 v₀ - f z₀ v₀| := abs_add_le _ _
    _ ≤ G * |p.2 - v₀| + |f p.1 v₀ - f z₀ v₀| := by
        have := hlip p.1 p.2 v₀
        linarith

/-- Joint continuity of the stationary value family, under eventual local
constancy of the classes and uniform convergence of kinetic/probe data. -/
theorem continuous_stationaryPressureFamily {W Z : Type*} [TopologicalSpace Z]
    {K : Z → W → ℝ} {P : Z → W → ℝ} {Cw : Z → Set W} {G : ℝ}
    (hG : 0 ≤ G)
    (hne : ∀ z, (Cw z).Nonempty)
    (hK : ∀ z w, w ∈ Cw z → 0 ≤ K z w)
    (hP : ∀ z w, w ∈ Cw z → |P z w| ≤ G)
    (hclass : ∀ z₀, ∀ᶠ z in 𝓝 z₀, Cw z = Cw z₀)
    (hconv : ∀ z₀, ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ w ∈ Cw z₀, |K z w - K z₀ w| ≤ ε ∧ |P z w - P z₀ w| ≤ ε) :
    Continuous (fun p : Z × ℝ ↦ stationaryValue (K p.1) (P p.1) (Cw p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z₀, v₀⟩
  refine continuousAt_uncurry_of_continuousAt_fst_of_lipschitz_snd
    (f := fun z v ↦ stationaryValue (K z) (P z) (Cw z) v) hG ?_ ?_
  · intro v
    have hroot : Tendsto (fun z ↦ stationaryValue (K z) (P z) (Cw z₀) v) (𝓝 z₀)
        (𝓝 (stationaryValue (K z₀) (P z₀) (Cw z₀) v)) :=
      tendsto_stationaryValue_of_uniform_convergence (l := 𝓝 z₀)
        (C := Cw z₀) (hne := hne z₀)
        (hK0 := fun w hw ↦ hK z₀ w hw)
        (hP0 := fun w hw ↦ hP z₀ w hw)
        (hconv := hconv z₀)
    exact hroot.congr' ((hclass z₀).mono fun z hz ↦ by
      change stationaryValue (K z) (P z) (Cw z₀) v =
        stationaryValue (K z) (P z) (Cw z) v
      rw [hz])
  · intro z v v'
    exact abs_stationaryValue_sub_le (hne z)
      (fun v ↦ bddBelow_stationaryValue (G := G) (v := v) (hK z) (hP z))
      hG (hP z) v v'

/-- The `j`-th member of the stationary pressure family is jointly continuous. -/
theorem continuous_stationaryPressureFamily_apply {W Z : Type*} [TopologicalSpace Z]
    (K : ℕ → Z → W → ℝ) (P : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W) {G : ℝ}
    (hG : 0 ≤ G)
    (hne : ∀ j z, (Cw j z).Nonempty)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |P j z w| ≤ G)
    (hclass : ∀ j z₀, ∀ᶠ z in 𝓝 z₀, Cw j z = Cw j z₀)
    (hconv : ∀ j z₀, ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ w ∈ Cw j z₀, |K j z w - K j z₀ w| ≤ ε ∧ |P j z w - P j z₀ w| ≤ ε)
    (j : ℕ) :
    Continuous (fun p : Z × ℝ ↦ stationaryPressureFamily K P Cw j p.1 p.2) :=
  continuous_stationaryPressureFamily (K := K j) (P := P j) (Cw := Cw j)
    hG (hne j) (hK j) (hP j) (hclass j) (hconv j)

/-! ## Intensity-core upper bounds -/

section CoreUpper

variable {E M Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- On the retained core, the theta weight is bounded by the core's upper
intensity bound. -/
theorem PopulationSeedIntensityCore.theta_le_upper
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore) :
    ∀ z ∈ D.roots, populationAtlasTheta P a κ lambda j z ≤ D.upper := by
  intro z hz
  exact (D.bounds (populationSeedRootLabelValue (P j).seed a z)
    (mem_image_of_mem _ hz)).2

/-- The core upper bound is nonnegative, since the core also carries a positive
lower bound. -/
theorem PopulationSeedIntensityCore.upper_nonneg
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore) : 0 ≤ D.upper :=
  D.lower_pos.le.trans D.lower_le_upper

/-- On a produced intensity core, its existing positive lower density bound
controls the inverse kinetic density power. This is a local output of the core
construction, rather than an additional global density assumption. -/
theorem PopulationSeedIntensityCore.abs_populationAtlasIntegrand_stationary_le
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    {G Cb : ℝ} (hG : 0 ≤ G) (hCb : 0 ≤ Cb)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |Ppr j z w| ≤ G)
    (hcomp : ∀ j z, ∃ w ∈ Cw j z, K j z w ≤ Cb)
    {q t : ℝ} (hq : 2 < q) :
    ∀ z ∈ D.roots,
      |populationAtlasIntegrand P a κ lambda (stationaryPressureFamily K Ppr Cw j) j q t z|
        ≤ Cb * D.lower ^ (-2 / q) + |t| * G := by
  intro z hz
  have hbase := OTSelector.Reconstruction.abs_populationAtlasIntegrand_stationary_le
    (t := t) P a κ lambda K Ppr Cw hG hCb hK hP hcomp hq j z
  have hlower : D.lower ≤ populationAtlasTheta P a κ lambda j z :=
    (D.bounds (populationSeedRootLabelValue (P j).seed a z)
      (mem_image_of_mem _ hz)).1
  have hqpos : 0 < q := by linarith
  have hpow : populationAtlasTheta P a κ lambda j z ^ (-2 / q) ≤ D.lower ^ (-2 / q) :=
    Real.rpow_le_rpow_of_nonpos D.lower_pos hlower (div_nonpos_of_nonpos_of_nonneg
      (by norm_num) hqpos.le)
  exact hbase.trans (add_le_add (mul_le_mul_of_nonneg_left hpow hCb) (le_refl _))

/-- Combining the core upper bound with an explicit off-core bound for the same
piece yields a global theta bound `≤ max D.upper U`. This fact by itself
does not bound the population integrand with its negative density exponent. -/
theorem PopulationSeedIntensityCore.theta_le_max_of_not_mem
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    {U : ℝ} (htheta_off : ∀ z, z ∉ D.roots →
      populationAtlasTheta P a κ lambda j z ≤ U) :
    ∀ z, populationAtlasTheta P a κ lambda j z ≤ max D.upper U := by
  intro z
  by_cases hz : z ∈ D.roots
  · exact (D.theta_le_upper (j := j) P a κ lambda z hz).trans (le_max_left D.upper U)
  · exact (htheta_off z hz).trans (le_max_right D.upper U)

end CoreUpper

/-! ## Full-atlas finite weighted sums and the complement -/

section CoreComplement

variable {Z : Type*} [MeasurableSpace Z]

/-- A finite weighted-sum approximation on a measurable core `K` and a uniform
bound on the complement give a full-atlas approximation with error
`η * λ(K) + B * λ(Kᶜ)`. -/
theorem abs_integral_sub_weighted_sum_le_of_core_complement
    {K : Set Z} (hK : MeasurableSet K) (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {B η : ℝ} (hB : 0 ≤ B)
    {ι : Type*} [Fintype ι] (cell : ι → Set Z) (center : ι → Z)
    (hint : Integrable f lambda) (hbound : ∀ z, |f z| ≤ B)
    (hcore : |∫ z in K, f z ∂lambda - ∑ i, (lambda (cell i)).toReal * f (center i)|
      ≤ η * (lambda K).toReal)
    {ε : ℝ≥0∞} (hε : ε ≠ (∞ : ℝ≥0∞)) (hsmall : lambda Kᶜ < ε) :
    |∫ z, f z ∂lambda - ∑ i, (lambda (cell i)).toReal * f (center i)|
      ≤ η * (lambda K).toReal + B * ε.toReal := by
  have hcompl := abs_integral_sub_integral_core_le_of_bound hK lambda hB hint hbound
  have hKc : (lambda Kᶜ).toReal ≤ ε.toReal := ENNReal.toReal_mono hε hsmall.le
  have hcompl' : |∫ z, f z ∂lambda - ∫ z in K, f z ∂lambda| ≤ B * ε.toReal :=
    hcompl.trans (mul_le_mul_of_nonneg_left hKc hB)
  calc
    |∫ z, f z ∂lambda - ∑ i, (lambda (cell i)).toReal * f (center i)|
        = |(∫ z, f z ∂lambda - ∫ z in K, f z ∂lambda) +
            (∫ z in K, f z ∂lambda -
              ∑ i, (lambda (cell i)).toReal * f (center i))| := by
          congr 1
          ring
    _ ≤ |∫ z, f z ∂lambda - ∫ z in K, f z ∂lambda| +
          |∫ z in K, f z ∂lambda -
            ∑ i, (lambda (cell i)).toReal * f (center i)| :=
        abs_add_le _ _
    _ ≤ B * ε.toReal + η * (lambda K).toReal := add_le_add hcompl' hcore
    _ = η * (lambda K).toReal + B * ε.toReal := by ring

end CoreComplement

/-! ## The atlas with the core upper bound and its complement -/

section AtlasCoreComplement

variable {E M Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Full-atlas finite weighted-sum approximation for one stationary-family
atlas term: the partition approximation on the intensity core combines with the
uniform complement bound and the core's small complement, giving error
`η * λ(core) + B * εcomp.toReal`. -/
theorem PopulationSeedIntensityCore.exists_weighted_sum_approximation_with_complement
    [PseudoMetricSpace Z] [PolishSpace Z] [BorelSpace Z]
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    {q t η B : ℝ} {εcomp : ℝ≥0∞} (hq : 2 < q) (hη : 0 < η) (hB : 0 ≤ B)
    (hcont : ContinuousOn
      (fun p : Z × ℝ ↦ stationaryPressureFamily K Ppr Cw j p.1 p.2)
      (D.roots ×ˢ univ))
    (hint : Integrable (fun z ↦
      populationAtlasIntegrand P a κ lambda (stationaryPressureFamily K Ppr Cw j) j q t z)
      lambda)
    (hbound : ∀ z, |populationAtlasIntegrand P a κ lambda
      (stationaryPressureFamily K Ppr Cw j) j q t z| ≤ B)
    (hεcomp : εcomp ≠ (∞ : ℝ≥0∞)) (hsmall : lambda D.rootsᶜ < εcomp) :
    ∃ δ > 0, ∀ {centers : Set Z} {U : Z → Set Z}
      (Q : FiniteRootNeighborhoodPartition D.roots centers U),
      (∀ i : Fin Q.count, Q.center i ∈ D.roots) →
      (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      |∫ z, populationAtlasIntegrand P a κ lambda
          (stationaryPressureFamily K Ppr Cw j) j q t z ∂lambda -
        ∑ i : Fin Q.count, (lambda (Q.cell i)).toReal *
          populationAtlasIntegrand P a κ lambda
            (stationaryPressureFamily K Ppr Cw j) j q t (Q.center i)|
        ≤ η * (lambda D.roots).toReal + B * εcomp.toReal := by
  obtain ⟨δ, hδ, happrox⟩ := D.exists_weighted_sum_approximation P a κ lambda
    (stationaryPressureFamily K Ppr Cw j) hq hη hcont
  refine ⟨δ, hδ, fun Q hcenters hdiam ↦ ?_⟩
  exact abs_integral_sub_weighted_sum_le_of_core_complement
    (K := D.roots) (f := fun z ↦ populationAtlasIntegrand P a κ lambda
      (stationaryPressureFamily K Ppr Cw j) j q t z) (B := B) (η := η)
    D.compact.measurableSet lambda hB Q.cell Q.center hint hbound
    (happrox Q hcenters hdiam) hεcomp hsmall

/-- The root-continuity theorem discharges the explicit continuity hypothesis of
`PopulationSeedIntensityCore.exists_weighted_sum_approximation_stationary`. -/
theorem PopulationSeedIntensityCore.exists_weighted_sum_approximation_stationary_of_continuous
    [PseudoMetricSpace Z] [PolishSpace Z] [BorelSpace Z]
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    {G q t η : ℝ} (hG : 0 ≤ G) (hq : 2 < q) (hη : 0 < η)
    (hne : ∀ j z, (Cw j z).Nonempty)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |Ppr j z w| ≤ G)
    (hclass : ∀ j z₀, ∀ᶠ z in 𝓝 z₀, Cw j z = Cw j z₀)
    (hconv : ∀ j z₀, ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ w ∈ Cw j z₀, |K j z w - K j z₀ w| ≤ ε ∧ |Ppr j z w - Ppr j z₀ w| ≤ ε) :
    ∃ δ > 0, ∀ {centers : Set Z} {U : Z → Set Z}
      (Q : FiniteRootNeighborhoodPartition D.roots centers U),
      (∀ i : Fin Q.count, Q.center i ∈ D.roots) →
      (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      |∫ z in D.roots, populationAtlasIntegrand P a κ lambda
          (stationaryPressureFamily K Ppr Cw j) j q t z ∂lambda -
        ∑ i : Fin Q.count, (lambda (Q.cell i)).toReal *
          populationAtlasIntegrand P a κ lambda
            (stationaryPressureFamily K Ppr Cw j) j q t (Q.center i)|
        ≤ η * (lambda D.roots).toReal :=
  D.exists_weighted_sum_approximation_stationary P a κ lambda K Ppr Cw hq hη
    (continuous_stationaryPressureFamily_apply K Ppr Cw hG hne hK hP hclass hconv j).continuousOn

end AtlasCoreComplement

/-! ## The physical pressure core's complement -/

section PressureCoreComplement

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {εcore : ℝ≥0∞}

/-- The physical complement masses of a `PopulationPressureCore` are exactly the
original label mass removed from the atlas. -/
theorem PopulationPressureCore.complement_mass_eq
    (C : PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good εcore) :
    η₀ (a ⁻¹' C.rootsᶜ) = lambda C.rootsᶜ ∧
      η₁ (a ⁻¹' C.rootsᶜ) = lambda C.rootsᶜ := by
  have h := C.remainder_mass
  exact ⟨h.1, h.2.1⟩

/-- A weighted-sum approximation on the pressure core's roots plus the uniform
complement bound gives the full-atlas approximation with error
`η * λ(roots) + B * εcore.toReal`, using `complement_small`. -/
theorem PopulationPressureCore.abs_integral_sub_weighted_sum_le
    (C : PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good εcore)
    [IsFiniteMeasure lambda]
    {f : (ℚ → M) → ℝ} {B η : ℝ} (hB : 0 ≤ B)
    {ι : Type*} [Fintype ι] (cell : ι → Set (ℚ → M)) (center : ι → (ℚ → M))
    (hKmeas : MeasurableSet C.roots)
    (hint : Integrable f lambda) (hbound : ∀ z, |f z| ≤ B)
    (hcore : |∫ z in C.roots, f z ∂lambda -
        ∑ i, (lambda (cell i)).toReal * f (center i)|
      ≤ η * (lambda C.roots).toReal)
    (hε : εcore ≠ (∞ : ℝ≥0∞)) :
    |∫ z, f z ∂lambda - ∑ i, (lambda (cell i)).toReal * f (center i)|
      ≤ η * (lambda C.roots).toReal + B * εcore.toReal :=
  abs_integral_sub_weighted_sum_le_of_core_complement
    (K := C.roots) (f := f) (B := B) (η := η)
    hKmeas lambda hB cell center hint hbound hcore hε C.complement_small

end PressureCoreComplement

end OTSelector.Reconstruction
