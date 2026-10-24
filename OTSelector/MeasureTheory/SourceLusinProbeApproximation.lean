import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.TietzeExtension
import OTSelector.MeasureTheory.LusinCompactCore
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneSourceLusinCompactProbeApproximation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneSourceLusinCompactProbeApproximation`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.SourceLusinProbeApproximation

## Lemma skeleton

* **Conditions:** A finite Radon source law, measurable source coordinates and source flag, continuous clock and a compact physical test.
* **Objects:** One large compact Lusin core with exact continuous coordinate/flag extensions and a uniformly bounded continuous probe approximant for all plans with that fixed source marginal.
* **Proof detail:** Apply Lusin jointly to the source data, extend by Tietze while retaining the flag range, clip the probe bound and pay only the common-marginal mass outside the compact core.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110): Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=14): Section 4A2F(d-ix), p. 14 (Tietze extension theorem).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Lusin/Tietze approximation with a uniform plan error; no target-marginal control is assumed.
-/

/-!
# Source Lusin cores for bounded physical probe approximation

The source coordinate and source-set indicator are continuous on one compact set of arbitrarily
large source mass. Tietze extensions preserve both exactly there and keep the flag in [0,1].
-/

open Set MeasureTheory TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- The source coordinate and indicator admit global continuous extensions agreeing on one
compact Lusin core, with arbitrarily small loss of the original source measure. -/
theorem exists_source_lusin_compact_coordinate_flag_extensions
    {q : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → (Fin q → ℝ)} (hf : Measurable f)
    {H : Set X} (hH : MeasurableSet H) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧
      ∃ (fcont : C(X, Fin q → ℝ)) (flag : C(X, ℝ)),
        (∀ x, flag x ∈ Icc 0 1) ∧ EqOn fcont f K ∧
          EqOn flag (H.indicator (fun _ ↦ (1 : ℝ))) K := by
  have hflag : Measurable (H.indicator (fun _ : X ↦ (1 : ℝ))) :=
    measurable_const.indicator hH
  obtain ⟨K, _, hK, hsmall, hcont⟩ := OTSelector.Geometry.exists_lusin_compact_core
    (μ := μ) MeasurableSet.univ (measure_ne_top μ univ) (hf.prodMk hflag)
      (ENNReal.ofReal_pos.mpr hε).ne'
  have hcompl : (univ : Set X) \ K = Kᶜ :=
    Set.ext fun _ ↦ ⟨fun hx ↦ hx.2, fun hx ↦ ⟨mem_univ _, hx⟩⟩
  have hsmall' : μ Kᶜ < ENNReal.ofReal ε := hcompl ▸ hsmall
  let fK : C(K, Fin q → ℝ) :=
    ⟨fun x ↦ f x, continuousOn_iff_continuous_domRestrict.mp hcont.fst⟩
  let flagK : C(K, ℝ) :=
    ⟨fun x ↦ H.indicator (fun _ ↦ (1 : ℝ)) x,
      continuousOn_iff_continuous_domRestrict.mp hcont.snd⟩
  obtain ⟨fcont, hfcont⟩ := fK.exists_restrict_eq hK.isClosed
  have hflagK (x : K) : flagK x ∈ Icc 0 1 := by
    change H.indicator (fun _ ↦ (1 : ℝ)) x.val ∈ Icc 0 1
    by_cases hx : x.val ∈ H
    · rw [Set.indicator_of_mem hx]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [Set.indicator_of_notMem hx]
      exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨flag, hflagbound, hflagEq⟩ := flagK.exists_restrict_eq_forall_mem_of_closed
    hflagK (nonempty_Icc.mpr zero_le_one) hK.isClosed
  refine ⟨K, hK, hsmall', fcont, flag, hflagbound, ?_, ?_⟩
  · intro x hx
    exact congrArg (fun g : C(K, Fin q → ℝ) ↦ g ⟨x, hx⟩) hfcont
  · intro x hx
    exact congrArg (fun g : C(K, ℝ) ↦ g ⟨x, hx⟩) hflagEq

/-- An original physical probe whose only potentially discontinuous inputs depend on the source. -/
def sourceCompactProbe {q : ℕ} (f : X → (Fin q → ℝ)) (H : Set X)
    (clock : X → ℝ) (g : C_c((Fin q → ℝ) × (ℝ × ℝ), ℝ)) (p : X × X) : ℝ :=
  H.indicator (fun x ↦ g (f x, (clock x, clock p.2))) p.1

/-- One bounded continuous approximation controls the original probe under every finite plan
with the same source marginal. Both the L1 error and the absolute integral error use only source
mass; no target marginal or target tail assumption is needed. -/
theorem exists_source_compactProbe_uniform_approximation
    {q : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → (Fin q → ℝ)} (hf : Measurable f)
    {H : Set X} (hH : MeasurableSet H) (clock : X → ℝ) (hclock : Continuous clock)
    (g : C_c((Fin q → ℝ) × (ℝ × ℝ), ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : (X × X) →ᵇ ℝ, ‖F‖ ≤ ‖g.toBoundedContinuousFunction‖ ∧
      ∀ (π : Measure (X × X)) [IsFiniteMeasure π], π.map Prod.fst = μ →
        Integrable (sourceCompactProbe f H clock g) π ∧
        (∫ p, |sourceCompactProbe f H clock g p - F p| ∂π) ≤
          2 * ‖g.toBoundedContinuousFunction‖ * ε ∧
        |(∫ p, sourceCompactProbe f H clock g p ∂π) - ∫ p, F p ∂π| ≤
          2 * ‖g.toBoundedContinuousFunction‖ * ε := by
  obtain ⟨K, hK, hsmall, fcont, flag, hflagbound, hfcont, hflagEq⟩ :=
    exists_source_lusin_compact_coordinate_flag_extensions μ hf hH hε
  let B : ℝ := ‖g.toBoundedContinuousFunction‖
  have hB : 0 ≤ B := norm_nonneg _
  have hg (z : (Fin q → ℝ) × (ℝ × ℝ)) : ‖g z‖ ≤ B := by
    exact g.toBoundedContinuousFunction.norm_coe_le_norm z
  have hflagNorm (x : X) : ‖flag x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hflagbound x).1]
    exact (hflagbound x).2
  let raw : X × X → ℝ := fun p ↦
    flag p.1 * g (fcont p.1, (clock p.1, clock p.2))
  have hrawCont : Continuous raw :=
    (flag.continuous.comp continuous_fst).mul
      (g.continuous.comp ((fcont.continuous.comp continuous_fst).prodMk
        ((hclock.comp continuous_fst).prodMk (hclock.comp continuous_snd))))
  have hrawBound (p : X × X) : ‖raw p‖ ≤ B := by
    dsimp only [raw]
    rw [norm_mul]
    exact (mul_le_mul (hflagNorm p.1) (hg _) (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul B)
  let F : (X × X) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup raw hrawCont B hrawBound
  have hFnorm : ‖F‖ ≤ B := (BoundedContinuousFunction.norm_le hB).mpr hrawBound
  let orig : X × X → ℝ := sourceCompactProbe f H clock g
  have hOrigEq (p : X × X) : orig p =
      H.indicator (fun _ ↦ (1 : ℝ)) p.1 * g (f p.1, (clock p.1, clock p.2)) := by
    dsimp only [orig, sourceCompactProbe]
    by_cases hx : p.1 ∈ H
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hOrigBound (p : X × X) : ‖orig p‖ ≤ B := by
    dsimp only [orig, sourceCompactProbe]
    by_cases hx : p.1 ∈ H
    · rw [Set.indicator_of_mem hx]
      exact hg _
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact hB
  have hOrigMeas : Measurable orig := by
    have hEq : orig = fun p : X × X ↦
        H.indicator (fun _ ↦ (1 : ℝ)) p.1 * g (f p.1, (clock p.1, clock p.2)) :=
      funext hOrigEq
    rw [hEq]
    exact ((measurable_const.indicator hH).comp measurable_fst).mul
      (g.continuous.measurable.comp ((hf.comp measurable_fst).prodMk
        ((hclock.measurable.comp measurable_fst).prodMk
          (hclock.measurable.comp measurable_snd))))
  have hExact (p : X × X) (hp : p.1 ∈ K) : orig p = F p := by
    change orig p = flag p.1 * g (fcont p.1, (clock p.1, clock p.2))
    rw [hflagEq hp, hfcont hp]
    exact hOrigEq p
  refine ⟨F, hFnorm, ?_⟩
  intro π hfinite hπ
  have hIntOrig : Integrable orig π := Integrable.of_bound hOrigMeas.aestronglyMeasurable
    B (ae_of_all _ hOrigBound)
  have hIntF : Integrable (fun p ↦ F p) π :=
    Integrable.of_bound F.continuous.aestronglyMeasurable B (ae_of_all _ hrawBound)
  let bad : Set (X × X) := Prod.fst ⁻¹' Kᶜ
  have hbad : MeasurableSet bad := hK.isClosed.measurableSet.compl.preimage measurable_fst
  have hError (p : X × X) : |orig p - F p| ≤
      bad.indicator (fun _ ↦ 2 * B) p := by
    by_cases hp : p ∈ bad
    · rw [Set.indicator_of_mem hp]
      calc
        |orig p - F p| = ‖orig p - F p‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖orig p‖ + ‖F p‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hOrigBound p) (hrawBound p)
        _ = 2 * B := by ring
    · have hpK : p.1 ∈ K := Classical.not_not.mp hp
      rw [Set.indicator_of_notMem hp, hExact p hpK, sub_self, abs_zero]
  have hbadmass : π.real bad = μ.real Kᶜ := by
    calc
      π.real bad = (π.map Prod.fst).real Kᶜ :=
        (map_measureReal_apply measurable_fst hK.isClosed.measurableSet.compl).symm
      _ = μ.real Kᶜ := congrArg (fun ν : Measure X ↦ ν.real Kᶜ) hπ
  have hMass : μ.real Kᶜ ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le hsmall.le
  have hL1 : (∫ p, |orig p - F p| ∂π) ≤ 2 * B * ε := by
    calc
      (∫ p, |orig p - F p| ∂π) ≤ ∫ p, bad.indicator (fun _ ↦ 2 * B) p ∂π :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
          ((integrable_const (2 * B)).indicator hbad) (ae_of_all _ hError)
      _ = π.real bad * (2 * B) := by rw [integral_indicator_const _ hbad, smul_eq_mul]
      _ = μ.real Kᶜ * (2 * B) := by rw [hbadmass]
      _ ≤ ε * (2 * B) := mul_le_mul_of_nonneg_right hMass (mul_nonneg (by norm_num) hB)
      _ = 2 * B * ε := by ring
  refine ⟨hIntOrig, hL1, ?_⟩
  calc
    |(∫ p, orig p ∂π) - ∫ p, F p ∂π| = |∫ p, orig p - F p ∂π| := by
      rw [integral_sub hIntOrig hIntF]
    _ ≤ ∫ p, |orig p - F p| ∂π := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun p ↦ orig p - F p)
    _ ≤ 2 * B * ε := hL1

end OTSelector.Reconstruction

end
end
