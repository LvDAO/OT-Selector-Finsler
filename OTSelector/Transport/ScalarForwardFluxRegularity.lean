import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Floor
import OTSelector.Transport.ScalarForwardFlux
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerIntrinsicActiveSurplusRegularity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerIntrinsicActiveSurplusRegularity`; the selected original proof blocks follow. -/
section

/-!
# Transport.ScalarForwardFluxRegularity

## Lemma skeleton

* **Conditions:** Finite scalar couplings with null coordinate singleton fibers and measurable label slices; joint measurability uses continuity in the real parameter.
* **Objects:** Continuous scalar flux and jointly measurable label/parameter flux.
* **Proof detail:** Use the CDF atom jump identity for continuity. Approximate the real parameter by dyadic floor slices, whose countable fibers are measurable, then take the pointwise continuous limit.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=19): Section 1.2, Theorem 1.2.1(iii)–(v), p. 11.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (composition): CDF and Caratheodory-style measurable/continuous assembly for a real second parameter; no transport existence result is asserted.
-/

/-!
# Measurability and continuity of the ray surplus

This module derives the two regularity inputs of the segment-test measurability
argument for the ray surplus
`rayFlux (κ z) r = (κ z {p | p.1 ≤ r}).toReal - (κ z {p | p.2 ≤ r}).toReal`
of a measurable family of finite atomless couplings.

## Continuity in the ray parameter

The cumulative distribution function `r ↦ ν (Iic r)` of a finite measure is
right continuous; atomlessness makes it left continuous as well, so the CDF of
an atomless finite measure is continuous (`continuous_cdfIic`).  Applying this
to the two marginals of the coupling yields continuity of the ray surplus in
the ray parameter (`continuous_rayFlux`).

## Joint measurability in the label variable and the ray parameter

A function that is measurable in the label variable and continuous in the ray
parameter is jointly Borel measurable (`measurable_of_measurable_continuous_second`),
by dyadic approximation of the ray parameter: the dyadic values are measurable
functions of the ray parameter with Borel floor-interval fibers, and the ray
surplus is a pointwise limit of measurable functions.  Combined with the CDF
slice measurability supplied by the geometric transport family, this gives
joint measurability of the ray surplus (`measurable_and_continuous_rayFlux`).
-/

open Set Function MeasureTheory Filter
open scoped ENNReal MeasureTheory Topology

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Continuity of the CDF of an atomless finite measure -/

/-- **Continuity of the CDF of an atomless finite measure.**  The cumulative
distribution function `r ↦ (ν (Iic r)).toReal` of a finite measure without
atoms is continuous. -/
theorem continuous_cdfIic (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hatom : ∀ r : ℝ, ν {r} = 0) :
    Continuous fun r : ℝ => (ν (Iic r)).toReal := by
  have hmono : Monotone fun r : ℝ => (ν (Iic r)).toReal :=
    fun a b hab => ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Iic_subset_Iic.mpr hab))
  have hone : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => one_div_pos.mpr (by positivity)
  refine continuous_iff_continuousAt.mpr (fun r0 => tendsto_order.mpr ⟨?_, ?_⟩)
  · -- left continuity: the intervals `Ioc (r0 - 1/(n+1)) r0` shrink to the atom `{r0}`
    intro b hb
    let s : ℕ → Set ℝ := fun n => Ioc (r0 - 1 / ((n : ℝ) + 1)) r0
    have hs : ∀ n, NullMeasurableSet (s n) ν := fun n => measurableSet_Ioc.nullMeasurableSet
    have hanti : Antitone s := by
      intro i j hij x hx
      simp only [s, mem_Ioc] at hx ⊢
      have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.succ_le_succ hij
      exact ⟨lt_of_le_of_lt (by linarith) hx.1, hx.2⟩
    have hlim : (⋂ n, s n) = {r0} := by
      ext x
      simp only [s, mem_iInter, mem_Ioc, mem_singleton_iff]
      constructor
      · intro h
        have hxle : x ≤ r0 := (h 0).2
        refine le_antisymm hxle ?_
        by_contra hne
        have hxlt : x < r0 := lt_of_not_ge hne
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hxlt)
        exact absurd (h n).1 (by linarith)
      · rintro hx n
        rw [hx]
        exact ⟨sub_lt_self r0 (hone n), le_rfl⟩
    have hseq : Tendsto (fun n : ℕ => ν (Ioc (r0 - 1 / ((n : ℝ) + 1)) r0)) atTop (𝓝 (ν {r0})) := by
      have h := tendsto_measure_iInter_atTop (μ := ν) hs hanti ⟨0, measure_ne_top ν _⟩
      rw [hlim] at h
      exact h
    rw [hatom r0] at hseq
    have hseq' : Tendsto (fun n : ℕ => (ν (Ioc (r0 - 1 / ((n : ℝ) + 1)) r0)).toReal) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal_iff (f := fun n : ℕ => ν (Ioc (r0 - 1 / ((n : ℝ) + 1)) r0))
        (fun n => measure_ne_top ν _) (by simp)).mpr hseq
    have hsplit : ∀ n : ℕ, (ν (Iic r0)).toReal
        = (ν (Iic (r0 - 1 / ((n : ℝ) + 1)))).toReal
          + (ν (Ioc (r0 - 1 / ((n : ℝ) + 1)) r0)).toReal := by
      intro n
      have hdisj : Disjoint (Iic (r0 - 1 / ((n : ℝ) + 1))) (Ioc (r0 - 1 / ((n : ℝ) + 1)) r0) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx (not_le.mpr hx'.1)
      have hunion : Iic r0 = Iic (r0 - 1 / ((n : ℝ) + 1)) ∪ Ioc (r0 - 1 / ((n : ℝ) + 1)) r0 := by
        ext x
        simp only [mem_union, mem_Iic, mem_Ioc]
        constructor
        · intro hx
          by_cases h : x ≤ r0 - 1 / ((n : ℝ) + 1)
          · exact Or.inl h
          · exact Or.inr ⟨lt_of_not_ge h, hx⟩
        · rintro (h | ⟨h1, h2⟩)
          · linarith [hone n]
          · exact h2
      rw [hunion, measure_union hdisj measurableSet_Ioc,
        ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
    have hb' : b < (ν (Iic r0)).toReal := hb
    have hpos : 0 < (ν (Iic r0)).toReal - b := sub_pos.mpr hb'
    obtain ⟨n, hn⟩ := (hseq'.eventually (Iio_mem_nhds hpos)).exists
    refine mem_of_superset (Ioi_mem_nhds (sub_lt_self r0 (hone n))) ?_
    intro r hr
    change b < (ν (Iic r)).toReal
    have h1 : (ν (Iic (r0 - 1 / ((n : ℝ) + 1)))).toReal ≤ (ν (Iic r)).toReal := hmono (le_of_lt hr)
    have h2 := hsplit n
    have h3 : (ν (Iic r0)).toReal - (ν (Ioc (r0 - 1 / ((n : ℝ) + 1)) r0)).toReal
        = (ν (Iic (r0 - 1 / ((n : ℝ) + 1)))).toReal := by linarith
    have h4 : b < (ν (Iic r0)).toReal - (ν (Ioc (r0 - 1 / ((n : ℝ) + 1)) r0)).toReal := by linarith
    rw [h3] at h4
    exact h4.trans_le h1
  · -- right continuity: the intervals `Iic (r0 + 1/(n+1))` shrink to `Iic r0`
    intro b hb
    let s : ℕ → Set ℝ := fun n => Iic (r0 + 1 / ((n : ℝ) + 1))
    have hs : ∀ n, NullMeasurableSet (s n) ν := fun n => measurableSet_Iic.nullMeasurableSet
    have hanti : Antitone s := by
      intro i j hij x hx
      simp only [s, mem_Iic] at hx ⊢
      have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.succ_le_succ hij
      linarith
    have hlim : (⋂ n, s n) = Iic r0 := by
      ext x
      simp only [s, mem_iInter, mem_Iic]
      constructor
      · intro h
        by_contra hlt
        have hxlt : r0 < x := lt_of_not_ge hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hxlt)
        exact absurd (h n) (by linarith)
      · intro hx n
        linarith [hone n]
    have hseq : Tendsto (fun n : ℕ => ν (Iic (r0 + 1 / ((n : ℝ) + 1)))) atTop (𝓝 (ν (Iic r0))) := by
      have h := tendsto_measure_iInter_atTop (μ := ν) hs hanti ⟨0, measure_ne_top ν _⟩
      rw [hlim] at h
      exact h
    have hreal : Tendsto (fun n : ℕ => (ν (Iic (r0 + 1 / ((n : ℝ) + 1)))).toReal)
        atTop (𝓝 (ν (Iic r0)).toReal) :=
      (ENNReal.tendsto_toReal_iff (f := fun n : ℕ => ν (Iic (r0 + 1 / ((n : ℝ) + 1))))
        (fun n => measure_ne_top ν _) (measure_ne_top ν _)).mpr hseq
    have hb' : (ν (Iic r0)).toReal < b := hb
    obtain ⟨n, hn⟩ := (hreal.eventually (Iio_mem_nhds hb')).exists
    refine mem_of_superset (Iio_mem_nhds (lt_add_of_pos_right r0 (hone n))) ?_
    intro r hr
    change (ν (Iic r)).toReal < b
    have h1 : (ν (Iic r)).toReal ≤ (ν (Iic (r0 + 1 / ((n : ℝ) + 1)))).toReal := hmono (le_of_lt hr)
    nlinarith [h1, hn]

/-! ## Continuity of the ray surplus in the ray parameter -/

/-- **Continuity of the ray surplus.**  For a finite atomless coupling the ray
surplus `rayFlux κ` is continuous in the ray parameter. -/
theorem continuous_rayFlux (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ]
    (h1 : ∀ r : ℝ, κ {p : ℝ × ℝ | p.1 = r} = 0)
    (h2 : ∀ r : ℝ, κ {p : ℝ × ℝ | p.2 = r} = 0) :
    Continuous (rayFlux κ) := by
  have hmap1 : ∀ r : ℝ, (Measure.map (fun p : ℝ × ℝ => p.1) κ) (Iic r) = κ {p | p.1 ≤ r} := by
    intro r; exact Measure.map_apply measurable_fst measurableSet_Iic
  have hmap2 : ∀ r : ℝ, (Measure.map (fun p : ℝ × ℝ => p.2) κ) (Iic r) = κ {p | p.2 ≤ r} := by
    intro r; exact Measure.map_apply measurable_snd measurableSet_Iic
  have hcont1 : Continuous fun r : ℝ => (κ {p : ℝ × ℝ | p.1 ≤ r}).toReal := by
    haveI : IsFiniteMeasure (Measure.map (fun p : ℝ × ℝ => p.1) κ) := Measure.isFiniteMeasure_map κ _
    have hatom : ∀ r : ℝ, (Measure.map (fun p : ℝ × ℝ => p.1) κ) {r} = 0 := by
      intro r
      rw [Measure.map_apply measurable_fst (measurableSet_singleton r)]
      have hset : (fun p : ℝ × ℝ => p.1) ⁻¹' {r} = {p : ℝ × ℝ | p.1 = r} := by
        ext p; simp
      rw [hset]
      exact h1 r
    have h := continuous_cdfIic (Measure.map (fun p : ℝ × ℝ => p.1) κ) hatom
    have heq : (fun r : ℝ => (Measure.map (fun p : ℝ × ℝ => p.1) κ (Iic r)).toReal)
        = fun r : ℝ => (κ {p : ℝ × ℝ | p.1 ≤ r}).toReal := by
      ext r; rw [hmap1 r]
    rw [heq] at h
    exact h
  have hcont2 : Continuous fun r : ℝ => (κ {p : ℝ × ℝ | p.2 ≤ r}).toReal := by
    haveI : IsFiniteMeasure (Measure.map (fun p : ℝ × ℝ => p.2) κ) := Measure.isFiniteMeasure_map κ _
    have hatom : ∀ r : ℝ, (Measure.map (fun p : ℝ × ℝ => p.2) κ) {r} = 0 := by
      intro r
      rw [Measure.map_apply measurable_snd (measurableSet_singleton r)]
      have hset : (fun p : ℝ × ℝ => p.2) ⁻¹' {r} = {p : ℝ × ℝ | p.2 = r} := by
        ext p; simp
      rw [hset]
      exact h2 r
    have h := continuous_cdfIic (Measure.map (fun p : ℝ × ℝ => p.2) κ) hatom
    have heq : (fun r : ℝ => (Measure.map (fun p : ℝ × ℝ => p.2) κ (Iic r)).toReal)
        = fun r : ℝ => (κ {p : ℝ × ℝ | p.2 ≤ r}).toReal := by
      ext r; rw [hmap2 r]
    rw [heq] at h
    exact h
  change Continuous fun r : ℝ => (κ {p : ℝ × ℝ | p.1 ≤ r}).toReal - (κ {p : ℝ × ℝ | p.2 ≤ r}).toReal
  exact hcont1.sub hcont2

/-! ## Joint measurability in the label variable and the ray parameter -/

/-- The dyadic truncation `n ↦ ⌊2^n x⌋ / 2^n` tends to `x` for every real `x`. -/
theorem tendsto_dyadic_slice (x : ℝ) :
    Tendsto (fun n : ℕ => (⌊(2 : ℝ) ^ n * x⌋ : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 x) := by
  have hgeo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hle : ∀ n : ℕ, (⌊(2 : ℝ) ^ n * x⌋ : ℝ) / (2 : ℝ) ^ n ≤ x := by
    intro n
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [div_le_iff₀ h2]
    have h1 : (⌊(2 : ℝ) ^ n * x⌋ : ℝ) ≤ (2 : ℝ) ^ n * x := Int.floor_le _
    nlinarith
  have hge : ∀ n : ℕ, x - (1 / 2 : ℝ) ^ n ≤ (⌊(2 : ℝ) ^ n * x⌋ : ℝ) / (2 : ℝ) ^ n := by
    intro n
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h1 : (2 : ℝ) ^ n * x < (⌊(2 : ℝ) ^ n * x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hpow : ((1 / 2 : ℝ) ^ n) = ((2 : ℝ) ^ n)⁻¹ := by
      rw [← inv_pow]; norm_num
    have hmid : x < (⌊(2 : ℝ) ^ n * x⌋ : ℝ) / (2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n := by
      rw [hpow, show (⌊(2 : ℝ) ^ n * x⌋ : ℝ) / (2 : ℝ) ^ n + ((2 : ℝ) ^ n)⁻¹
          = ((⌊(2 : ℝ) ^ n * x⌋ : ℝ) + 1) / (2 : ℝ) ^ n by rw [add_div, one_div]]
      rw [lt_div_iff₀ h2]
      nlinarith
    linarith
  have hlow : Tendsto (fun n : ℕ => x - (1 / 2 : ℝ) ^ n) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub hgeo
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    hge hle

/-- **Dyadic slices are jointly measurable.**  If `H z ·` is defined by a family
of functions that is measurable in `z` for every ray parameter, then the dyadic
approximation `(z, r) ↦ H z (⌊2^n r⌋ / 2^n)` is jointly measurable. -/
theorem measurable_dyadic_slice {Z : Type*} [MeasurableSpace Z] {H : Z → ℝ → ℝ}
    (hslice : ∀ r : ℝ, Measurable fun z : Z => H z r) (n : ℕ) :
    Measurable fun p : Z × ℝ => H p.1 ((⌊(2 : ℝ) ^ n * p.2⌋ : ℝ) / (2 : ℝ) ^ n) := by
  intro B hB
  have hfloor : Measurable fun r : ℝ => ⌊(2 : ℝ) ^ n * r⌋ :=
    Int.measurable_floor.comp (by fun_prop)
  have hset : (fun p : Z × ℝ => H p.1 ((⌊(2 : ℝ) ^ n * p.2⌋ : ℝ) / (2 : ℝ) ^ n)) ⁻¹' B
      = ⋃ k : ℤ, {z : Z | H z ((k : ℝ) / (2 : ℝ) ^ n) ∈ B}
          ×ˢ {r : ℝ | ⌊(2 : ℝ) ^ n * r⌋ = k} := by
    ext p
    simp only [mem_preimage, mem_iUnion, mem_prod, mem_setOf_eq]
    constructor
    · intro hp
      exact ⟨⌊(2 : ℝ) ^ n * p.2⌋, hp, rfl⟩
    · rintro ⟨k, hk, hfl⟩
      rw [hfl]
      exact hk
  rw [hset]
  exact MeasurableSet.iUnion fun k : ℤ =>
    ((hslice ((k : ℝ) / (2 : ℝ) ^ n)) hB).prod (hfloor (measurableSet_singleton k))

/-- **Carathéodory measurability.**  A function on a product that is measurable in
the first variable and continuous in the second is jointly Borel measurable. -/
theorem measurable_of_measurable_continuous_second {Z : Type*} [MeasurableSpace Z]
    {H : Z → ℝ → ℝ} (hslice : ∀ r : ℝ, Measurable fun z : Z => H z r)
    (hcont : ∀ z : Z, Continuous fun r : ℝ => H z r) :
    Measurable fun p : Z × ℝ => H p.1 p.2 := by
  refine measurable_of_tendsto_metrizable
    (f := fun n p => H p.1 ((⌊(2 : ℝ) ^ n * p.2⌋ : ℝ) / (2 : ℝ) ^ n))
    (fun n => measurable_dyadic_slice hslice n) ?_
  rw [tendsto_pi_nhds]
  intro p
  exact ((hcont p.1).tendsto p.2).comp (tendsto_dyadic_slice p.2)

/-- **Joint measurability of a measurable ray family.** -/
theorem measurable_rayFlux_of_measurable_slice {Z : Type*} [MeasurableSpace Z]
    (κ : Z → Measure (ℝ × ℝ)) (hfin : ∀ z, IsFiniteMeasure (κ z))
    (hslice : ∀ r : ℝ, Measurable fun z : Z => rayFlux (κ z) r)
    (h1 : ∀ z r, κ z {p : ℝ × ℝ | p.1 = r} = 0)
    (h2 : ∀ z r, κ z {p : ℝ × ℝ | p.2 = r} = 0) :
    Measurable fun p : Z × ℝ => rayFlux (κ p.1) p.2 :=
  measurable_of_measurable_continuous_second hslice (fun z => by
    haveI := hfin z
    exact continuous_rayFlux (κ z) (h1 z) (h2 z))

/-- **Regularity of the ray surplus of a measurable atomless coupling family.**

If the coupling family is finite, atomless in both coordinates, and has
measurable real-valued total mass on every measurable set, then the ray surplus
`(z, r) ↦ rayFlux (κ z) r` is jointly measurable and, for every label `z`, is
continuous in the ray parameter.  These are precisely the two regularity inputs
of the segment-test measurability theorem for the intrinsic active set. -/
theorem measurable_and_continuous_rayFlux {Z : Type*} [MeasurableSpace Z]
    (κ : Z → Measure (ℝ × ℝ)) (hfin : ∀ z, IsFiniteMeasure (κ z))
    (hκ : ∀ A : Set (ℝ × ℝ), MeasurableSet A → Measurable fun z : Z => (κ z A).toReal)
    (h1 : ∀ z r, κ z {p : ℝ × ℝ | p.1 = r} = 0)
    (h2 : ∀ z r, κ z {p : ℝ × ℝ | p.2 = r} = 0) :
    Measurable (fun p : Z × ℝ => rayFlux (κ p.1) p.2) ∧
      ∀ z : Z, Continuous fun r : ℝ => rayFlux (κ z) r := by
  have hslice : ∀ r : ℝ, Measurable fun z : Z => rayFlux (κ z) r := by
    intro r
    have hA : Measurable fun z : Z => (κ z {p : ℝ × ℝ | p.1 ≤ r}).toReal :=
      hκ {p : ℝ × ℝ | p.1 ≤ r} (measurableSet_Iic.preimage measurable_fst)
    have hB : Measurable fun z : Z => (κ z {p : ℝ × ℝ | p.2 ≤ r}).toReal :=
      hκ {p : ℝ × ℝ | p.2 ≤ r} (measurableSet_Iic.preimage measurable_snd)
    change Measurable fun z : Z =>
      (κ z {p : ℝ × ℝ | p.1 ≤ r}).toReal - (κ z {p : ℝ × ℝ | p.2 ≤ r}).toReal
    exact hA.sub hB
  refine ⟨measurable_rayFlux_of_measurable_slice κ hfin hslice h1 h2, fun z => ?_⟩
  haveI := hfin z
  exact continuous_rayFlux (κ z) (h1 z) (h2 z)

end OTSelector.Reconstruction
end
end
