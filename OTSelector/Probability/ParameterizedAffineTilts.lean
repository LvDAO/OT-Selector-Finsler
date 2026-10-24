import OTSelector.Probability.AffineTiltAtomlessness

/-!
Conditions: Two probability spaces, jointly measurable affine coefficients and a.e. atomlessness of the base observable; the cavity corollary uses only finitely many labels and their pairwise differences.

Objects: A deterministic countable set of slopes outside which the parameter-conditioned affine image law is atomless almost everywhere, simultaneously for the finite label pairs.

Proof detail: For each slope form its independent-pair collision event in the parameter/source/source product. Distinct slopes intersect only inside the zero base-collision event; countability of positive-mass a.e. disjoint sets and Fubini give the conclusion.

References: Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38; mathlib contributors: Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean, lines 282–301, Measure.countable_meas_pos_of_disjoint_iUnion₀.
Relation: The affine-collision algebra and global exceptional-slope construction are local. The general s-finite disjoint-positive-set theorem supplies precisely the countability step; no uncountable intersection of a.e. parameter sets is taken.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityTiltParameterized.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityTiltParameterized`; the selected original proof blocks follow. -/
section

/-!
# A common countable exceptional tilt set for random target environments

Collision events live on the actual environment and two independent source copies.
Their pairwise intersections lie in the null base collision event. Countability of
positive-measure almost-disjoint events therefore gives deterministic good tilts which
work almost surely in the environment, rather than environment-dependent tilt choices.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

/-- Almost surely atomless conditional base laws admit only countably many globally bad tilts. -/
theorem countable_nonatomless_parameterized_affine_tilts
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (h k : V → S → ℝ)
    (hh : Measurable (Function.uncurry h)) (hk : Measurable (Function.uncurry k))
    (hatom : ∀ᵐ v ∂ρ, NullSingletonClass (μ.map (h v))) :
    {t : ℝ | ¬∀ᵐ v ∂ρ, NullSingletonClass (μ.map (fun s ↦ h v s + t * k v s))}.Countable := by
  let E : ℝ → Set (V × (S × S)) := fun t ↦
    {q | h q.1 q.2.1 + t * k q.1 q.2.1 = h q.1 q.2.2 + t * k q.1 q.2.2}
  have hm₁ : Measurable (fun q : V × (S × S) ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm₂ : Measurable (fun q : V × (S × S) ↦ (q.1, q.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hmeas t : MeasurableSet (E t) :=
    measurableSet_eq_fun ((hh.comp hm₁).add ((hk.comp hm₁).const_mul t))
      ((hh.comp hm₂).add ((hk.comp hm₂).const_mul t))
  have hbase : (ρ.prod (μ.prod μ)) (E 0) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    apply (Measure.ae_prod_iff_ae_ae (hmeas 0).compl).mpr
    filter_upwards [hatom] with v hv
    have : NullSingletonClass (μ.map (h v)) := hv
    have hz := measure_pair_collision_eq_zero μ (h v)
      (hh.comp (measurable_const.prodMk measurable_id))
    simpa only [E, zero_mul, add_zero, mem_ofPred_eq] using
      (measure_eq_zero_iff_ae_notMem.mp hz)
  have hdisj : Pairwise (fun s t ↦ AEDisjoint (ρ.prod (μ.prod μ)) (E s) (E t)) := by
    intro s t hst
    apply measure_mono_null _ hbase
    intro q hq
    have hs : h q.1 q.2.1 + s * k q.1 q.2.1 = h q.1 q.2.2 + s * k q.1 q.2.2 := hq.1
    have ht : h q.1 q.2.1 + t * k q.1 q.2.1 = h q.1 q.2.2 + t * k q.1 q.2.2 := hq.2
    have hm : (s - t) * (k q.1 q.2.1 - k q.1 q.2.2) = 0 := by nlinarith
    have hkd : k q.1 q.2.1 - k q.1 q.2.2 = 0 :=
      (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hst)
    change h q.1 q.2.1 + 0 * k q.1 q.2.1 = h q.1 q.2.2 + 0 * k q.1 q.2.2
    simp only [zero_mul, add_zero]
    rw [sub_eq_zero.mp hkd] at hs
    exact add_right_cancel hs
  apply (Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun t ↦ (hmeas t).nullMeasurableSet) hdisj).mono
  intro t hbad
  change 0 < (ρ.prod (μ.prod μ)) (E t)
  apply pos_iff_ne_zero.mpr
  intro hz
  apply hbad
  have ha := (Measure.ae_prod_iff_ae_ae (hmeas t).compl).mp
    (measure_eq_zero_iff_ae_notMem.mp hz)
  filter_upwards [ha] with v hv
  apply nullSingletonClass_map_of_pair_collision_null μ _
    ((hh.comp (measurable_const.prodMk measurable_id)).add
      ((hk.comp (measurable_const.prodMk measurable_id)).const_mul t))
  exact measure_eq_zero_iff_ae_notMem.mpr hv

/-- Finite target labels share one deterministic countable set of bad tilts. -/
theorem countable_bad_parameterized_cavity_tilts {ι : Type*} [Fintype ι]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : ι → V → S → ℝ)
    (hc : ∀ j, Measurable (Function.uncurry (c j)))
    (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c j v s - c l v s))) :
    {t : ℝ | ¬∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
      (μ.map (fun s ↦ (c j v s + t * g j v s) - (c l v s + t * g l v s)))}.Countable := by
  classical
  let E : ι → ι → Set ℝ := fun j l ↦
    {t | j ≠ l ∧ ¬∀ᵐ v ∂ρ, NullSingletonClass
      (μ.map (fun s ↦ (c j v s + t * g j v s) - (c l v s + t * g l v s)))}
  have hE j l : (E j l).Countable := by
    by_cases hjl : j = l
    · simp [E, hjl]
    · have h := countable_nonatomless_parameterized_affine_tilts μ ρ
        (fun v s ↦ c j v s - c l v s) (fun v s ↦ g j v s - g l v s)
        ((hc j).sub (hc l)) ((hg j).sub (hg l))
        (hatom.mono fun _ hv ↦ hv j l hjl)
      apply h.mono
      intro t ht
      have heq (v : V) : (fun s ↦ c j v s - c l v s + t * (g j v s - g l v s)) =
          (fun s ↦ (c j v s + t * g j v s) - (c l v s + t * g l v s)) := by
        funext s
        ring
      change ¬∀ᵐ v ∂ρ, NullSingletonClass
        (μ.map (fun s ↦ c j v s - c l v s + t * (g j v s - g l v s)))
      simpa only [heq] using ht.2
  apply (countable_iUnion fun j ↦ countable_iUnion (hE j)).mono
  intro t ht
  by_contra hnot
  apply ht
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro l
  by_cases hjl : j = l
  · simp [hjl]
  · have hgood : ∀ᵐ v ∂ρ, NullSingletonClass
        (μ.map (fun s ↦ (c j v s + t * g j v s) - (c l v s + t * g l v s))) := by
      by_contra hb
      exact hnot (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨l, hjl, hb⟩⟩)
    exact hgood.mono fun _ hv _ ↦ hv

end OTSelector.Probability

end
end
