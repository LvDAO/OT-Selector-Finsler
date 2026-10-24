import OTSelector.Probability.AffineTiltAtomlessness
import OTSelector.Probability.Dirichlet.CavityLaw
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Only countably many perturbations destroy cost-difference atomlessness

On the actual independent source pair, equality of two tilted scores defines a collision
event. Events for distinct tilts intersect only inside the zero-probability base collision
event. The existing countability theorem for almost-disjoint positive-measure sets then
gives a countable exceptional set, without introducing an auxiliary sampling law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S]





/-- For measurable real `h,k` with atomless `h`, the bad slopes of `h + t*k` are countable. -/
theorem countable_nonatomless_affine_tilts
    (μ : Measure S) [IsProbabilityMeasure μ] (h k : S → ℝ)
    (hh : Measurable h) (hk : Measurable k) [NullSingletonClass (μ.map h)] :
    {t : ℝ | ¬NullSingletonClass (μ.map (fun s ↦ h s + t * k s))}.Countable := by
  let E : ℝ → Set (S × S) := fun t ↦
    {q | h q.1 + t * k q.1 = h q.2 + t * k q.2}
  have hmeas t : MeasurableSet (E t) :=
    measurableSet_eq_fun ((hh.add (hk.const_mul t)).comp measurable_fst)
      ((hh.add (hk.const_mul t)).comp measurable_snd)
  have hbase := measure_pair_collision_eq_zero μ h hh
  have hdisj : Pairwise (fun s t ↦ AEDisjoint (μ.prod μ) (E s) (E t)) := by
    intro s t hst
    apply measure_mono_null _ hbase
    intro q hq
    have hs : h q.1 + s * k q.1 = h q.2 + s * k q.2 := hq.1
    have ht : h q.1 + t * k q.1 = h q.2 + t * k q.2 := hq.2
    have hm : (s - t) * (k q.1 - k q.2) = 0 := by nlinarith
    have hkd : k q.1 - k q.2 = 0 :=
      (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hst)
    change h q.1 = h q.2
    rw [sub_eq_zero.mp hkd] at hs
    exact add_right_cancel hs
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun t ↦ (hmeas t).nullMeasurableSet) hdisj
  apply hcount.mono
  intro t ht
  change 0 < (μ.prod μ) (E t)
  apply pos_iff_ne_zero.mpr
  intro hz
  exact ht (nullSingletonClass_map_of_pair_collision_null μ _ (hh.add (hk.const_mul t)) hz)

/-- The actual finite cost family has atomless pair differences outside one countable
set of tilts; the probe may be any measurable paired test. -/
theorem countable_bad_cavity_tilts {ι : Type*} [Fintype ι]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : ι → S → ℝ) (hc : ∀ j, Measurable (c j)) (hg : ∀ j, Measurable (g j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    {t : ℝ | ¬∀ j l, j ≠ l → NullSingletonClass
      (μ.map (fun s ↦ (c j s + t * g j s) - (c l s + t * g l s)))}.Countable := by
  classical
  let E : ι → ι → Set ℝ := fun j l ↦
    {t | j ≠ l ∧ ¬NullSingletonClass
      (μ.map (fun s ↦ (c j s + t * g j s) - (c l s + t * g l s)))}
  have hE (j l : ι) : (E j l).Countable := by
    by_cases hjl : j = l
    · simp [E, hjl]
    · have := hatom j l hjl
      have h := countable_nonatomless_affine_tilts μ
        (fun s ↦ c j s - c l s) (fun s ↦ g j s - g l s)
        ((hc j).sub (hc l)) ((hg j).sub (hg l))
      apply h.mono
      intro t ht
      change ¬NullSingletonClass
        (μ.map (fun s ↦ c j s - c l s + t * (g j s - g l s)))
      have heq : (fun s ↦ c j s - c l s + t * (g j s - g l s)) =
          (fun s ↦ (c j s + t * g j s) - (c l s + t * g l s)) := by
        funext s
        ring
      simpa only [heq] using ht.2
  apply (countable_iUnion fun j ↦ countable_iUnion (hE j)).mono
  intro t ht
  push Not at ht
  obtain ⟨j, l, hjl, hbad⟩ := ht
  exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨l, hjl, hbad⟩⟩

/-- Atomless perturbed pair differences hold on a dense set of actual tilt parameters. -/
theorem dense_good_cavity_tilts {ι : Type*} [Fintype ι]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : ι → S → ℝ) (hc : ∀ j, Measurable (c j)) (hg : ∀ j, Measurable (g j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    Dense {t : ℝ | ∀ j l, j ≠ l → NullSingletonClass
      (μ.map (fun s ↦ (c j s + t * g j s) - (c l s + t * g l s)))} := by
  simpa only [compl_ofPred, not_not] using
    (countable_bad_cavity_tilts μ c g hc hg hatom).dense_compl ℝ

end OTSelector.Probability
