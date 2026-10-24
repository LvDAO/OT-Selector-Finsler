import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
## Lemma skeleton

* **Conditions:** A finite scalar Borel measure with null singletons and a compact set of clock locations; requested strip mass epsilon is positive.
* **Objects:** Continuous unnormalized prefix-mass function and a finite collection of intervals covering the compact set with mass at most epsilon each.
* **Proof detail:** Continuity from above/below and null singleton jumps give prefix continuity. Around each clock choose a sufficiently small prefix-mass increment and use a finite compact subcover.

## Mathematical sources

* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.2, Theorem 1.2.1(iii)–(v), p. 11.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=19
* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html

**Relationship to the sources:** Finite-measure version of the distribution-function jump formula followed by compactness. No probability normalization or density is needed.
-/

/-! Atomless original clock laws admit finite meshes of arbitrarily small strip mass. -/
open Set MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Atomlessness makes the original finite-measure prefix mass continuous. -/
theorem continuous_clockPrefixMass (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : Continuous (fun c ↦ μ.real (Iic c)) := by
  rw [continuous_iff_continuousAt]
  intro c
  have hI : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Iic (c + 1)) μ :=
    (integrable_const (1 : ℝ)).integrableOn
  have hc := hI.continuousOn_Iic_primitive_Iic c (by simp)
  have hN : Iic (c + 1) ∈ 𝓝 c := Iic_mem_nhds (by linarith)
  simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ] using hc.continuousAt hN

/-- Every compact clock carrier has a finite bracketing mesh whose strips have
arbitrarily small mass under the same original atomless clock law. -/
theorem exists_finite_clockPrefixMesh (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : Finset ℝ) (lo hi : ℝ → ℝ),
      (∀ j ∈ t, lo j ≤ hi j) ∧
      (∀ c ∈ K, ∃ j ∈ t, lo j ≤ c ∧ c ≤ hi j) ∧
      (∀ j ∈ t, μ.real (Ioc (lo j) (hi j)) ≤ ε) := by
  have hcont := continuous_clockPrefixMass μ
  have hlocal (c : ℝ) : ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, dist x c < δ → |μ.real (Iic x) - μ.real (Iic c)| < ε / 2 := by
    exact (Metric.continuousAt_iff.mp (hcont.continuousAt : ContinuousAt _ c))
      (ε / 2) (by positivity)
  choose δ hδ hδbound using hlocal
  let lo : ℝ → ℝ := fun c ↦ c - δ c / 2
  let hi : ℝ → ℝ := fun c ↦ c + δ c / 2
  have horder (c : ℝ) : lo c ≤ hi c := by dsimp [lo, hi]; linarith [hδ c]
  have hcl (c : ℝ) : lo c < c := by dsimp [lo]; linarith [hδ c]
  have hch (c : ℝ) : c < hi c := by dsimp [hi]; linarith [hδ c]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : ℝ ↦ Ioo (lo c) (hi c))
    (fun _ ↦ isOpen_Ioo) (fun c _ ↦ mem_iUnion.mpr ⟨c, hcl c, hch c⟩)
  refine ⟨t, lo, hi, fun j _ ↦ horder j, ?_, ?_⟩
  · intro c hc
    obtain ⟨j, hj, hcj⟩ := mem_iUnion₂.mp (ht hc)
    exact ⟨j, hj, hcj.1.le, hcj.2.le⟩
  · intro j hj
    have hl := hδbound j (lo j) (by
      rw [Real.dist_eq, abs_of_nonpos (by dsimp [lo]; linarith [hδ j])]
      dsimp [lo]
      linarith [hδ j])
    have hh := hδbound j (hi j) (by
      rw [Real.dist_eq, abs_of_nonneg (by dsimp [hi]; linarith [hδ j])]
      dsimp [hi]
      linarith [hδ j])
    have heq : μ.real (Iic (hi j)) - μ.real (Iic (lo j)) =
        μ.real (Ioc (lo j) (hi j)) := by
      rw [← Iic_sdiff_Iic]
      exact (measureReal_sdiff (Iic_subset_Iic.mpr (horder j)) measurableSet_Iic).symm
    rw [← heq]
    linarith [le_abs_self (μ.real (Iic (hi j)) - μ.real (Iic j)),
      neg_le_abs (μ.real (Iic (lo j)) - μ.real (Iic j))]

end OTSelector.Probability
