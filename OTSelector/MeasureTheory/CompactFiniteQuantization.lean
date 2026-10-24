import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
## Lemma skeleton

* **Conditions:** A compact carrier in a metric space and a positive approximation radius, with measurable open sets; a default value is supplied, or zero in the seminormed version.
* **Objects:** A measurable finite-range approximation taking values in the compact carrier plus a single default point and approximating every carrier point within the radius.
* **Proof detail:** Cover the compact set by finitely many small open balls. Select the first ball center on disjoint measurable pieces and use the default off the cover.

## Mathematical sources

* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html
* D. H. Fremlin, *Measure Theory, Volume 4, Appendix*, Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
  https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32

**Relationship to the sources:** Elementary finite-net quantization and measurable first-index construction. No transport optimizer or quadratic cost theorem is used.
-/

/-! Finite measurable grids on arbitrary compact metric carriers. -/
open Set Metric
noncomputable section
namespace OTSelector.Reconstruction

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

private lemma exists_finite_ball_step (s : Finset E) (x₀ : E) (h : ℝ) :
    ∃ T : E → E, Measurable T ∧ (∀ x, T x = x₀ ∨ T x ∈ s) ∧
      ∀ x, (∃ a ∈ s, x ∈ ball a h) → dist (T x) x < h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ ↦ x₀, measurable_const, fun _ ↦ Or.inl rfl, ?_⟩
    simp
  | @insert a s ha ih =>
    obtain ⟨T, hT, hval, hnear⟩ := ih
    let T' : E → E := fun x ↦ if x ∈ ball a h then a else T x
    refine ⟨T', Measurable.ite isOpen_ball.measurableSet measurable_const hT, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ ball a h
      · right
        change (if x ∈ ball a h then a else T x) ∈ insert a s
        rw [ite_eq_left hx]
        exact Finset.mem_insert_self a s
      · change (if x ∈ ball a h then a else T x) = x₀ ∨
          (if x ∈ ball a h then a else T x) ∈ insert a s
        rw [ite_eq_right hx]
        exact (hval x).imp_right (fun hx ↦ Finset.mem_insert_of_mem hx)
    · intro x hx
      by_cases hxa : x ∈ ball a h
      · change dist (if x ∈ ball a h then a else T x) x < h
        rw [ite_eq_left hxa]
        simpa only [dist_comm] using Metric.mem_ball.mp hxa
      · change dist (if x ∈ ball a h then a else T x) x < h
        rw [ite_eq_right hxa]
        apply hnear x
        obtain ⟨b, hb, hxb⟩ := hx
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (hxa hxb).elim
        · exact ⟨b, hb, hxb⟩

/-- A compact carrier admits a measurable finite grid at every positive spatial
resolution; every grid value is an original carrier node or the chosen fallback. -/
theorem exists_compact_measurable_finiteRange_grid {K : Set E} (hK : IsCompact K)
    (x₀ : E) {h : ℝ} (hh : 0 < h) :
    ∃ T : E → E, Measurable T ∧ (Set.range T).Finite ∧
      Set.range T ⊆ insert x₀ K ∧ ∀ x ∈ K, dist (T x) x < h := by
  classical
  obtain ⟨s, hsK, hsfin, hcover⟩ := hK.finite_cover_balls hh
  obtain ⟨T, hT, hval, hnear⟩ := exists_finite_ball_step hsfin.toFinset x₀ h
  have hfinite : (Set.range T).Finite := by
    apply (hsfin.insert x₀).subset
    rintro _ ⟨x, rfl⟩
    rcases hval x with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hsfin.mem_toFinset.mp hx)
  refine ⟨T, hT, hfinite, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rcases hval x with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hsK (hsfin.mem_toFinset.mp hx))
  · intro x hx
    apply hnear x
    obtain ⟨a, has, hxa⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact ⟨a, hsfin.mem_toFinset.mpr has, hxa⟩


/-- A compact normed carrier has a measurable finite grid with actual norm
error at most the requested resolution, using only original nodes and zero. -/
theorem exists_compact_measurable_finiteRange_norm_grid
    {F : Type*} [SeminormedAddCommGroup F] [MeasurableSpace F] [OpensMeasurableSpace F]
    {K : Set F} (hK : IsCompact K) {h : ℝ} (hh : 0 < h) :
    ∃ T : F → F, Measurable T ∧ (Set.range T).Finite ∧
      Set.range T ⊆ K ∪ {0} ∧ ∀ x ∈ K, ‖T x-x‖ ≤ h := by
  obtain ⟨T, hT, hfin, hnodes, hnear⟩ :=
    exists_compact_measurable_finiteRange_grid hK 0 hh
  refine ⟨T, hT, hfin, ?_, fun x hx ↦ ?_⟩
  · simpa only [Set.union_singleton] using hnodes
  · simpa only [dist_eq_norm] using (hnear x hx).le

end OTSelector.Reconstruction
