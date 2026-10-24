import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Tactic.NormNum

/-!
## Lemma skeleton

* **Conditions:** A countable family of complete real Banach-valued L2 functions with nonnegative summable real norm bounds.
* **Objects:** Pointwise sum in L2, its norm bound, and almost-everywhere summability of the norm series.
* **Proof detail:** Apply Minkowski to finite partial sums, sum the nonnegative norms to obtain almost-everywhere absolute convergence, then pass to the complete L2 limit.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7B, Theorem 7.20 and proof, pp. 204–205; Theorem 7.24, p. 205.
  https://measure.axler.net/MIRA.pdf#page=219
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.14, p. 199 (Minkowski).
  https://measure.axler.net/MIRA.pdf#page=214
* D. H. Fremlin, *Measure Theory, Volume 2*, Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46

**Relationship to the sources:** Banach-valued/countably indexed version of the absolute-series proof of Lp completeness.
-/

/-! Actual countable traffic sums from summable levelwise L2 bounds. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Probability

/-- Summable deterministic bounds for the actual levelwise L2 norms give
L2 integrability of the literal pointwise countable sum, its norm bound and
almost sure absolute convergence. No independence is assumed. -/
theorem memLp_tsum_of_summable_level_bound
    {Ω I V : Type*} [MeasurableSpace Ω] [Countable I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Measure Ω) (f : I → Ω → V) (hf : ∀ i, MemLp (f i) 2 P)
    (B : I → ℝ) (hB : Summable B) (hB₀ : ∀ i, 0 ≤ B i)
    (hbound : ∀ i, eLpNorm (f i) 2 P ≤ ENNReal.ofReal (B i)) :
    MemLp (fun x ↦ ∑' i, f i x) 2 P ∧
      (eLpNorm (fun x ↦ ∑' i, f i x) 2 P).toReal ≤ ∑' i, B i ∧
      ∀ᵐ x ∂P, Summable (fun i ↦ ‖f i x‖) := by
  let _ : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let F : I → Lp V 2 P := fun i ↦ (hf i).toLp (f i)
  have hnorm (i : I) : ‖F i‖ ≤ B i := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (hB₀ i) (hbound i)
  have hsum : Summable (fun i ↦ ‖F i‖) :=
    hB.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hnorm
  have hfinite : ∑' i, ‖F i‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hsum
  have hpoint : (fun x ↦ (∑' i, F i) x) =ᵐ[P] fun x ↦ ∑' i, f i x := by
    filter_upwards [Lp.coeFn_tsum hfinite,
      ae_all_iff.mpr (fun i ↦ (hf i).coeFn_toLp)] with x hx htoLp
    exact hx.trans (tsum_congr fun i ↦ htoLp i)
  have hmem : MemLp (fun x ↦ ∑' i, f i x) 2 P :=
    MemLp.ae_eq hpoint (Lp.memLp (∑' i, F i))
  refine ⟨hmem, ?_, ?_⟩
  · calc
      (eLpNorm (fun x ↦ ∑' i, f i x) 2 P).toReal = ‖∑' i, F i‖ := by
        rw [← eLpNorm_congr_ae hpoint]
        exact (Lp.norm_def _).symm
      _ ≤ ∑' i, B i := tsum_of_norm_bounded hB.hasSum hnorm
  · have heq (i : I) : eLpNorm (F i) 2 P = eLpNorm (f i) 2 P :=
      eLpNorm_congr_ae (hf i).coeFn_toLp
    have hfinite' : ∑' i, eLpNorm (f i) 2 P ≠ ∞ := by
      simpa only [Lp.enorm_def, heq] using hfinite
    exact summable_norm_of_tsum_eLpNorm_ne_top (by norm_num)
      (fun i ↦ (hf i).aestronglyMeasurable) hfinite'

end OTSelector.Probability
