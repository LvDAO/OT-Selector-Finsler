import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
## Lemma skeleton

* **Conditions:** A measurable natural-valued count and measurable nonnegative real energy family; finite sample measure, integrable count-power and count-fiber moment bounds for the energy conclusion.
* **Objects:** Measurable count-selected readout, assembly of fiberwise almost-everywhere facts, and integrated energy bound C times the count-power moment.
* **Proof detail:** Partition the sample space into count fibers, glue measurability/null facts countably, and sum the nonnegative fiber energy bounds.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106

**Relationship to the sources:** Countable disjoint integration, with no independence between the count and the energy.
-/

/-! Integrating genuine nonnegative energy estimates over actual count fibres. -/

open MeasureTheory Set Function

noncomputable section
namespace OTSelector.Reconstruction

/-- A countable measurable family can be evaluated at a measurable actual count. -/
theorem measurable_count_diagonal
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (N : Ω → ℕ) (hN : Measurable N) (f : ℕ → Ω → Y) (hf : ∀ k, Measurable (f k)) :
    Measurable (fun p ↦ f (N p) p) := by
  have hh : Measurable (fun p : Ω × ℕ ↦ f p.2 p.1) :=
    measurable_from_prod_countable_left fun k ↦ hf k
  exact hh.comp (measurable_id.prodMk hN)

/-- Almost-everywhere facts on every actual count fibre hold at the actual count. -/
theorem randomCount_ae_of_restrict
    {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω) (N : Ω → ℕ)
    (A : ℕ → Ω → Prop) (hA : ∀ k, ∀ᵐ p ∂M.restrict {p | N p = k}, A k p) :
    ∀ᵐ p ∂M, A (N p) p := by
  have h := ae_all_iff.mpr fun k ↦ ae_imp_of_ae_restrict (hA k)
  filter_upwards [h] with p hp
  exact hp (N p) rfl

/-- Count-fibre estimates and their actual local integrability imply the complete
random-count estimate. The countable partition supplies global integrability. -/
theorem randomCount_energy_integrable_and_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω) [IsFiniteMeasure M]
    (N : Ω → ℕ) (hN : Measurable N) (e : ℕ → Ω → ℝ)
    (he : ∀ k, Measurable (e k)) (he₀ : ∀ k p, 0 ≤ e k p)
    (C : ℝ) {r : ℝ}
    (hNI : Integrable (fun p ↦ (N p : ℝ) ^ r) M)
    (heI : ∀ k, Integrable (e k) (M.restrict {p | N p = k}))
    (heB : ∀ k, (∫ p, e k p ∂M.restrict {p | N p = k}) ≤
      C * M.real {p | N p = k} * (k : ℝ) ^ r) :
    Measurable (fun p ↦ e (N p) p) ∧
      Integrable (fun p ↦ e (N p) p) M ∧
      (∫ p, e (N p) p ∂M) ≤ C * ∫ p, (N p : ℝ) ^ r ∂M := by
  let S : ℕ → Set Ω := fun k ↦ {p | N p = k}
  let E : Ω → ℝ := fun p ↦ e (N p) p
  let w : Ω → ℝ := fun p ↦ (N p : ℝ) ^ r
  have hS (k) : MeasurableSet (S k) := (measurableSet_singleton k).preimage hN
  have hdis : Pairwise (Disjoint on S) := by
    intro i j hij
    exact disjoint_left.mpr fun p hi hj ↦ hij (hi.symm.trans hj)
  have hall : ⋃ k, S k = univ := by ext p; simp [S]
  have hm : Measurable E := measurable_count_diagonal N hN e he
  have hEa (k) : E =ᵐ[M.restrict (S k)] e k := by
    filter_upwards [ae_restrict_mem (hS k)] with p hp
    change N p = k at hp
    exact congrArg (fun j ↦ e j p) hp
  have hEI (k) : IntegrableOn E (S k) M := (heI k).congr (hEa k).symm
  have hnorm (k) : (∫ p in S k, ‖E p‖ ∂M) = ∫ p in S k, e k p ∂M := by
    apply integral_congr_ae
    filter_upwards [hEa k] with p hp
    rw [hp, Real.norm_eq_abs, abs_of_nonneg (he₀ k p)]
  have hw (k) : (∫ p in S k, w p ∂M) = M.real (S k) * (k : ℝ) ^ r := by
    calc
      _ = ∫ _ in S k, (k : ℝ) ^ r ∂M := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (hS k)] with p hp
        change N p = k at hp
        simp only [w, hp]
      _ = _ := by simp [measureReal_def]
  have hwI : IntegrableOn w (⋃ k, S k) M := by simpa [hall] using hNI
  have hws := (hasSum_integral_iUnion hS hdis hwI).summable
  have hbound (k) : (∫ p in S k, ‖E p‖ ∂M) ≤ C * ∫ p in S k, w p ∂M := by
    rw [hnorm, hw]
    simpa only [S, mul_assoc] using heB k
  have hsum : Summable (fun k ↦ ∫ p in S k, ‖E p‖ ∂M) :=
    .of_nonneg_of_le (fun k ↦ integral_nonneg fun p ↦ norm_nonneg _) hbound (hws.mul_left C)
  have hEU := integrableOn_iUnion_of_summable_integral_norm hEI hsum
  have hE : Integrable E M := by simpa [hall] using hEU
  refine ⟨hm, hE, ?_⟩
  have hb (k) : (∫ p in S k, E p ∂M) ≤ C * ∫ p in S k, w p ∂M := by
    rw [integral_congr_ae (hEa k), hw]
    simpa only [S, mul_assoc] using heB k
  have ht := ((hasSum_integral_iUnion hS hdis hEU).summable).tsum_le_tsum hb (hws.mul_left C)
  rw [← integral_iUnion hS hdis hEU, tsum_mul_left, ← integral_iUnion hS hdis hwI] at ht
  simpa only [hall, setIntegral_univ] using ht

end OTSelector.Reconstruction
