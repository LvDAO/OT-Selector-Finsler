import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional real normed spaces; SFinite frequency and angular measures. Angular singleton-nullness is enough for the first Tonelli result; Haar angular measures are singleton-null when dimension>1. The common reflected frame construction uses an inner product and dimension>2.
* **Objects:** Generic directions and a common orthonormal frame whose nonzero normal lines carry zero mass for every measure in a countable frequency family.
* **Proof detail:** For a fixed nonzero frequency at most two directions are incident. Apply Tonelli to the measurable incidence and intersect countably many conull sets. For one common line reflection, bad parameters lie in span(axis,frequency) union axis-perpendicular, two proper subspaces; choose a good parameter and reflect the original orthonormal frame.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Corollary 252F, p. 24.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=24
* D. H. Fremlin, *Measure Theory, Volume 2*, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19

**Relationship to the sources:** Locally derived incidence/Tonelli and reflection argument. Proper subspaces are Haar-null by linear volume facts; angular nullity follows from the radial-cone definition, valid also for non-Euclidean norms in the first half. No spectral representation or random-orthogonal-matrix theorem is asserted.
-/

/-!
# Generic normal directions for finite frequency measures

The normal line of almost every direction carries no nonzero mass of any fixed
sigma-finite frequency measure.  This is the geometric Tonelli step in the
stationary-current boundary argument; no spectral representation of a random
field is asserted here.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped Pointwise

namespace OTSelector.Probability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Frequencies on the real normal line, excluding the zero frequency. -/
def normalLineAwayZero (n : sphere (0 : E) 1) : Set E :=
  (ℝ ∙ (n : E) : Set E) \ {0}

/-- A proper linear subspace meets the unit sphere in an angular null set. -/
theorem toSphere_submodule_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Submodule ℝ E) (hS : S ≠ ⊤) :
    μ.toSphere {n | (n : E) ∈ S} = 0 := by
  have hs : MeasurableSet {n : sphere (0 : E) 1 | (n : E) ∈ S} :=
    (Submodule.closed_of_finiteDimensional S).measurableSet.preimage measurable_subtype_coe
  rw [μ.toSphere_apply' (s := {n : sphere (0 : E) 1 | (n : E) ∈ S}) hs]
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' {n : sphere (0 : E) 1 | (n : E) ∈ S}) ⊆
      (S : Set E) := by
    rintro x ⟨a, ha, y, hy, rfl⟩
    rcases hy with ⟨n, hn, rfl⟩
    exact S.smul_mem a hn
  rw [measure_mono_null hcone (Measure.addHaar_submodule μ S hS), mul_zero]

/-- In dimension greater than one the angular measure of additive Haar measure
has no point masses. -/
theorem nullSingletonClass_toSphere_of_one_lt_finrank
    (μ : Measure E) [μ.IsAddHaarMeasure] (hdim : 1 < Module.finrank ℝ E) :
    NullSingletonClass μ.toSphere := by
  constructor
  intro n
  have hn : ‖(n : E)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using n.property
  have hn0 : (n : E) ≠ 0 := by
    intro h
    simp [h] at hn
  have hproper : ℝ ∙ (n : E) ≠ ⊤ := by
    intro h
    have hd := finrank_span_singleton (K := ℝ) hn0
    rw [h, finrank_top] at hd
    omega
  exact measure_mono_null (by
    intro m hm
    have hmn : m = n := by simpa using hm
    subst m
    exact Submodule.mem_span_singleton_self _) (toSphere_submodule_eq_zero μ _ hproper)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The normal-line incidence has a continuous-equation description, including
both orientations of the same line. -/
theorem mem_normalLineAwayZero_iff (n : sphere (0 : E) 1) (k : E) :
    k ∈ normalLineAwayZero n ↔
      k ≠ 0 ∧ (‖k‖ • (n : E) = k ∨ ‖k‖ • (n : E) = -k) := by
  have hn : ‖(n : E)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using n.property
  constructor
  · rintro ⟨hk, hk0⟩
    refine ⟨by simpa using hk0, ?_⟩
    rcases Submodule.mem_span_singleton.mp hk with ⟨a, rfl⟩
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs]
    rcases le_total 0 a with ha | ha
    · exact Or.inl (by rw [abs_of_nonneg ha])
    · exact Or.inr (by rw [abs_of_nonpos ha, neg_smul])
  · rintro ⟨hk0, hk | hk⟩
    · exact ⟨Submodule.mem_span_singleton.mpr ⟨‖k‖, hk⟩, by simpa using hk0⟩
    · refine ⟨Submodule.mem_span_singleton.mpr ⟨-‖k‖, ?_⟩, by simpa using hk0⟩
      rw [neg_smul, hk, neg_neg]

/-- The frequency/normal incidence is measurable, so Tonelli applies without
any regularity assumption on the frequency measure. -/
theorem measurableSet_normalLineAwayZero_incidence :
    MeasurableSet {p : sphere (0 : E) 1 × E | p.2 ∈ normalLineAwayZero p.1} := by
  simp_rw [mem_normalLineAwayZero_iff]
  exact (measurable_snd (measurableSet_singleton (0 : E))).compl.inter
    ((measurableSet_eq_fun (by fun_prop) measurable_snd).union
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)))

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- For a fixed nonzero frequency there are at most two unit normal directions.
Consequently any angular measure without atoms gives those directions mass zero. -/
theorem measure_normalLineAwayZero_directions_eq_zero
    (σ : Measure (sphere (0 : E) 1)) [NullSingletonClass σ] (k : E) :
    σ {n | k ∈ normalLineAwayZero n} = 0 := by
  by_cases hk : k = 0
  · simp [hk, normalLineAwayZero]
  have hnorm : ‖k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
  have hsub (v : E) : Set.Subsingleton {n : sphere (0 : E) 1 | ‖k‖ • (n : E) = v} := by
    intro n hn m hm
    apply Subtype.ext
    have h := congrArg (fun x : E => ‖k‖⁻¹ • x) (hn.trans hm.symm)
    simpa only [smul_smul, inv_mul_cancel₀ hnorm, one_smul] using h
  have hnull := measure_union_null ((hsub k).measure_zero σ) ((hsub (-k)).measure_zero σ)
  exact measure_mono_null (fun n hn => (mem_normalLineAwayZero_iff n k).mp hn |>.2) hnull

/-- A sigma-finite frequency measure charges no nonzero normal line for almost
every atomless angular direction.  This applies in particular to finite scalar
trace measures of matrix spectral measures, once those have been constructed. -/
theorem ae_measure_normalLineAwayZero_eq_zero
    (σ : Measure (sphere (0 : E) 1)) [SFinite σ] [NullSingletonClass σ]
    (ν : Measure E) [SFinite ν] :
    ∀ᵐ n ∂σ, ν (normalLineAwayZero n) = 0 := by
  have hfirst : ∀ᵐ k ∂ν, ∀ᵐ n ∂σ, k ∉ normalLineAwayZero n := by
    filter_upwards [] with k
    exact ae_iff.mpr (by simpa only [not_not] using
      measure_normalLineAwayZero_directions_eq_zero σ k)
  have hmeas : MeasurableSet {p : E × sphere (0 : E) 1 |
      p.1 ∉ normalLineAwayZero p.2} :=
    (measurable_swap measurableSet_normalLineAwayZero_incidence).compl
  filter_upwards [(Measure.ae_ae_comm hmeas).mp hfirst] with n hn
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hn

/-- The angular measure induced by Haar measure admits a common full-measure
set of good directions for any countable family of frequency measures. -/
theorem ae_toSphere_all_measure_normalLineAwayZero_eq_zero
    {ι : Type*} [Countable ι] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : 1 < Module.finrank ℝ E) (ν : ι → Measure E) [∀ i, SFinite (ν i)] :
    ∀ᵐ n ∂μ.toSphere, ∀ i, ν i (normalLineAwayZero n) = 0 := by
  let := nullSingletonClass_toSphere_of_one_lt_finrank μ hdim
  exact ae_all_iff.mpr (fun i => ae_measure_normalLineAwayZero_eq_zero μ.toSphere (ν i))

/-- A deterministic common normal direction exists for every countable family
of sigma-finite frequency measures in dimension greater than one.  This selects
one direction; it does not assert that a whole orthogonal frame has been selected. -/
theorem exists_all_measure_normalLineAwayZero_eq_zero
    {ι : Type*} [Countable ι] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : 1 < Module.finrank ℝ E) (ν : ι → Measure E) [∀ i, SFinite (ν i)] :
    ∃ n : sphere (0 : E) 1, ∀ i, ν i (normalLineAwayZero n) = 0 := by
  have hμ : μ.toSphere ≠ 0 := by
    intro hzero
    have := μ.toSphere_eq_zero_iff_finrank.mp hzero
    omega
  have := ae_neBot.mpr hμ
  exact (ae_toSphere_all_measure_normalLineAwayZero_eq_zero μ hdim ν).exists

section Reflection

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- Reflect a unit direction in the line of another unit direction.  The
underlying map is an actual orthogonal linear isometry. -/
def reflectedUnitDirection (v e : sphere (0 : F) 1) : sphere (0 : F) 1 :=
  ⟨(ℝ ∙ (v : F)).reflection (e : F), by
    simpa only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] using e.property⟩

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Line reflections depend continuously on their unit normal. -/
theorem continuous_reflectedUnitDirection (e : sphere (0 : F) 1) :
    Continuous (fun v : sphere (0 : F) 1 => reflectedUnitDirection v e) := by
  apply Continuous.subtype_mk
  have hformula (v : sphere (0 : F) 1) :
      (reflectedUnitDirection v e : F) = 2 • (inner ℝ (v : F) (e : F)) • (v : F) - e := by
    have hv : ‖(v : F)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using v.property
    simp [reflectedUnitDirection, Submodule.reflection_singleton_apply, hv]
  change Continuous (fun v : sphere (0 : F) 1 => (reflectedUnitDirection v e : F))
  simp_rw [hformula]
  fun_prop

/-- For a fixed axis and a fixed frequency, the reflection parameters sending
the axis onto that frequency line lie in two proper linear subspaces. -/
theorem measure_reflected_normalLineAwayZero_parameters_eq_zero
    (μ : Measure F) [μ.IsAddHaarMeasure] (hdim : 2 < Module.finrank ℝ F)
    (e : sphere (0 : F) 1) (k : F) :
    μ.toSphere {v | k ∈ normalLineAwayZero (reflectedUnitDirection v e)} = 0 := by
  classical
  let S : Submodule ℝ F := Submodule.span ℝ {(e : F), k}
  let T : Submodule ℝ F := (ℝ ∙ (e : F))ᗮ
  have he : ‖(e : F)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using e.property
  have hS : S ≠ ⊤ := by
    have hs : Module.finrank ℝ S ≤ 2 := by
      have h := finrank_span_finset_le_card (R := ℝ) ({(e : F), k} : Finset F)
      have hpair : (({(e : F), k} : Finset F) : Set F) = {(e : F), k} := by
        ext x
        simp
      rw [Set.finrank, hpair] at h
      exact h.trans (by simpa using Finset.card_insert_le (e : F) ({k} : Finset F))
    intro h
    rw [h, finrank_top] at hs
    omega
  have hT : T ≠ ⊤ := by
    intro h
    have het : (e : F) ∈ T := by rw [h]; trivial
    have hz : inner ℝ (e : F) (e : F) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp het
    have he0 : (e : F) = 0 := inner_self_eq_zero.mp hz
    simp [he0] at he
  refine measure_mono_null (t := {v : sphere (0 : F) 1 | (v : F) ∈ S} ∪
    {v : sphere (0 : F) 1 | (v : F) ∈ T}) ?_
    (measure_union_null (toSphere_submodule_eq_zero μ S hS)
      (toSphere_submodule_eq_zero μ T hT))
  intro v hv
  by_cases hinner : inner ℝ (v : F) (e : F) = 0
  · exact Or.inr (Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hinner)
  · left
    have heS : (e : F) ∈ S := Submodule.subset_span (by simp)
    have hkS : k ∈ S := Submodule.subset_span (by simp)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv.1
    have hk0 : k ≠ 0 := by simpa using hv.2
    have ha0 : a ≠ 0 := by
      intro h
      simp [h] at ha
      exact hk0 ha.symm
    have hrS : (reflectedUnitDirection v e : F) ∈ S := by
      have hak : a • (reflectedUnitDirection v e : F) ∈ S := ha.symm ▸ hkS
      have h := S.smul_mem a⁻¹ hak
      simpa only [smul_smul, inv_mul_cancel₀ ha0, one_smul] using h
    have hvnorm : ‖(v : F)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using v.property
    have hdecomp : (2 * inner ℝ (v : F) (e : F)) • (v : F) =
        (reflectedUnitDirection v e : F) + e := by
      simp [reflectedUnitDirection, Submodule.reflection_singleton_apply, hvnorm,
        two_mul, two_smul, add_smul]
    have hcoef : 2 * inner ℝ (v : F) (e : F) ≠ 0 := mul_ne_zero two_ne_zero hinner
    have h := S.smul_mem (2 * inner ℝ (v : F) (e : F))⁻¹
      (hdecomp.symm ▸ S.add_mem hrS heS)
    change (v : F) ∈ S
    simpa only [smul_smul, inv_mul_cancel₀ hcoef, one_smul] using h

/-- Almost every single line reflection gives an axis good for a prescribed
sigma-finite frequency measure. -/
theorem ae_toSphere_measure_reflected_normalLineAwayZero_eq_zero
    (μ : Measure F) [μ.IsAddHaarMeasure] (hdim : 2 < Module.finrank ℝ F)
    (e : sphere (0 : F) 1) (ν : Measure F) [SFinite ν] :
    ∀ᵐ v ∂μ.toSphere, ν (normalLineAwayZero (reflectedUnitDirection v e)) = 0 := by
  have hfirst : ∀ᵐ k ∂ν, ∀ᵐ v ∂μ.toSphere,
      k ∉ normalLineAwayZero (reflectedUnitDirection v e) := by
    filter_upwards [] with k
    exact ae_iff.mpr (by simpa only [not_not] using
      measure_reflected_normalLineAwayZero_parameters_eq_zero μ hdim e k)
  have hmeas : MeasurableSet {p : F × sphere (0 : F) 1 |
      p.1 ∉ normalLineAwayZero (reflectedUnitDirection p.2 e)} := by
    exact (measurableSet_normalLineAwayZero_incidence.preimage
      (((continuous_reflectedUnitDirection e).comp continuous_snd).measurable.prodMk
        measurable_fst)).compl
  filter_upwards [(Measure.ae_ae_comm hmeas).mp hfirst] with v hv
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hv

/-- One full angular-measure set works simultaneously for every axis in a
countable family and every measure in a countable frequency family. -/
theorem ae_toSphere_all_measure_reflected_normalLineAwayZero_eq_zero
    {ι κ : Type*} [Countable ι] [Countable κ]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hdim : 2 < Module.finrank ℝ F)
    (e : ι → sphere (0 : F) 1) (ν : κ → Measure F) [∀ j, SFinite (ν j)] :
    ∀ᵐ v ∂μ.toSphere, ∀ i j,
      ν j (normalLineAwayZero (reflectedUnitDirection v (e i))) = 0 := by
  exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
    ae_toSphere_measure_reflected_normalLineAwayZero_eq_zero μ hdim (e i) (ν j)))

/-- In dimension greater than two one deterministic orthogonal map makes all
prescribed countably many unit axes good for all countably many frequency
measures.  The map is a single genuine line reflection, not an assumed random
orthogonal matrix or an assumed distribution on axes. -/
theorem exists_linearIsometryEquiv_all_measure_normalLines_eq_zero
    {ι κ : Type*} [Countable ι] [Countable κ]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hdim : 2 < Module.finrank ℝ F)
    (e : ι → sphere (0 : F) 1) (ν : κ → Measure F) [∀ j, SFinite (ν j)] :
    ∃ O : F ≃ₗᵢ[ℝ] F, ∀ i j,
      ν j ((ℝ ∙ O (e i) : Set F) \ {0}) = 0 := by
  have hμ : μ.toSphere ≠ 0 := by
    intro hzero
    have := μ.toSphere_eq_zero_iff_finrank.mp hzero
    omega
  have := ae_neBot.mpr hμ
  obtain ⟨v, hv⟩ :=
    (ae_toSphere_all_measure_reflected_normalLineAwayZero_eq_zero μ hdim e ν).exists
  exact ⟨(ℝ ∙ (v : F)).reflection, hv⟩

/-- A deterministic orthonormal frame whose every normal line avoids all
nonzero frequency mass in a countable family.  The basis and its common
orthogonal transformation are constructed from the preceding reflection result. -/
theorem exists_orthonormalBasis_all_measure_normalLines_eq_zero
    {κ : Type*} [Countable κ]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hdim : 2 < Module.finrank ℝ F)
    (ν : κ → Measure F) [∀ j, SFinite (ν j)] :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F, ∀ i j,
      ν j ((ℝ ∙ b i : Set F) \ {0}) = 0 := by
  let b := stdOrthonormalBasis ℝ F
  let e (i : Fin (Module.finrank ℝ F)) : sphere (0 : F) 1 :=
    ⟨b i, by simpa only [mem_sphere_zero_iff_norm] using b.norm_eq_one i⟩
  obtain ⟨O, hO⟩ :=
    exists_linearIsometryEquiv_all_measure_normalLines_eq_zero μ hdim e ν
  exact ⟨b.map O, hO⟩

end Reflection

end OTSelector.Probability
