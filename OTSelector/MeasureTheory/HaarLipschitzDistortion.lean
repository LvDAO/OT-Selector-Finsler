import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
## Lemma skeleton

* **Conditions:** An arbitrary subset S of a finite-dimensional real normed space; maps with the stated Lipschitz/antilipschitz restriction, or displacement T-id of Lipschitz constant one half; any additive Haar normalization.
* **Objects:** Lipschitz constants 3/2 and inverse constant 2, and upper/lower image-volume distortion for every subset of S.
* **Proof detail:** Use triangle/reverse-triangle inequalities for T and its inverse on the image. Apply the Hausdorff outer-measure Lipschitz^dimension inequality and Haar uniqueness.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38
* D. H. Fremlin, *Measure Theory, Volume 2*, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22

**Relationship to the sources:** Norm/outer-measure inequalities valid for arbitrary nonmeasurable subsets, without injectivity beyond the supplied antilipschitz conclusion. The exact constants are locally derived.
-/

/-!
# Haar distortion of maps with small Lipschitz displacement

A displacement with Lipschitz constant one half gives an actual map with Lipschitz
constant three halves and inverse Lipschitz constant two. Finite-dimensional Haar
uniqueness transfers the existing Hausdorff image estimate to every additive Haar
measure. Both image bounds hold for arbitrary subsets, without measurability inputs.
-/

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E]

/-- A displacement bounded by one half makes the original map three-halves Lipschitz. -/
theorem lipschitzOnWith_of_half_lipschitz_displacement {T : E → E} {S : Set E}
    (h : LipschitzOnWith (1 / 2) (fun x ↦ T x - x) S) :
    LipschitzOnWith (3 / 2) T S := by
  have hh := h.add LipschitzWith.id.lipschitzOnWith
  norm_num at hh
  simpa using! hh

/-- The original map with half-Lipschitz displacement expands distances by at least
one half on its actual domain; the assertion includes injectivity on that domain. -/
theorem antilipschitzWith_of_half_lipschitz_displacement {T : E → E} {S : Set E}
    (h : LipschitzOnWith (1 / 2) (fun x ↦ T x - x) S) :
    AntilipschitzWith 2 (S.domRestrict T) := by
  have hh := (AntilipschitzWith.subtype_coe S).add_lipschitzWith h.to_restrict
    (by norm_num : (1 / 2 : ℝ≥0) < (1 : ℝ≥0)⁻¹)
  have hC : ((1 : ℝ≥0)⁻¹ - 1 / 2)⁻¹ = 2 := by
    apply NNReal.coe_injective
    norm_num [NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
  rw [hC] at hh
  simpa only [Set.domRestrict, add_sub_cancel] using! hh

/-- The unique inverse on the actual image has the same Lipschitz constant as the
map's inverse distance bound. Its arbitrary values outside the image are unused. -/
theorem lipschitzOnWith_invFunOn_of_antilipschitzWith {T : E → E} {S : Set E}
    {C : ℝ≥0} (h : AntilipschitzWith C (S.domRestrict T)) :
    LipschitzOnWith C (Function.invFunOn T S) (T '' S) := by
  apply lipschitzOnWith_iff_restrict.mpr
  exact h.to_rightInvOn' (fun _ hy ↦ Function.invFunOn_mem hy)
    (fun _ hy ↦ Function.invFunOn_eq hy)

section Haar

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every Lipschitz map has the dimension-power image bound for any additive Haar
measure, on arbitrary subsets of its Lipschitz domain. -/
theorem haar_image_le_of_lipschitzOnWith (m : Measure E) [IsAddHaarMeasure m]
    {T : E → E} {S : Set E} {C : ℝ≥0} (h : LipschitzOnWith C T S)
    {B : Set E} (hB : B ⊆ S) :
    m (T '' B) ≤ (C : ℝ≥0∞) ^ Module.finrank ℝ E * m B := by
  let H : Measure E := μH[Module.finrank ℝ E]
  have hm : m = addHaarScalarFactor m H • H := isAddLeftInvariant_eq_smul m H
  have hh : H (T '' B) ≤ (C : ℝ≥0∞) ^ Module.finrank ℝ E * H B := by
    simpa only [ENNReal.rpow_natCast] using
      (h.mono hB).hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ Module.finrank ℝ E)
  rw [hm]
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_left_comm,
    mul_assoc] using mul_le_mul_right hh (addHaarScalarFactor m H : ℝ≥0∞)

/-- The inverse distance bound controls loss of Haar mass on arbitrary subsets of
the actual domain, with no assumption on measurability of the set or its image. -/
theorem haar_le_image_of_antilipschitzWith (m : Measure E) [IsAddHaarMeasure m]
    {T : E → E} {S : Set E} {C : ℝ≥0} (h : AntilipschitzWith C (S.domRestrict T))
    {B : Set E} (hB : B ⊆ S) :
    m B ≤ (C : ℝ≥0∞) ^ Module.finrank ℝ E * m (T '' B) := by
  have hinj : InjOn T S := injOn_iff_injective.mpr h.injective
  have hh := haar_image_le_of_lipschitzOnWith m
    (lipschitzOnWith_invFunOn_of_antilipschitzWith h) (image_mono hB)
  rwa [hinj.invFunOn_image hB] at hh

/-- A single bound on the actual displacement gives two-sided uniform Haar distortion
for every subset. Constants depend only on dimension, and the original map is retained. -/
theorem haar_image_distortion_of_half_lipschitz_displacement
    (m : Measure E) [IsAddHaarMeasure m] {T : E → E} {S : Set E}
    (h : LipschitzOnWith (1 / 2) (fun x ↦ T x - x) S) :
    LipschitzOnWith (3 / 2) T S ∧ AntilipschitzWith 2 (S.domRestrict T) ∧
      LipschitzOnWith 2 (Function.invFunOn T S) (T '' S) ∧
      ∀ B ⊆ S,
        m (T '' B) ≤ (3 / 2 : ℝ≥0∞) ^ Module.finrank ℝ E * m B ∧
        m B ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E * m (T '' B) := by
  have hLip := lipschitzOnWith_of_half_lipschitz_displacement h
  have hAnti := antilipschitzWith_of_half_lipschitz_displacement h
  refine ⟨hLip, hAnti, lipschitzOnWith_invFunOn_of_antilipschitzWith hAnti, ?_⟩
  intro B hB
  constructor
  · simpa using haar_image_le_of_lipschitzOnWith m hLip hB
  · simpa using haar_le_image_of_antilipschitzWith m hAnti hB

end Haar
end OTSelector.Geometry
