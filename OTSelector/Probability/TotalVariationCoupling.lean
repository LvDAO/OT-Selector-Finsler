import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
import OTSelector.Probability.ProductCouplingTransfer

/-!
Conditions: Two probability laws with a genuine common submeasure and equal residual masses; expectation transfer also supplies bounded measurable coordinate-stable functionals, while freezing normalization supplies positive original mass and η<1.

Objects: An explicit diagonal common-part plus normalized residual-product coupling, off-diagonal mass≤residual mass and sharp n-point expectation-transfer bounds.

Proof detail: Place the common measure on the diagonal and couple the two equal-mass residuals by their normalized product, treating zero residual mass separately. Lift that actual coupling to the iid product and invoke the mismatch-count transfer.

References: David A. Levin and Yuval Peres, with contributions by Elizabeth L. Wilmer: Section 4.2, pp. 49–52, Proposition 4.7, Remark 4.8 and equations (4.8)–(4.13); D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: The common-overlap coupling method is standard. Lean formulates it for measurable equality and general finite measures rather than the book finite-state pmf setting; optimal total-variation equality is not needed for its upper bound.
-/


/-!
# Couplings from a common-part decomposition

Two probability laws that share a common submeasure `θ` and have residuals `a`,
`b` of equal total mass `M` are coupled by

`π = diag_# θ + M⁻¹ • (a ⊗ b)`.

The diagonal part carries the common mass exactly, and the product part spreads
the two residual masses independently; its mass on the diagonal is never larger
than its total mass, so the off-diagonal mass of `π` is at most `M`.  This is the
elementary coupling behind the sharp total-variation transfer estimate, and it
uses only the Jordan/subtraction infrastructure already available for finite
measures.
-/

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section
namespace OTSelector.Probability

variable {X : Type*} [MeasurableSpace X] [MeasurableEq X]

/-- Pushforward of a measure by the diagonal map. -/
def diagonalMeasure (μ : Measure X) : Measure (X × X) :=
  μ.map (fun x => (id x, id x))

/-- The first marginal of the diagonal pushforward. -/
theorem diagonalMeasure_fst (μ : Measure X) :
    Measure.map Prod.fst (diagonalMeasure μ) = μ := by
  rw [diagonalMeasure, Measure.map_map (g := Prod.fst) (f := fun x : X => (id x, id x))
    measurable_fst (measurable_id.prodMk measurable_id)]
  rw [show Prod.fst ∘ (fun x : X => (id x, id x)) = id from rfl, Measure.map_id]

/-- The second marginal of the diagonal pushforward. -/
theorem diagonalMeasure_snd (μ : Measure X) :
    Measure.map Prod.snd (diagonalMeasure μ) = μ := by
  rw [diagonalMeasure, Measure.map_map (g := Prod.snd) (f := fun x : X => (id x, id x))
    measurable_snd (measurable_id.prodMk measurable_id)]
  rw [show Prod.snd ∘ (fun x : X => (id x, id x)) = id from rfl, Measure.map_id]

/-- The diagonal pushforward charges no off-diagonal pair. -/
theorem diagonalMeasure_offDiag (μ : Measure X) :
    diagonalMeasure μ {z : X × X | z.1 ≠ z.2} = 0 := by
  rw [diagonalMeasure, Measure.map_apply (measurable_id.prodMk measurable_id)
    measurableSet_offDiag]
  have hpre : (fun x : X => (id x, id x)) ⁻¹' {z : X × X | z.1 ≠ z.2} = (∅ : Set X) := by
    ext x
    simp
  rw [hpre]
  simp

/-- **Coupling from a common-part decomposition.**  If `μ = θ + a` and
`ν = θ + b` with `a` and `b` of equal finite mass `M ≤ δ`, then there is a
coupling of `μ` and `ν` whose off-diagonal mass is at most `δ`. -/
theorem exists_coupling_of_common_decomposition
    {μ ν θ a b : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : θ + a = μ) (hν : θ + b = ν)
    (hmass : a Set.univ = b Set.univ) {δ : ℝ}
    (hδ : a Set.univ ≤ ENNReal.ofReal δ) :
    ∃ π : Measure (X × X), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν ∧
      π {z : X × X | z.1 ≠ z.2} ≤ ENNReal.ofReal δ := by
  classical
  by_cases hM : a Set.univ = 0
  · -- Equal zero residuals: the two laws coincide.
    have ha0 : a = 0 := Measure.measure_univ_eq_zero.mp hM
    have hb0 : b = 0 := Measure.measure_univ_eq_zero.mp (by rw [← hmass]; exact hM)
    have hμθ : μ = θ := by rw [← hμ, ha0, add_zero]
    have hνθ : ν = θ := by rw [← hν, hb0, add_zero]
    haveI hdiag : IsProbabilityMeasure (diagonalMeasure μ) :=
      Measure.isProbabilityMeasure_map (μ := μ) (f := fun x : X => (id x, id x))
        (measurable_id.prodMk measurable_id).aemeasurable
    refine ⟨diagonalMeasure μ, hdiag, diagonalMeasure_fst μ, ?_, ?_⟩
    · rw [show ν = μ from hνθ.trans hμθ.symm]
      exact diagonalMeasure_snd μ
    · rw [diagonalMeasure_offDiag]
      exact zero_le
  · -- Positive residual mass.
    have ha_le : a ≤ μ := by
      rw [← hμ]
      exact Measure.le_add_left le_rfl
    have hb_le : b ≤ ν := by
      rw [← hν]
      exact Measure.le_add_left le_rfl
    haveI : IsFiniteMeasure a := isFiniteMeasure_of_le μ ha_le
    haveI : IsFiniteMeasure b := isFiniteMeasure_of_le ν hb_le
    have hMtop : a Set.univ ≠ ⊤ := measure_ne_top a Set.univ
    have hMpos : 0 < (a Set.univ).toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨lt_of_le_of_ne zero_le (Ne.symm hM), lt_top_iff_ne_top.mpr hMtop⟩
    -- The residual scale.
    let c : ℝ≥0∞ := ENNReal.ofReal (a Set.univ).toReal⁻¹
    have hc_eq : c = (a Set.univ)⁻¹ := by
      dsimp only [c]
      rw [ENNReal.ofReal_inv_of_pos hMpos, ENNReal.ofReal_toReal hMtop]
    have hcM : c * (a Set.univ) = 1 := by
      rw [hc_eq]
      exact ENNReal.inv_mul_cancel hM hMtop
    -- The candidate coupling.
    refine ⟨diagonalMeasure θ + c • (a.prod b), ?_, ?_, ?_, ?_⟩
    · -- Total mass one.
      constructor
      have hdiag : (diagonalMeasure θ) Set.univ = θ Set.univ := by
        rw [diagonalMeasure, Measure.map_apply (measurable_id.prodMk measurable_id)
          MeasurableSet.univ]
        simp
      have hprod : c * (a Set.univ * b Set.univ) = a Set.univ := by
        rw [← hmass]
        calc c * (a Set.univ * a Set.univ) = (c * (a Set.univ)) * a Set.univ := by ring
          _ = a Set.univ := by rw [hcM, one_mul]
      have hsum : θ Set.univ + a Set.univ = 1 := by
        have h := congrArg (fun m : Measure X => m Set.univ) hμ
        simpa only [Measure.add_apply, measure_univ] using h
      have hproduniv : (a.prod b) Set.univ = a Set.univ * b Set.univ := by
        rw [← Set.univ_prod_univ, Measure.prod_prod]
      rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hdiag, hproduniv, hprod, hsum]
    · -- First marginal.
      rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, diagonalMeasure_fst,
        Measure.map_fst_prod, smul_smul, ← hmass, hcM, one_smul]
      exact hμ
    · -- Second marginal.
      rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, diagonalMeasure_snd,
        Measure.map_snd_prod, smul_smul, hcM, one_smul]
      exact hν
    · -- Off-diagonal mass.
      have hmono : (a.prod b) {z : X × X | z.1 ≠ z.2} ≤ (a.prod b) Set.univ :=
        measure_mono (Set.subset_univ _)
      calc (diagonalMeasure θ + c • (a.prod b)) {z : X × X | z.1 ≠ z.2}
          = diagonalMeasure θ {z : X × X | z.1 ≠ z.2} +
              c * (a.prod b) {z : X × X | z.1 ≠ z.2} := by
            rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
        _ = c * (a.prod b) {z : X × X | z.1 ≠ z.2} := by
            rw [diagonalMeasure_offDiag, zero_add]
        _ ≤ c * (a.prod b) Set.univ := by gcongr
        _ = c * (a Set.univ * b Set.univ) := by
            rw [← Set.univ_prod_univ, Measure.prod_prod]
        _ = (c * (a Set.univ)) * b Set.univ := by ring
        _ = a Set.univ := by rw [hcM, one_mul, ← hmass]
        _ ≤ ENNReal.ofReal δ := hδ

/-- **Sharp total-variation transfer.**  If `μ = θ + a` and `ν = θ + b` with
equal residual masses `M ≤ δ`, then an `n`-point functional with coordinate-count
stability `B` has expectations under the two product laws differing by at most
`B * n * δ`. -/
theorem abs_integral_pi_sub_le_of_common_decomposition
    {μ ν θ a b : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : θ + a = μ) (hν : θ + b = ν)
    (hmass : a Set.univ = b Set.univ)
    {n : ℕ} (F : (Fin n → X) → ℝ) (hF : Measurable F)
    {B δ C : ℝ} (hB : 0 ≤ B) (hδ0 : 0 ≤ δ)
    (hFb : ∀ x, |F x| ≤ C)
    (hδ : a Set.univ ≤ ENNReal.ofReal δ)
    (hstable : ∀ x y : Fin n → X, |F x - F y| ≤ B * pairDiffCount n x y) :
    |∫ x, F x ∂(Measure.pi (fun _ : Fin n => μ)) -
      ∫ y, F y ∂(Measure.pi (fun _ : Fin n => ν))| ≤ B * (n : ℝ) * δ := by
  obtain ⟨π, hπprob, hπ1, hπ2, hoff⟩ :=
    exists_coupling_of_common_decomposition hμ hν hmass hδ
  haveI : IsProbabilityMeasure π := hπprob
  exact abs_integral_pi_sub_le_of_coupling μ ν π hπ1 hπ2 F hF hB hδ0 hFb hoff hstable

end OTSelector.Probability

namespace OTSelector.Probability

open OTSelector.Reconstruction

variable {X : Type*} [MeasurableSpace X] [MeasurableEq X]

/-- **Transfer across a raw finite-law freezing bound.**  A relative mass error
and raw total-variation error `η` between two finite cell laws give a normalized
probability error `3η/(1−η)`, and hence a per-sample transfer cost `3η/(1−η)` for
coordinate-count-stable functionals. -/
theorem abs_integral_pi_sub_le_of_finiteLawFreezingBound
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {η : ℝ} (D : FiniteLawFreezingBound μ ν η) (hη : 0 ≤ η) (hη1 : η < 1)
    (hν : 0 < ν.real Set.univ)
    {n : ℕ} (F : (Fin n → X) → ℝ) (hF : Measurable F)
    {B C : ℝ} (hB : 0 ≤ B) (hFb : ∀ x, |F x| ≤ C)
    (hstable : ∀ x y : Fin n → X, |F x - F y| ≤ B * pairDiffCount n x y) :
    |∫ x, F x ∂(Measure.pi (fun _ : Fin n => normalizedFiniteLaw μ)) -
      ∫ y, F y ∂(Measure.pi (fun _ : Fin n => normalizedFiniteLaw ν))| ≤
      B * (n : ℝ) * (3 * η / (1 - η)) := by
  obtain ⟨hvpos, _⟩ := D.normalized_variation hη hη1 hν
  obtain ⟨θ, hθμ, hθν, hmass, hres⟩ := D.normalized_common_part hη hη1 hν
  haveI : IsProbabilityMeasure (normalizedFiniteLaw μ) :=
    normalizedFiniteLaw_probability μ hvpos
  haveI : IsProbabilityMeasure (normalizedFiniteLaw ν) :=
    normalizedFiniteLaw_probability ν hν
  haveI : IsFiniteMeasure θ := isFiniteMeasure_of_le (normalizedFiniteLaw μ) hθμ
  have hδ0 : 0 ≤ 3 * η / (1 - η) := by positivity
  refine abs_integral_pi_sub_le_of_common_decomposition
    (μ := normalizedFiniteLaw μ) (ν := normalizedFiniteLaw ν) (θ := θ)
    (a := normalizedFiniteLaw μ - θ) (b := normalizedFiniteLaw ν - θ)
    ?_ ?_ hmass F hF hB hδ0 hFb hres hstable
  · rw [add_comm]
    exact Measure.sub_add_cancel_of_le hθμ
  · rw [add_comm]
    exact Measure.sub_add_cancel_of_le hθν

end OTSelector.Probability
