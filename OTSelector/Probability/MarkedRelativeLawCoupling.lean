import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pointwise
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Probability.CommonSubplanSampling
import OTSelector.Probability.ProductCouplingTransfer

/-!
Conditions: Actual one-point source/target probability couplings with specified original iid marginals and disagreement bounds, integrable original comparison functionals and an explicit integrable pointwise repair remainder.

Objects: True product-cloud marginals, exact expected moved-endpoint count and an integrated relative comparison retaining the kinetic repair remainder.

Proof detail: Take the product of the original endpoint couplings, compute expected mismatch indicators and integrate the supplied deterministic repair inequality using the exact marginal-law identities.

References: David A. Levin and Yuval Peres, with contributions by Elizabeth L. Wilmer: Section 4.2, pp. 49–52, Proposition 4.7, Remark 4.8 and equations (4.8)–(4.13); Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A local coupling/integration adapter with its actual remainder. Only the bounded probe term is charged to disagreement; the kinetic repair is left explicit rather than hidden in a total-variation estimate.
-/


/-!
# Relative law transfer with an explicit repair remainder

The product coupling has the exact iid laws on both sides. Its expected number
of moved endpoints is linear in the one-point disagreement probabilities. The
retained-matching estimate therefore charges only the bounded probe to total
variation; the kinetic contribution of the repair remains explicit.
-/

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableEq X] [MeasurableEq Y]

omit [MeasurableSpace X] [MeasurableEq X] in
/-- The mismatch count is bounded by the sample size. -/
theorem diffCount_nonneg_le (n : ℕ) (z : Fin n → X × X) :
    0 ≤ diffCount n z ∧ diffCount n z ≤ n := by
  classical
  constructor
  · exact Nat.cast_nonneg _
  · unfold diffCount
    exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i ↦ (z i).1 ≠ (z i).2)).trans (by simp)

/-- The mismatch count is integrable under any finite paired-sample law. -/
theorem integrable_diffCount (n : ℕ) (P : Measure (Fin n → X × X))
    [IsFiniteMeasure P] : Integrable (diffCount (X := X) n) P := by
  apply Integrable.of_bound (measurable_diffCount n).aestronglyMeasurable n
  filter_upwards with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg (diffCount_nonneg_le n z).1] using
    (diffCount_nonneg_le n z).2

/-- Expected moved coordinates under iid common sampling. -/
theorem integral_diffCount_pi (n : ℕ) (γ : Measure (X × X))
    [IsProbabilityMeasure γ] :
    ∫ z, diffCount n z ∂(Measure.pi fun _ : Fin n ↦ γ) =
      (n : ℝ) * (γ {p | p.1 ≠ p.2}).toReal := by
  classical
  let P := Measure.pi fun _ : Fin n ↦ γ
  have hfun : (fun z : Fin n → X × X ↦ diffCount n z) =
      fun z ↦ ∑ i : Fin n, if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0 := by
    funext z
    unfold diffCount
    rw [Finset.card_filter]
    push_cast
    rfl
  have hInt (i : Fin n) :
      Integrable (fun z : Fin n → X × X ↦ if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0) P := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun z ↦ ?_)
    · exact (Measurable.ite
        (measurableSet_offDiag.preimage (measurable_pi_apply i))
        measurable_const measurable_const).aestronglyMeasurable
    · split_ifs <;> simp
  have hterm (i : Fin n) :
      ∫ z : Fin n → X × X, (if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0) ∂P =
        (γ {p | p.1 ≠ p.2}).toReal := by
    have hmap : P.map (Function.eval i) = γ := by
      dsimp only [P]
      rw [Measure.pi_map_eval]
      simp
    have hind : (fun z : Fin n → X × X ↦ if (z i).1 ≠ (z i).2 then (1 : ℝ) else 0) =
        {z | (z i).1 ≠ (z i).2}.indicator (fun _ ↦ (1 : ℝ)) := by
      funext z
      by_cases h : (z i).1 ≠ (z i).2 <;> simp [Set.indicator, h]
    rw [hind, integral_indicator_const (μ := P) (s := {z | (z i).1 ≠ (z i).2})
      (1 : ℝ) (measurableSet_offDiag.preimage (measurable_pi_apply i))]
    simp only [Measure.real, smul_eq_mul, mul_one]
    change (P ((Function.eval i) ⁻¹' {p | p.1 ≠ p.2})).toReal = _
    rw [← Measure.map_apply (measurable_pi_apply i) measurableSet_offDiag, hmap]
  change ∫ z, diffCount n z ∂P = _
  rw [hfun, integral_finsetSum _ (fun i _ ↦ hInt i)]
  simp_rw [hterm]
  simp

/-- Source and target common samplings, independent between colors. -/
def pairedCloudLaw (m n : ℕ) (γs : Measure (X × X)) (γt : Measure (Y × Y)) :
    Measure ((Fin m → X × X) × (Fin n → Y × Y)) :=
  (Measure.pi fun _ : Fin m ↦ γs).prod (Measure.pi fun _ : Fin n ↦ γt)

/-- Project either the actual (`true`) or frozen (`false`) sample. -/
def pairedCloudProj (m n : ℕ) (b : Bool)
    (z : (Fin m → X × X) × (Fin n → Y × Y)) :
    (Fin m → X) × (Fin n → Y) :=
  (coordProj m b z.1, coordProj n b z.2)

theorem measurable_pairedCloudProj (m n : ℕ) (b : Bool) :
    Measurable (pairedCloudProj (X := X) (Y := Y) m n b) :=
  ((measurable_coordProj m b).comp measurable_fst).prodMk
    ((measurable_coordProj n b).comp measurable_snd)

/-- Common sampling preserves both full independent iid cloud laws exactly. -/
theorem pairedCloudLaw_marginals (m n : ℕ)
    (γs : Measure (X × X)) (γt : Measure (Y × Y))
    [IsProbabilityMeasure γs] [IsProbabilityMeasure γt]
    (μs νs : Measure X) (μt νt : Measure Y)
    (hs₀ : γs.map Prod.fst = μs) (hs₁ : γs.map Prod.snd = νs)
    (ht₀ : γt.map Prod.fst = μt) (ht₁ : γt.map Prod.snd = νt) :
    (pairedCloudLaw m n γs γt).map (pairedCloudProj m n true) =
        (Measure.pi fun _ : Fin m ↦ μs).prod (Measure.pi fun _ : Fin n ↦ μt) ∧
    (pairedCloudLaw m n γs γt).map (pairedCloudProj m n false) =
        (Measure.pi fun _ : Fin m ↦ νs).prod (Measure.pi fun _ : Fin n ↦ νt) := by
  have hs := Reconstruction.iid_common_sampling_marginals (I := Fin m) γs μs νs hs₀ hs₁
  have ht := Reconstruction.iid_common_sampling_marginals (I := Fin n) γt μt νt ht₀ ht₁
  constructor
  · rw [← hs.1, ← ht.1]
    exact (Measure.map_prod_map _ _ (measurable_coordProj m true)
      (measurable_coordProj n true)).symm
  · rw [← hs.2, ← ht.2]
    exact (Measure.map_prod_map _ _ (measurable_coordProj m false)
      (measurable_coordProj n false)).symm

/-- Expected endpoint disagreement in the exact two-color coupling. -/
theorem integral_pairedCloud_moved (m n : ℕ)
    (γs : Measure (X × X)) (γt : Measure (Y × Y))
    [IsProbabilityMeasure γs] [IsProbabilityMeasure γt] :
    ∫ z, (diffCount m z.1 + diffCount n z.2) ∂(pairedCloudLaw m n γs γt) =
      (m : ℝ) * (γs {p | p.1 ≠ p.2}).toReal +
        (n : ℝ) * (γt {p | p.1 ≠ p.2}).toReal := by
  let Ps := Measure.pi fun _ : Fin m ↦ γs
  let Pt := Measure.pi fun _ : Fin n ↦ γt
  have hs := (integrable_diffCount m Ps).comp_fst Pt
  have ht := (integrable_diffCount n Pt).comp_snd Ps
  change ∫ z, (diffCount m z.1 + diffCount n z.2) ∂(Ps.prod Pt) = _
  rw [integral_add hs ht]
  have hfirst : ∫ z, diffCount m z.1 ∂(Ps.prod Pt) = ∫ z, diffCount m z ∂Ps := by
    have hmap : (Ps.prod Pt).map Prod.fst = Ps := by simp
    have hi := integral_map (μ := Ps.prod Pt) measurable_fst.aemeasurable
      (measurable_diffCount (X := X) m).aestronglyMeasurable
    rw [hmap] at hi
    exact hi.symm
  have hsecond : ∫ z, diffCount n z.2 ∂(Ps.prod Pt) = ∫ z, diffCount n z ∂Pt := by
    have hmap : (Ps.prod Pt).map Prod.snd = Pt := by simp
    have hi := integral_map (μ := Ps.prod Pt) measurable_snd.aemeasurable
      (measurable_diffCount (X := Y) n).aestronglyMeasurable
    rw [hmap] at hi
    exact hi.symm
  rw [hfirst, hsecond, integral_diffCount_pi, integral_diffCount_pi]

/-- Integrating a retained-core comparison charges total variation only to the
bounded probe. `R` is the actual repair kinetic cost, which may use the original
residual subplan and needs no uniform bound on the kinetic kernel. -/
theorem integral_le_relative_of_pairedCloud_repair (m n : ℕ)
    (γs : Measure (X × X)) (γt : Measure (Y × Y))
    [IsProbabilityMeasure γs] [IsProbabilityMeasure γt]
    (μs νs : Measure X) (μt νt : Measure Y)
    (hs₀ : γs.map Prod.fst = μs) (hs₁ : γs.map Prod.snd = νs)
    (ht₀ : γt.map Prod.fst = μt) (ht₁ : γt.map Prod.snd = νt)
    (F F' : ((Fin m → X) × (Fin n → Y)) → ℝ)
    (R : ((Fin m → X × X) × (Fin n → Y × Y)) → ℝ)
    {ρ K δs δt : ℝ} (hK : 0 ≤ K) (hδs : 0 ≤ δs) (hδt : 0 ≤ δt)
    (hFs : Measurable F) (hFt : Measurable F')
    (hF : Integrable F ((Measure.pi fun _ : Fin m ↦ μs).prod
      (Measure.pi fun _ : Fin n ↦ μt)))
    (hF' : Integrable F' ((Measure.pi fun _ : Fin m ↦ νs).prod
      (Measure.pi fun _ : Fin n ↦ νt)))
    (hR : Integrable R (pairedCloudLaw m n γs γt))
    (hbs : γs {p | p.1 ≠ p.2} ≤ ENNReal.ofReal δs)
    (hbt : γt {p | p.1 ≠ p.2} ≤ ENNReal.ofReal δt)
    (hpoint : ∀ᵐ z ∂(pairedCloudLaw m n γs γt),
      F (pairedCloudProj m n true z) ≤
        (1 + ρ) * F' (pairedCloudProj m n false z) + ρ * K * (min m n : ℝ) +
          R z + 2 * K * (diffCount m z.1 + diffCount n z.2)) :
    ∫ z, F z ∂((Measure.pi fun _ : Fin m ↦ μs).prod
        (Measure.pi fun _ : Fin n ↦ μt)) ≤
      (1 + ρ) * (∫ z, F' z ∂((Measure.pi fun _ : Fin m ↦ νs).prod
        (Measure.pi fun _ : Fin n ↦ νt))) + ρ * K * (min m n : ℝ) +
        (∫ z, R z ∂(pairedCloudLaw m n γs γt)) +
        2 * K * ((m : ℝ) * δs + (n : ℝ) * δt) := by
  let P := pairedCloudLaw m n γs γt
  have : IsProbabilityMeasure P := by dsimp [P, pairedCloudLaw]; infer_instance
  obtain ⟨hmap₀, hmap₁⟩ := pairedCloudLaw_marginals m n γs γt μs νs μt νt
    hs₀ hs₁ ht₀ ht₁
  have hFcomp : Integrable (fun z ↦ F (pairedCloudProj m n true z)) P :=
    (integrable_map_measure hFs.aestronglyMeasurable
      (measurable_pairedCloudProj m n true).aemeasurable).mp (by
        change Integrable F ((pairedCloudLaw m n γs γt).map (pairedCloudProj m n true))
        rw [hmap₀]
        exact hF)
  have hF'comp : Integrable (fun z ↦ F' (pairedCloudProj m n false z)) P :=
    (integrable_map_measure hFt.aestronglyMeasurable
      (measurable_pairedCloudProj m n false).aemeasurable).mp (by
        change Integrable F' ((pairedCloudLaw m n γs γt).map (pairedCloudProj m n false))
        rw [hmap₁]
        exact hF')
  have hD : Integrable (fun z ↦ diffCount m z.1 + diffCount n z.2) P :=
    ((integrable_diffCount m _).comp_fst _).add ((integrable_diffCount n _).comp_snd _)
  have hmono := integral_mono_ae hFcomp
    ((((hF'comp.const_mul (1 + ρ)).add (integrable_const _)).add hR).add
      (hD.const_mul (2 * K))) hpoint
  simp only [Pi.add_apply] at hmono
  have hA := hF'comp.const_mul (1 + ρ)
  have hB := integrable_const (μ := P) (ρ * K * (min m n : ℝ))
  have hC := hD.const_mul (2 * K)
  have hsplit₁ : (∫ z, (1 + ρ) * F' (pairedCloudProj m n false z) +
      ρ * K * (min m n : ℝ) + R z + 2 * K * (diffCount m z.1 + diffCount n z.2) ∂P) =
      (∫ z, (1 + ρ) * F' (pairedCloudProj m n false z) +
        ρ * K * (min m n : ℝ) + R z ∂P) +
          ∫ z, 2 * K * (diffCount m z.1 + diffCount n z.2) ∂P :=
    integral_add ((hA.add hB).add hR) hC
  have hsplit₂ : (∫ z, (1 + ρ) * F' (pairedCloudProj m n false z) +
      ρ * K * (min m n : ℝ) + R z ∂P) =
      (∫ z, (1 + ρ) * F' (pairedCloudProj m n false z) +
        ρ * K * (min m n : ℝ) ∂P) + ∫ z, R z ∂P :=
    integral_add (hA.add hB) hR
  have hsplit₃ : (∫ z, (1 + ρ) * F' (pairedCloudProj m n false z) +
      ρ * K * (min m n : ℝ) ∂P) =
      (∫ z, (1 + ρ) * F' (pairedCloudProj m n false z) ∂P) +
        ∫ _z, ρ * K * (min m n : ℝ) ∂P := integral_add hA hB
  rw [hsplit₁, hsplit₂, hsplit₃, integral_const_mul, integral_const,
    integral_const_mul] at hmono
  have hI₀ : ∫ z, F (pairedCloudProj m n true z) ∂P =
      ∫ z, F z ∂((Measure.pi fun _ : Fin m ↦ μs).prod
        (Measure.pi fun _ : Fin n ↦ μt)) := by
    rw [← hmap₀]
    exact (integral_map (measurable_pairedCloudProj m n true).aemeasurable
      hFs.aestronglyMeasurable).symm
  have hI₁ : ∫ z, F' (pairedCloudProj m n false z) ∂P =
      ∫ z, F' z ∂((Measure.pi fun _ : Fin m ↦ νs).prod
        (Measure.pi fun _ : Fin n ↦ νt)) := by
    rw [← hmap₁]
    exact (integral_map (measurable_pairedCloudProj m n false).aemeasurable
      hFt.aestronglyMeasurable).symm
  have hds : (γs {p | p.1 ≠ p.2}).toReal ≤ δs := by
    simpa [ENNReal.toReal_ofReal hδs] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbs
  have hdt : (γt {p | p.1 ≠ p.2}).toReal ≤ δt := by
    simpa [ENNReal.toReal_ofReal hδt] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbt
  rw [hI₀, hI₁] at hmono
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hmono
  rw [show (∫ z, (diffCount m z.1 + diffCount n z.2) ∂P) = _ from
    integral_pairedCloud_moved m n γs γt] at hmono
  exact hmono.trans (by gcongr)

end OTSelector.Probability
