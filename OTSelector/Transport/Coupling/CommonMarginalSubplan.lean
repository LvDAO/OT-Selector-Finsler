import LeanPool.Vlasov.OT.Coupling
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CommonMarginalSubplan.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CommonMarginalSubplan`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.CommonMarginalSubplan

**Conditions:** A finite original coupling and finite retained source/target submeasures dominated by its exact marginals.

**Objects:** The original subplan with density min(f(x),g(y)) and its marginal-loss-controlled complement.

**Proof detail:** Use the two Radon–Nikodym retention densities, each ≤1, pull them onto the coupling, and take their minimum; pushforward withDensity identities give marginal bounds, and 1−min≤(1−f)+(1−g) controls lost mass.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Section 235G, integration along an inverse-measure-preserving map; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# A fixed original subplan covering both marginal losses

The common plan is cut directly from the original coupling by the minimum of
the two marginal retention densities. Its complement remains a fixed original
subplan, so all original support and calibration constraints are retained.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem map_withDensity_comp
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) {f : A → B} (hf : Measurable f)
    {g : B → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hf]
  rfl

/-- Retain an original pair only up to both original marginal retention densities. -/
def commonMarginalSubplan (π : Measure (X × Y)) (μ : Measure X) (ν : Measure Y)
    (θ₀ : Measure X) (θ₁ : Measure Y) : Measure (X × Y) :=
  π.withDensity (fun p ↦ min (θ₀.rnDeriv μ p.1) (θ₁.rnDeriv ν p.2))

/-- The fixed original complement covers both marginal losses, with no more than
their sum of masses. Both pieces remain dominated by the original coupling. -/
theorem commonMarginalSubplan_spec
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν)
    (θ₀ : Measure X) (θ₁ : Measure Y) (h₀ : θ₀ ≤ μ) (h₁ : θ₁ ≤ ν) :
    let χ := commonMarginalSubplan π μ ν θ₀ θ₁
    χ ≤ π ∧ χ.map Prod.fst ≤ θ₀ ∧ χ.map Prod.snd ≤ θ₁ ∧
      π - χ ≤ π ∧ (π - χ) univ ≤ (μ - θ₀) univ + (ν - θ₁) univ := by
  let _instTheta0 : IsFiniteMeasure θ₀ := isFiniteMeasure_of_le μ h₀
  let _instTheta1 : IsFiniteMeasure θ₁ := isFiniteMeasure_of_le ν h₁
  let f : X × Y → ℝ≥0∞ := θ₀.rnDeriv μ ∘ Prod.fst
  let g : X × Y → ℝ≥0∞ := θ₁.rnDeriv ν ∘ Prod.snd
  let χ := commonMarginalSubplan π μ ν θ₀ θ₁
  have hf : Measurable f := (Measure.measurable_rnDeriv _ _).comp measurable_fst
  have hg : Measurable g := (Measure.measurable_rnDeriv _ _).comp measurable_snd
  have hf1 : ∀ᵐ p ∂π, f p ≤ 1 := by
    have h : ∀ᵐ x ∂π.map Prod.fst, θ₀.rnDeriv μ x ≤ 1 := by
      rw [hπ.1]
      filter_upwards [Measure.rnDeriv_le_one_of_le h₀] with x hx
      exact hx
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_le (Measure.measurable_rnDeriv _ _) measurable_const)).mp h
  have hg1 : ∀ᵐ p ∂π, g p ≤ 1 := by
    have h : ∀ᵐ x ∂π.map Prod.snd, θ₁.rnDeriv ν x ≤ 1 := by
      rw [hπ.2]
      filter_upwards [Measure.rnDeriv_le_one_of_le h₁] with x hx
      exact hx
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le (Measure.measurable_rnDeriv _ _) measurable_const)).mp h
  have hχ : χ ≤ π := by
    calc
      χ ≤ π.withDensity 1 := withDensity_mono (by
        filter_upwards [hf1] with p hp
        exact (min_le_left _ _).trans hp)
      _ = π := withDensity_one
  let _instChi : IsFiniteMeasure χ := isFiniteMeasure_of_le π hχ
  have hfm : (π.withDensity f).map Prod.fst = θ₀ := by
    rw [map_withDensity_comp π measurable_fst (Measure.measurable_rnDeriv _ _), hπ.1]
    exact Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le h₀)
  have hgm : (π.withDensity g).map Prod.snd = θ₁ := by
    rw [map_withDensity_comp π measurable_snd (Measure.measurable_rnDeriv _ _), hπ.2]
    exact Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le h₁)
  have hχf : χ.map Prod.fst ≤ θ₀ := by
    rw [← hfm]
    exact Measure.map_mono (withDensity_mono (.of_forall fun _ ↦ min_le_left _ _))
      measurable_fst
  have hχg : χ.map Prod.snd ≤ θ₁ := by
    rw [← hgm]
    exact Measure.map_mono (withDensity_mono (.of_forall fun _ ↦ min_le_right _ _))
      measurable_snd
  refine ⟨hχ, hχf, hχg, Measure.sub_le, ?_⟩
  have hfmass : (π.withDensity f) univ = θ₀ univ := by
    have h := congrArg (fun ξ : Measure X ↦ ξ univ) hfm
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using h
  have hgmass : (π.withDensity g) univ = θ₁ univ := by
    have h := congrArg (fun ξ : Measure Y ↦ ξ univ) hgm
    simpa only [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ] using h
  have hretained : θ₀ univ + θ₁ univ ≤ π univ + χ univ := by
    rw [← hfmass, ← hgmass, ← Measure.add_apply, ← withDensity_add_left hf]
    have hbound : π.withDensity (f + g) ≤ π.withDensity (1 + fun p ↦ min (f p) (g p)) := by
      apply withDensity_mono
      filter_upwards [hf1, hg1] with p hp hq
      dsimp only [Pi.add_apply, Pi.one_apply]
      rcases le_total (f p) (g p) with h | h
      · rw [min_eq_left h, add_comm]
        exact add_le_add hq le_rfl
      · rw [min_eq_right h]
        exact add_le_add hp le_rfl
    have h := hbound univ
    rw [withDensity_add_left (show Measurable (1 : X × Y → ℝ≥0∞) from measurable_const),
      withDensity_one, Measure.add_apply] at h
    exact h
  have hμmass : μ univ = π univ := by
    rw [← hπ.1, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  have hνmass : ν univ = π univ := by
    rw [← hπ.2, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)).mp
  rw [Measure.sub_apply .univ hχ,
    ENNReal.toReal_sub_of_le (hχ univ) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    Measure.sub_apply .univ h₀,
    ENNReal.toReal_sub_of_le (h₀ univ) (measure_ne_top _ _),
    Measure.sub_apply .univ h₁,
    ENNReal.toReal_sub_of_le (h₁ univ) (measure_ne_top _ _), hμmass, hνmass]
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hretained
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hr
  linarith

/-- The original complement's marginals contain every prescribed lost endpoint. -/
theorem commonMarginalSubplan_residual_marginals
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν)
    (θ₀ : Measure X) (θ₁ : Measure Y) (h₀ : θ₀ ≤ μ) (h₁ : θ₁ ≤ ν) :
    let χ := commonMarginalSubplan π μ ν θ₀ θ₁
    μ - θ₀ ≤ (π - χ).map Prod.fst ∧ ν - θ₁ ≤ (π - χ).map Prod.snd := by
  let χ := commonMarginalSubplan π μ ν θ₀ θ₁
  obtain ⟨hχ, hχ₀, hχ₁, _, _⟩ := commonMarginalSubplan_spec π μ ν hπ θ₀ θ₁ h₀ h₁
  let _instChi : IsFiniteMeasure χ := isFiniteMeasure_of_le π hχ
  have he : (π - χ) + χ = π := Measure.sub_add_cancel_of_le hχ
  constructor
  · apply Measure.sub_le_of_le_add
    have h := congrArg (Measure.map Prod.fst) he
    rw [Measure.map_add _ _ measurable_fst, hπ.1] at h
    calc
      μ = (π - χ).map Prod.fst + χ.map Prod.fst := h.symm
      _ ≤ _ := add_le_add le_rfl hχ₀
  · apply Measure.sub_le_of_le_add
    have h := congrArg (Measure.map Prod.snd) he
    rw [Measure.map_add _ _ measurable_snd, hπ.2] at h
    calc
      ν = (π - χ).map Prod.snd + χ.map Prod.snd := h.symm
      _ ≤ _ := add_le_add le_rfl hχ₁

end
end OTSelector.Reconstruction

end
