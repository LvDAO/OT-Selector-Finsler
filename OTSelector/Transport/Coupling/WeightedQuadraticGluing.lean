import OTSelector.Topology.MetricSpace.FinitePathSquareEnergy
import OTSelector.Transport.Coupling.FiniteMeasureGluing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingWeightedCost.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingWeightedCost`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingWeightedCost

**Conditions:** A genuine three-point joint has the stated two segment marginals and integrable squared costs; k>0.

**Objects:** Endpoint quadratic integrability and the unequal-weight concatenation estimate.

**Proof detail:** Apply d(x,z)²≤(k+1)d(x,y)²/k+(k+1)d(y,z)² pointwise, transfer both majorants through the exact marginals, and integrate; specialize to the constructed gluing joint.

**Sources:** [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Actual unequal-weight quadratic estimates for finite joint concatenation. -/
open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 350000

/-- Any genuine adjacent-plan joint obeys the actual unequal-weight quadratic
estimate, independently of the version of the conditional kernel used. -/
theorem finiteStageJoint_quadratic_weighted_le
    {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (x : A → E) (y : B → E) (z : C → E)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (π₁ : Measure (A × B)) (π₂ : Measure (B × C)) (θ : Measure ((A × B) × C))
    (hθfst : θ.map Prod.fst = π₁)
    (hθsnd : θ.map (fun p ↦ (p.1.2, p.2)) = π₂)
    (hcost₁ : Integrable (fun p ↦ dist (x p.1) (y p.2) ^ 2) π₁)
    (hcost₂ : Integrable (fun p ↦ dist (y p.1) (z p.2) ^ 2) π₂)
    {k : ℝ} (hk : 0 < k) :
    Integrable (fun p ↦ dist (x p.1.1) (z p.2) ^ 2) θ ∧
      (∫ p, dist (x p.1.1) (z p.2) ^ 2 ∂θ) ≤
        (k + 1) / k * (∫ p, dist (x p.1) (y p.2) ^ 2 ∂π₁) +
          (k + 1) * (∫ p, dist (y p.1) (z p.2) ^ 2 ∂π₂) := by
  let c₁ : A × B → ℝ := fun p ↦ dist (x p.1) (y p.2) ^ 2
  let c₂ : B × C → ℝ := fun p ↦ dist (y p.1) (z p.2) ^ 2
  have hc₁ : Measurable c₁ := by fun_prop
  have hc₂ : Measurable c₂ := by fun_prop
  have hpair : Measurable (fun p : (A × B) × C ↦ (p.1.2, p.2)) := by fun_prop
  have hI₁map : Integrable c₁ (θ.map Prod.fst) := by rw [hθfst]; exact hcost₁
  have hI₂map : Integrable c₂ (θ.map (fun p ↦ (p.1.2, p.2))) := by rw [hθsnd]; exact hcost₂
  have hI₁ : Integrable (fun p : (A × B) × C ↦ c₁ p.1) θ :=
    (integrable_map_measure hc₁.aestronglyMeasurable measurable_fst.aemeasurable).mp hI₁map
  have hI₂ : Integrable (fun p : (A × B) × C ↦ c₂ (p.1.2, p.2)) θ :=
    (integrable_map_measure hc₂.aestronglyMeasurable hpair.aemeasurable).mp hI₂map
  have hupper : Integrable (fun p : (A × B) × C ↦
      (k + 1) / k * c₁ p.1 + (k + 1) * c₂ (p.1.2, p.2)) θ :=
    (hI₁.const_mul ((k + 1) / k)).add (hI₂.const_mul (k + 1))
  have hbound (p : (A × B) × C) : dist (x p.1.1) (z p.2) ^ 2 ≤
      (k + 1) / k * c₁ p.1 + (k + 1) * c₂ (p.1.2, p.2) :=
    finiteStage_dist_sq_weighted_le _ _ _ hk
  have hendpoint : Integrable (fun p : (A × B) × C ↦ dist (x p.1.1) (z p.2) ^ 2) θ := by
    apply hupper.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun p ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (dist (x p.1.1) (z p.2)))] using hbound p
  refine ⟨hendpoint, ?_⟩
  have h₁ : (∫ p, c₁ p.1 ∂θ) = ∫ p, c₁ p ∂π₁ := by
    rw [← hθfst]
    exact (integral_map measurable_fst.aemeasurable hc₁.aestronglyMeasurable).symm
  have h₂ : (∫ p, c₂ (p.1.2, p.2) ∂θ) = ∫ p, c₂ p ∂π₂ := by
    rw [← hθsnd]
    exact (integral_map hpair.aemeasurable hc₂.aestronglyMeasurable).symm
  calc
    _ ≤ ∫ p, ((k + 1) / k * c₁ p.1 + (k + 1) * c₂ (p.1.2, p.2)) ∂θ :=
      integral_mono_ae hendpoint hupper (Filter.Eventually.of_forall hbound)
    _ = _ := by
      rw [integral_add (hI₁.const_mul ((k + 1) / k)) (hI₂.const_mul (k + 1)),
        integral_const_mul, integral_const_mul, h₁, h₂]


/-- Concatenating two genuine finite plans obeys the weighted square estimate.
The first endpoint may contain original class labels and earlier path data. -/
theorem finiteStageCouplingJoint_quadratic_weighted_le
    {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace C] [Nonempty C]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (x : A → E) (y : B → E) (z : C → E)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂] (hmiddle : π₁.snd = π₂.fst)
    (hcost₁ : Integrable (fun p ↦ dist (x p.1) (y p.2) ^ 2) π₁)
    (hcost₂ : Integrable (fun p ↦ dist (y p.1) (z p.2) ^ 2) π₂)
    {k : ℝ} (hk : 0 < k) :
    Integrable (fun p ↦ dist (x p.1.1) (z p.2) ^ 2) (finiteStageCouplingJoint π₁ π₂) ∧
      (∫ p, dist (x p.1.1) (z p.2) ^ 2 ∂finiteStageCouplingJoint π₁ π₂) ≤
        (k + 1) / k * (∫ p, dist (x p.1) (y p.2) ^ 2 ∂π₁) +
          (k + 1) * (∫ p, dist (y p.1) (z p.2) ^ 2 ∂π₂) := by
  exact finiteStageJoint_quadratic_weighted_le x y z hx hy hz π₁ π₂
    (finiteStageCouplingJoint π₁ π₂) (finiteStageCouplingJoint_fst π₁ π₂)
    (finiteStageCouplingJoint_snd_pair π₁ π₂ hmiddle) hcost₁ hcost₂ hk

end OTSelector.Reconstruction

end
end
