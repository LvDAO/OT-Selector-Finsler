import OTSelector.Topology.MetricSpace.FinitePathSquareEnergy
import OTSelector.Transport.Coupling.StageSplice
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingSpliceCost.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingSpliceCost`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingSpliceCost

**Conditions:** A genuine finite one-cut splice witness, measurable original positions and squared metric costs.

**Objects:** Exact three-branch energy bookkeeping and a two-segment quadratic endpoint-cost bound.

**Proof detail:** Read segment costs through the actual component marginals; apply d(x,z)²≤2d(x,y)²+2d(y,z)² on the continuing branch and preserve one-sided branches, then push the labelled plan to physical endpoints.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144), Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144; [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! The actual labelled one-cut splice has exactly the original total path
energy and satisfies the genuine two-segment squared endpoint bound. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 400000
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

/-- Splitting and splicing conserve the literal sum of all stage energies. -/
theorem FiniteStageSpliceWitness.lintegral_energy
    {π₁ : Measure (A × B)} {π₂ : Measure (B × C)} {ρ ν ζ : Measure B}
    (w : FiniteStageSpliceWitness π₁ π₂ ρ ν ζ)
    {c₁ : A × B → ℝ≥0∞} {c₂ : B × C → ℝ≥0∞}
    (hc₁ : Measurable c₁) (hc₂ : Measurable c₂) :
    (∫⁻ p, c₁ p ∂w.leftExit) +
      (∫⁻ p, c₁ p.1 + c₂ (p.1.2, p.2) ∂w.triple) +
      (∫⁻ p, c₂ p ∂w.rightBirth) =
      (∫⁻ p, c₁ p ∂π₁) + ∫⁻ p, c₂ p ∂π₂ := by
  have hm₁ : Measurable (fun p : (A × B) × C ↦ c₁ p.1) := hc₁.comp measurable_fst
  have hpair : Measurable (fun p : (A × B) × C ↦ (p.1.2, p.2)) := by fun_prop
  have h₁ : (∫⁻ p, c₁ p.1 ∂w.triple) = ∫⁻ p, c₁ p ∂w.leftContinue := by
    rw [← lintegral_map hc₁ measurable_fst]
    exact congrArg (fun μ ↦ ∫⁻ p, c₁ p ∂μ) w.triple_fst
  have h₂ : (∫⁻ p, c₂ (p.1.2, p.2) ∂w.triple) = ∫⁻ p, c₂ p ∂w.rightContinue := by
    rw [← lintegral_map hc₂ hpair]
    exact congrArg (fun μ ↦ ∫⁻ p, c₂ p ∂μ) w.triple_snd_pair
  have hleft : (∫⁻ p, c₁ p ∂π₁) =
      (∫⁻ p, c₁ p ∂w.leftContinue) + ∫⁻ p, c₁ p ∂w.leftExit := by
    exact (congrArg (fun μ ↦ ∫⁻ p, c₁ p ∂μ) w.left_decomp).symm.trans
      (lintegral_add_measure _ _ _)
  have hright : (∫⁻ p, c₂ p ∂π₂) =
      (∫⁻ p, c₂ p ∂w.rightContinue) + ∫⁻ p, c₂ p ∂w.rightBirth := by
    exact (congrArg (fun μ ↦ ∫⁻ p, c₂ p ∂μ) w.right_decomp).symm.trans
      (lintegral_add_measure _ _ _)
  rw [lintegral_add_left hm₁, h₁, h₂, hleft, hright]
  ac_rfl

/-- The constructed labelled one-cut plan satisfies the actual two-segment
quadratic endpoint estimate. No cost estimate is assumed as an input. -/
theorem FiniteStageSpliceWitness.labelPlan_quadratic_cost_le
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {π₁ : Measure (A × B)} {π₂ : Measure (B × C)} {ρ ν ζ : Measure B}
    (w : FiniteStageSpliceWitness π₁ π₂ ρ ν ζ)
    (x : A → E) (y : B → E) (z : C → E)
    (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) :
    (∫⁻ p, ENNReal.ofReal (dist (Sum.elim x y p.1) (Sum.elim y z p.2) ^ 2) ∂w.labelPlan) ≤
      2 * ((∫⁻ p, ENNReal.ofReal (dist (x p.1) (y p.2) ^ 2) ∂π₁) +
        ∫⁻ p, ENNReal.ofReal (dist (y p.1) (z p.2) ^ 2) ∂π₂) := by
  let c₁ : A × B → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (dist (x p.1) (y p.2) ^ 2)
  let c₂ : B × C → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (dist (y p.1) (z p.2) ^ 2)
  let c : (A ⊕ B) × (B ⊕ C) → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal (dist (Sum.elim x y p.1) (Sum.elim y z p.2) ^ 2)
  have hc₁ : Measurable c₁ := by fun_prop
  have hc₂ : Measurable c₂ := by fun_prop
  have hc : Measurable c := by fun_prop
  have htag : Measurable (fun p : (A × B) × C ↦
      ((Sum.inl p.1.1 : A ⊕ B), (Sum.inr p.2 : B ⊕ C))) := by fun_prop
  have hcost : (∫⁻ p, c p ∂w.labelPlan) = (∫⁻ p, c₁ p ∂w.leftExit) +
      (∫⁻ p, ENNReal.ofReal (dist (x p.1.1) (z p.2) ^ 2) ∂w.triple) +
      (∫⁻ p, c₂ p ∂w.rightBirth) := by
    rw [FiniteStageSpliceWitness.labelPlan, lintegral_add_measure, lintegral_add_measure,
      lintegral_map hc (measurable_inl.prodMap measurable_inl), lintegral_map hc htag,
      lintegral_map hc (measurable_inr.prodMap measurable_inr)]
    rfl
  have hm : Measurable (fun p : (A × B) × C ↦ c₁ p.1 + c₂ (p.1.2, p.2)) := by fun_prop
  have hbound : (∫⁻ p, ENNReal.ofReal (dist (x p.1.1) (z p.2) ^ 2) ∂w.triple) ≤
      2 * (∫⁻ p, c₁ p.1 + c₂ (p.1.2, p.2) ∂w.triple) := by
    calc
      _ ≤ ∫⁻ p, (2 : ℝ≥0∞) * (c₁ p.1 + c₂ (p.1.2, p.2)) ∂w.triple := by
        apply lintegral_mono
        intro p
        have hr : dist (x p.1.1) (z p.2) ^ 2 ≤
            2 * (dist (x p.1.1) (y p.1.2) ^ 2 + dist (y p.1.2) (z p.2) ^ 2) := by
          have ht := finiteStage_dist_sq_weighted_le (x p.1.1) (y p.1.2) (z p.2) (k := 1) (by norm_num)
          norm_num at ht
          linarith
        simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_add (sq_nonneg (dist (x p.1.1) (y p.1.2)))
            (sq_nonneg (dist (y p.1.2) (z p.2))), c₁, c₂] using ENNReal.ofReal_le_ofReal hr
      _ = _ := lintegral_const_mul 2 hm
  have hmul (r : ℝ≥0∞) : r ≤ 2 * r := by
    exact le_mul_of_one_le_left bot_le (by norm_num)
  rw [hcost]
  calc
    _ ≤ 2 * (∫⁻ p, c₁ p ∂w.leftExit) +
        2 * (∫⁻ p, c₁ p.1 + c₂ (p.1.2, p.2) ∂w.triple) +
        2 * (∫⁻ p, c₂ p ∂w.rightBirth) := add_le_add (add_le_add (hmul _) hbound) (hmul _)
    _ = 2 * ((∫⁻ p, c₁ p ∂w.leftExit) +
        (∫⁻ p, c₁ p.1 + c₂ (p.1.2, p.2) ∂w.triple) + ∫⁻ p, c₂ p ∂w.rightBirth) := by
      rw [mul_add, mul_add]
    _ = _ := by rw [w.lintegral_energy hc₁ hc₂]

/-- The physical one-cut consumer gives a genuine coupling of the original
finite source and target laws with its literal quadratic cost bound. -/
theorem exists_finiteStageCoupling_quadratic_splice
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E]
    (μ ρ ν ζ σ : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ζ] [IsFiniteMeasure σ]
    (π₁ π₂ : Measure (E × E))
    (h₁ : Vlasov.IsCoupling π₁ μ (ρ + ν))
    (h₂ : Vlasov.IsCoupling π₂ (ρ + ζ) σ) :
    ∃ Γ : Measure (E × E), IsFiniteMeasure Γ ∧ Vlasov.IsCoupling Γ (μ + ζ) (ν + σ) ∧
      (∫⁻ p, ENNReal.ofReal (dist p.1 p.2 ^ 2) ∂Γ) ≤
        2 * ((∫⁻ p, ENNReal.ofReal (dist p.1 p.2 ^ 2) ∂π₁) +
          ∫⁻ p, ENNReal.ofReal (dist p.1 p.2 ^ 2) ∂π₂) := by
  have hm₁ : π₁ univ = μ univ := by
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using
      congrArg (fun τ : Measure E ↦ τ univ) h₁.1
  have hm₂ : π₂ univ = (ρ + ζ) univ := by
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using
      congrArg (fun τ : Measure E ↦ τ univ) h₂.1
  have : IsFiniteMeasure π₁ := ⟨by rw [hm₁]; exact measure_lt_top _ _⟩
  have : IsFiniteMeasure π₂ := ⟨by rw [hm₂]; exact measure_lt_top _ _⟩
  obtain ⟨w⟩ := exists_finiteStageSpliceWitness π₁ π₂ ρ ν ζ h₁.2 h₂.1
  have : IsFiniteMeasure w.leftExit := w.leftExit_finite
  have : IsFiniteMeasure w.rightBirth := w.rightBirth_finite
  have : IsFiniteMeasure w.triple := w.triple_finite
  have : IsFiniteMeasure w.labelPlan := by
    unfold FiniteStageSpliceWitness.labelPlan
    infer_instance
  let collapse : E ⊕ E → E := Sum.elim id id
  have hc : Measurable collapse := measurable_id.sumElim measurable_id
  have hcollapse (a b : Measure E) :
      (a.map (Sum.inl : E → E ⊕ E) + b.map Sum.inr).map collapse = a + b := by
    rw [Measure.map_add _ _ hc, Measure.map_map hc measurable_inl,
      Measure.map_map hc measurable_inr]
    change a.map id + b.map id = _
    rw [Measure.map_id, Measure.map_id]
  let Γ := w.labelPlan.map (Prod.map collapse collapse)
  have hΓ : Vlasov.IsCoupling Γ (μ + ζ) (ν + σ) := by
    have h := w.labelPlan_isCoupling.map collapse collapse hc hc
    rw [hcollapse, hcollapse] at h
    simpa only [Measure.fst, Measure.snd, h₁.1, h₂.2] using h
  refine ⟨Γ, inferInstance, hΓ, ?_⟩
  have hmeas : Measurable (fun p : E × E ↦ ENNReal.ofReal (dist p.1 p.2 ^ 2)) := by fun_prop
  change (∫⁻ p, ENNReal.ofReal (dist p.1 p.2 ^ 2) ∂w.labelPlan.map (Prod.map collapse collapse)) ≤ _
  rw [lintegral_map hmeas (hc.prodMap hc)]
  exact w.labelPlan_quadratic_cost_le id id id measurable_id measurable_id measurable_id

end OTSelector.Reconstruction

end
end
