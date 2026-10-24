import OTSelector.Transport.Coupling.FiniteOrderedStages
import OTSelector.Transport.Coupling.MixtureLabelTransfer
import OTSelector.Transport.Coupling.OrderedStageChain
import OTSelector.Transport.Coupling.StrictOrderedStageChain
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingLegality.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingLegality`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite labeled stage couplings have the actual successive marginals and finite quadratic costs; the strict-order consequence has disjoint source/target colors at each stage.

Objects: A pseudometric ignoring labels, strict ordered classwise coupling and forbidden-label matrix zeros.

Proof detail: Lift smoothing while retaining labels, glue the actual successive couplings, compare nondecreasing labels and eliminate equality using the zero-color condition; forbidden classes have zero carried mass.

Sources: Gabriel Peyré, Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185); D. H. Fremlin, 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary (https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Derived finite-stage gluing/label-support construction. The factor N in quadratic cost is the local path Cauchy–Schwarz bound, not an optimal constant.
-/

/-! Strict class order and actual RN unsmoothing retain the same genuine
quadratic coupling, original labels, physical cost and allowed class pairs. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 300000

/-- The tagged carrier uses exactly physical distance, while retaining its
ordinary product measurable space and the original class coordinate. -/
@[instance_reducible]
def classPhysicalPseudoMetricSpace (C E : Type*) [PseudoMetricSpace E] :
    PseudoMetricSpace (C × E) := PseudoMetricSpace.induced Prod.snd inferInstance

/-- Tagging an actual smoothing law proves both its fixed class and the original
physical support radius under the explicitly induced pseudometric. -/
theorem classPhysical_smoothing_map_support
    {C E : Type*} [MeasurableSpace C] [MeasurableSingletonClass C]
    [MeasurableSpace E] [PseudoMetricSpace E]
    (κ : Measure E) (c : C) (x : E) {r : ℝ}
    (hκ : ∀ᵐ u ∂κ, dist x u ≤ r) :
    letI := classPhysicalPseudoMetricSpace C E
    (∀ᵐ p ∂κ.map (Prod.mk c), p.1 = c) ∧
      (∀ᵐ p ∂κ.map (Prod.mk c), dist (c, x) p ≤ r) := by
  change (∀ᵐ p ∂κ.map (Prod.mk c), p.1 = c) ∧
    (∀ᵐ p ∂κ.map (Prod.mk c), dist x p.2 ≤ r)
  exact ⟨(measurableEmbedding_prodMk_left c).ae_map_iff.mpr (ae_of_all _ fun _ ↦ rfl),
    (measurableEmbedding_prodMk_left c).ae_map_iff.mpr hκ⟩



/-- Any actual ordered labelled coupling is strictly ordered when each class
contains at most one colour; the coupling itself is retained. -/
theorem finiteStageLabelledCoupling_ae_strict_of_colours
    {E : Type*} [MeasurableSpace E] (S T : ℕ → Measure E) (N : ℕ)
    (Γ : Measure ((ℕ × E) × (ℕ × E)))
    (hΓ : Vlasov.IsCoupling Γ (finiteStageLabelledPrefix S N) (finiteStageLabelledPrefix T N))
    (horder : ∀ᵐ p ∂Γ, p.1.1 ≤ p.2.1)
    (hcolours : ∀ k < N, S k = 0 ∨ T k = 0) :
    ∀ᵐ p ∂Γ, p.1.1 < p.2.1 := by
  have hsource : ∀ᵐ p ∂Γ, p.1.1 < N := by
    have h : ∀ᵐ a ∂Γ.fst, a.1 < N := by
      rw [Measure.fst, hΓ.1]
      exact finiteStageLabelledPrefix_ae_lt S N
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have havoid (k : Fin N) : ∀ᵐ p ∂Γ, p.1.1 ≠ (k : ℕ) ∨ p.2.1 ≠ (k : ℕ) := by
    rcases hcolours k k.isLt with hS | hT
    · have h : ∀ᵐ a ∂Γ.fst, a.1 ≠ (k : ℕ) := by
        rw [Measure.fst, hΓ.1]
        exact finiteStageLabelledPrefix_ae_ne_of_zero S N k hS
      exact (ae_of_ae_map measurable_fst.aemeasurable h).mono fun _ hz ↦ Or.inl hz
    · have h : ∀ᵐ a ∂Γ.snd, a.1 ≠ (k : ℕ) := by
        rw [Measure.snd, hΓ.2]
        exact finiteStageLabelledPrefix_ae_ne_of_zero T N k hT
      exact (ae_of_ae_map measurable_snd.aemeasurable h).mono fun _ hz ↦ Or.inr hz
  have hall : ∀ᵐ p ∂Γ, ∀ k : Fin N, p.1.1 ≠ (k : ℕ) ∨ p.2.1 ≠ (k : ℕ) :=
    ae_all_iff.mpr havoid
  filter_upwards [horder, hsource, hall] with p hp hsource hall
  apply Nat.lt_of_le_of_ne hp
  intro heq
  rcases hall ⟨p.1.1, hsource⟩ with hs | ht
  · exact hs rfl
  · exact ht heq.symm

/-- Genuine finite stage plans produce one and the same strictly forward
labelled coupling with integrable square cost and the literal linear-length factor. -/
theorem exists_finiteStrictOrderedQuadraticClasswiseCoupling
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E]
    (ν S T : ℕ → Measure E) (π : ℕ → Measure (E × E)) (N : ℕ)
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hνN : ν N = 0)
    (hπ₁ : ∀ k < N, (π k).fst = ν k + S k)
    (hπ₂ : ∀ k < N, (π k).snd = ν (k + 1) + T k)
    (hcost : ∀ k < N, Integrable (fun p ↦ dist p.1 p.2 ^ 2) (π k))
    (hcolours : ∀ k < N, S k = 0 ∨ T k = 0) :
    ∃ Γ : Measure ((ℕ × E) × (ℕ × E)), IsFiniteMeasure Γ ∧
      Vlasov.IsCoupling Γ (finiteStageLabelledPrefix S N) (finiteStageLabelledPrefix T N) ∧
      (∀ᵐ p ∂Γ, p.1.1 < p.2.1) ∧
      Integrable (fun p ↦ dist p.1.2 p.2.2 ^ 2) Γ ∧
      (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) ≤
        (N : ℝ) * ∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k := by
  obtain ⟨Γ, hfinite, hΓ, horder, hI, hbound⟩ :=
    exists_finiteOrderedQuadraticClasswiseCoupling ν S T π N hν₀ hνN hπ₁ hπ₂ hcost
  exact ⟨Γ, hfinite, hΓ,
    finiteStageLabelledCoupling_ae_strict_of_colours S T N Γ hΓ horder hcolours, hI, hbound⟩

/-- Forbidden class pairs have zero mass in the actual recovered RN label
matrix. Readouts may be the class coordinates of a labelled physical space. -/
theorem smoothingEndpointLabelMatrix_zero_of_forbidden_labels
    {X Y I J K L : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype I] [Fintype J]
    (κ : I → Measure X) (σ : J → Measure Y)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (π : Measure (X × Y)) (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j))
    (sourceClass : X → K) (targetClass : Y → L) (a : I → K) (b : J → L)
    (R : K → L → Prop)
    (hκ : ∀ i, ∀ᵐ x ∂κ i, sourceClass x = a i)
    (hσ : ∀ j, ∀ᵐ y ∂σ j, targetClass y = b j)
    (hR : ∀ᵐ p ∂π, R (sourceClass p.1) (targetClass p.2)) :
    ∀ i j, ¬ R (a i) (b j) → smoothingEndpointLabelMatrix κ σ π i j = 0 := by
  classical
  intro i j hij
  let τ := smoothingEndpointCouplingPart κ σ π i j
  have hleft : τ.map Prod.fst ≤ κ i := by
    calc
      _ ≤ (∑ k, smoothingEndpointCouplingPart κ σ π i k).map Prod.fst :=
        Measure.map_mono (Finset.single_le_sum
          (f := fun k ↦ smoothingEndpointCouplingPart κ σ π i k)
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)) measurable_fst
      _ = _ := smoothingEndpointCouplingPart_row κ σ π hπ i
  have hright : τ.map Prod.snd ≤ σ j := by
    calc
      _ ≤ (∑ k, smoothingEndpointCouplingPart κ σ π k j).map Prod.snd :=
        Measure.map_mono (Finset.single_le_sum
          (f := fun k ↦ smoothingEndpointCouplingPart κ σ π k j)
          (fun _ _ ↦ bot_le) (Finset.mem_univ i)) measurable_snd
      _ = _ := smoothingEndpointCouplingPart_column κ σ π hπ j
  have hs := ae_of_ae_map (μ := τ) measurable_fst.aemeasurable
    (hleft.absolutelyContinuous.ae_le (hκ i))
  have ht := ae_of_ae_map (μ := τ) measurable_snd.aemeasurable
    (hright.absolutelyContinuous.ae_le (hσ j))
  have hRτ := (smoothingEndpointCouplingPart_le κ σ π hπ i j).absolutelyContinuous.ae_le hR
  have hfalse : ∀ᵐ p ∂τ, False := by
    filter_upwards [hs, ht, hRτ] with p hp₁ hp₂ hpR
    exact hij (by simpa only [hp₁, hp₂] using hpR)
  have hzero : τ = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    simpa only [ae_iff, not_false_eq_true, ofPred_true] using hfalse
  change τ.real univ = 0
  simp only [hzero, measureReal_zero_apply]


end OTSelector.Reconstruction

end
end
