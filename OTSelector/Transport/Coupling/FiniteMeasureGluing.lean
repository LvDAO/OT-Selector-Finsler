import LeanPool.Vlasov.OT.Coupling

/-!
# Transport.Coupling.FiniteMeasureGluing

## Lemma skeleton

* **Conditions:** Two finite adjacent pair laws with the same middle marginal; the final target is a nonempty standard Borel space.

* **Objects:** A genuine finite three-point joint retaining each entire adjacent pair marginal.

* **Proof detail:** Disintegrate the second pair law over its first coordinate. Pull its conditional Markov kernel back to the middle coordinate of the first pair and take the kernel product. The common-middle identity gives the second adjacent marginal, including zero common mass.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185): Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4).

Source relation (generalization): The usual gluing lemma in a finite-mass formulation that preserves arbitrary source metadata and does not normalize by total mass.
-/

/-! Finite-mass three-point coupling joints preserve both actual adjacent plans.
The first endpoint may carry arbitrary source-class and path metadata. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 300000
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [StandardBorelSpace C] [Nonempty C]

/-- The genuine three-point joint obtained by disintegrating the second finite
plan over the common middle marginal. No probability mass normalization is used. -/
def finiteStageCouplingJoint (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    [IsFiniteMeasure π₂] : Measure ((A × B) × C) :=
  π₁ ⊗ₘ (π₂.condKernel.comap Prod.snd measurable_snd)

/-- The first two-coordinate marginal of the actual joint is the entire first
plan, retaining any source labels and previous path metadata. -/
theorem finiteStageCouplingJoint_fst (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂] :
    (finiteStageCouplingJoint π₁ π₂).fst = π₁ := by
  exact Measure.fst_compProd _ _

/-- The second two-coordinate marginal is the entire second plan whenever the
middle marginals agree, including the case of zero common mass. -/
theorem finiteStageCouplingJoint_snd_pair
    (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂] (hmiddle : π₁.snd = π₂.fst) :
    (finiteStageCouplingJoint π₁ π₂).map (fun z ↦ (z.1.2, z.2)) = π₂ := by
  have hproj : Measurable (fun z : (A × B) × C ↦ (z.1.2, z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hdisint : π₁.snd ⊗ₘ π₂.condKernel = π₂ := by
    rw [hmiddle]
    exact Measure.disintegrate π₂ π₂.condKernel
  ext s hs
  calc
    _ = ∫⁻ p, π₂.condKernel p.2 (Prod.mk p.2 ⁻¹' s) ∂π₁ := by
      rw [Measure.map_apply hproj hs, finiteStageCouplingJoint,
        Measure.compProd_apply (hproj hs)]
      apply lintegral_congr
      intro p
      rw [Kernel.comap_apply]
      rfl
    _ = ∫⁻ b, π₂.condKernel b (Prod.mk b ⁻¹' s) ∂π₁.snd := by
      exact (lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_snd).symm
    _ = (π₁.snd ⊗ₘ π₂.condKernel) s := (Measure.compProd_apply hs).symm
    _ = π₂ s := congrArg (fun μ ↦ μ s) hdisint

/-- Arbitrary finite adjacent plans admit a genuine finite joint, without a
unit-mass condition on any marginal. -/
theorem exists_finiteStageCouplingJoint
    (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂] (hmiddle : π₁.snd = π₂.fst) :
    ∃ θ : Measure ((A × B) × C), IsFiniteMeasure θ ∧ θ.fst = π₁ ∧
      θ.map (fun z ↦ (z.1.2, z.2)) = π₂ := by
  refine ⟨finiteStageCouplingJoint π₁ π₂, ?_, finiteStageCouplingJoint_fst _ _,
    finiteStageCouplingJoint_snd_pair _ _ hmiddle⟩
  unfold finiteStageCouplingJoint
  infer_instance

end OTSelector.Reconstruction
