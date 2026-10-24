import OTSelector.Reconstruction.FinslerPhysicalSceneRealRootedProbeConvolution
import OTSelector.Reconstruction.FinslerPhysicalSceneRootGrid

/-!
# Finitely many original probability root laws recover the signed probe

The compact macro support fixes the finite box set before samples, scales and
source cutoffs. Genuine signed integrability retains exact finite additivity.
-/
open Set Function MeasureTheory ProbabilityTheory OTSelector.Probability BoxIntegral
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]
local notation "V" => (ι → ℝ)

/-- A real full-Haar readout supported in finitely many original grid boxes is
exactly the sum of their original normalized readouts. -/
theorem sum_integral_cavityRoot_grid_eq
    (scale N : ℝ) (cells : Finset (ι → ℤ)) (f : V → ℝ) (hf : Integrable f volume)
    (hsub : Function.support f ⊆ ⋃ ν ∈ cells, physicalSceneRootGridDomain scale ν) :
    (∑ ν ∈ cells, ∫ z, f z ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) =
      ∫ z, f z ∂cavityRootMeasure volume univ N := by
  simp only [cavityRootMeasure, integral_smul_measure, smul_eq_mul, Measure.restrict_univ]
  rw [← Finset.mul_sum, ← integral_biUnion_finset cells
    (fun ν _ ↦ measurableSet_physicalSceneRootGridDomain scale ν)
    (fun _ _ _ _ h ↦ pairwise_disjoint_physicalSceneRootGridDomain scale h)
    (fun _ _ ↦ hf.integrableOn)]
  apply congrArg (fun x ↦ (ENNReal.ofReal N)⁻¹.toReal * x)
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  by_contra h
  exact hz (hsub h)

/-- The signed original convolution is recovered from finitely many unchanged
probability root laws. The finite box set is fixed before the original plan. -/
theorem exists_finite_original_real_macroProbe_root_convolution
    {M : Type*} [MeasurableSpace M]
    (g : C_c(V × (ℝ × ℝ), ℝ)) :
    ∃ cells : Finset (ι → ℤ), ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
      (coord : M → V), Measurable coord →
      ∀ (u : M → ℝ), Measurable u →
      ∀ (scale N : ℝ), 0 < scale → 0 < N → scale ^ Fintype.card ι = N →
      ∀ (η : C_c(V, ℝ)), (∀ v, 0 ≤ η v) →
      (∀ ν : ι → ℤ, IsProbabilityMeasure
        (cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N)) ∧
      (∑ ν ∈ cells, ∫ z, physicalSceneRealMacroClockProbe
        (physicalSceneRootedPlan Γ coord u N z) (scale⁻¹ • z) η g
          ∂cavityRootMeasure volume (physicalSceneRootGridDomain scale ν) N) =
        ∫ p, ∫ v, η v * g (scale⁻¹ • (coord p.1 - v), (u p.1, u p.2)) ∂volume ∂Γ := by
  obtain ⟨cells, hcells⟩ := exists_finite_unit_root_grid_cover
    (g.hasCompactSupport.isCompact.image continuous_fst).isBounded
  refine ⟨cells, ?_⟩
  intro Γ _ coord hcoord u hu scale N hscale hN hpower η hη
  constructor
  · intro ν
    apply isProbabilityMeasure_cavityRootMeasure volume _ N hN
    rw [volume_physicalSceneRootGridDomain scale hscale ν, hpower]
  · let f : V → ℝ := fun z ↦ physicalSceneRealMacroClockProbe
      (physicalSceneRootedPlan Γ coord u N z) (scale⁻¹ • z) η g
    have hf : Integrable f volume := integrable_physicalSceneRealMacroClockProbe_haar
      Γ coord hcoord u hu N hN.le scale η hη g
    have hs : Function.support f ⊆ ⋃ ν ∈ cells, physicalSceneRootGridDomain scale ν := by
      intro z hz
      by_contra hn
      have hnot : scale⁻¹ • z ∉ Prod.fst '' tsupport g := by
        intro h
        have hh := hcells h
        simp only [mem_iUnion] at hh
        obtain ⟨ν, hν, hbox⟩ := hh
        exact hn (mem_biUnion hν hbox)
      have hg0 (st : ℝ × ℝ) : g (scale⁻¹ • z, st) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (mem_image_of_mem Prod.fst h))
      apply hz
      simp only [f, physicalSceneRealMacroClockProbe, hg0, mul_zero, integral_zero]
    rw [sum_integral_cavityRoot_grid_eq scale N cells f hf hs]
    exact integral_physicalSceneRealMacroClockProbe_eq_convolution Γ coord hcoord u hu
      N hN scale η hη g

end OTSelector.Reconstruction
