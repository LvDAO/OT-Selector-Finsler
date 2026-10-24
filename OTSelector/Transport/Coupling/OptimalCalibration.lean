import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.Embedding
import OTSelector.Transport.Kantorovich.PotentialAttainment
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OptimalCalibration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OptimalCalibration`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OptimalCalibration

**Conditions:** A one-Lipschitz potential attains the exact distance dual value; compact-carrier probabilities supply such a potential and integrability.

**Objects:** Calibration of every member of the original distance-optimal face.

**Proof detail:** Marginal pushforwards identify the endpoint potential gap, whose nonnegative slack has zero integral exactly at the optimal cost; compact support gives distance integrability and global dual attainment.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110), Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (PDF pages 110–111); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini); [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_metcont.html), Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Calibration characterizes the entire original distance-optimal face

A dual-attaining one-Lipschitz potential calibrates exactly the optimal couplings.
The compact-carrier consumer constructs that potential for the original probabilities;
no calibrated plan or chosen optimizer is an input. All costs remain the lower integral
of the original extended distance.
-/

open Set MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace OTSelector.Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
private theorem optimal_iff_cost_eq_inf {μ ν : Measure M} {π : Measure (M × M)}
    (hπ : Vlasov.IsCoupling π μ ν) :
    IsOptimalCoupling edist μ ν π ↔
      couplingCost edist π = Vlasov.wasserstein1Coupling μ ν := by
  constructor
  · intro h
    apply le_antisymm
    · exact le_iInf fun κ ↦ le_iInf fun hκ ↦ h.2 κ hκ
    · exact iInf_le_of_le π (iInf_le_of_le hπ le_rfl)
  · intro h
    refine ⟨hπ, fun κ hκ ↦ ?_⟩
    rw [h]
    exact iInf_le_of_le κ (iInf_le_of_le hκ le_rfl)

omit [BorelSpace M] in
private theorem cost_eq_ofReal_integral_dist {π : Measure (M × M)}
    (hd : Integrable (fun z : M × M ↦ dist z.1 z.2) π) :
    couplingCost edist π = ENNReal.ofReal (∫ z, dist z.1 z.2 ∂π) := by
  unfold couplingCost
  simp_rw [edist_dist]
  exact (ofReal_integral_eq_lintegral_ofReal hd
    (Eventually.of_forall fun _ ↦ dist_nonneg)).symm

/-- Any dual-attaining one-Lipschitz potential characterizes every original distance
optimizer by almost-everywhere calibration. Integrability of the coupling distance is
inferred in each direction, rather than imposed on a competing plan. -/
theorem isOptimalCoupling_edist_iff_calibrated_of_dual_attainment
    {μ ν : Measure M} {f : M → ℝ} (hf : LipschitzWith 1 f)
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hnonneg : 0 ≤ (∫ x, f x ∂ν) - (∫ x, f x ∂μ))
    (hvalue : ENNReal.ofReal ((∫ x, f x ∂ν) - (∫ x, f x ∂μ)) =
      Vlasov.wasserstein1Coupling μ ν)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν)
    (hπdist : AEStronglyMeasurable (fun z : M × M ↦ dist z.1 z.2) π) :
    IsOptimalCoupling edist μ ν π ↔
      ∀ᵐ z ∂π, f z.2 - f z.1 = dist z.1 z.2 := by
  have hfst : Integrable (fun z : M × M ↦ f z.1) π := by
    have h : Integrable f (π.map Prod.fst) := hπ.1.symm ▸ hfμ
    exact h.comp_aemeasurable measurable_fst.aemeasurable
  have hsnd : Integrable (fun z : M × M ↦ f z.2) π := by
    have h : Integrable f (π.map Prod.snd) := hπ.2.symm ▸ hfν
    exact h.comp_aemeasurable measurable_snd.aemeasurable
  have hgap : Integrable (fun z : M × M ↦ f z.2 - f z.1) π := hsnd.sub hfst
  have hgapIntegral : (∫ z, f z.2 - f z.1 ∂π) =
      (∫ x, f x ∂ν) - (∫ x, f x ∂μ) := by
    rw [integral_sub hsnd hfst]
    congr 1
    · rw [← hπ.2]
      exact (integral_map measurable_snd.aemeasurable hf.continuous.aestronglyMeasurable).symm
    · rw [← hπ.1]
      exact (integral_map measurable_fst.aemeasurable hf.continuous.aestronglyMeasurable).symm
  have hle : (fun z : M × M ↦ f z.2 - f z.1) ≤ᵐ[π]
      (fun z ↦ dist z.1 z.2) := Eventually.of_forall fun z ↦ by
    have h := hf.dist_le_mul z.2 z.1
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_comm z.2 z.1] at h
    exact (le_abs_self _).trans h
  rw [optimal_iff_cost_eq_inf hπ]
  constructor
  · intro hcost
    have hfinite : couplingCost edist π ≠ ∞ := by
      rw [hcost, ← hvalue]
      exact ENNReal.ofReal_ne_top
    have hd : Integrable (fun z : M × M ↦ dist z.1 z.2) π := by
      refine ⟨hπdist, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hn : ∀ z : M × M, ‖dist z.1 z.2‖ₑ = edist z.1 z.2 := fun z ↦ by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg dist_nonneg, edist_dist]
      simp_rw [hn]
      exact hfinite.lt_top
    apply (integral_eq_iff_of_ae_le hgap hd hle).mp
    rw [hgapIntegral]
    apply ((ENNReal.ofReal_eq_ofReal_iff hnonneg
      (integral_nonneg fun _ ↦ dist_nonneg)).mp ?_)
    rw [hvalue, ← cost_eq_ofReal_integral_dist hd, hcost]
  · intro hcal
    have hd : Integrable (fun z : M × M ↦ dist z.1 z.2) π := hgap.congr hcal
    rw [cost_eq_ofReal_integral_dist hd, ← integral_congr_ae hcal, hgapIntegral, hvalue]

private theorem integrable_dist_of_compact_carrier
    {μ ν : Measure M} [IsProbabilityMeasure μ] {K : Set M} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K)
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π μ ν) :
    Integrable (fun z : M × M ↦ dist z.1 z.2) π := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ inferInstance
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  obtain ⟨πK, ⟨_, hmap⟩, _⟩ :=
    existsUnique_subtype_coupling_lift hK.measurableSet hK.measurableSet hμ hν hπ
  have : IsProbabilityMeasure (πK.map (Prod.map ((↑) : K → M) ((↑) : K → M))) :=
    hmap.symm ▸ inferInstance
  have : IsProbabilityMeasure πK :=
    Measure.isProbabilityMeasure_of_map (Prod.map ((↑) : K → M) ((↑) : K → M))
  let d : (K × K) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ dist z.1 z.2, continuous_fst.dist continuous_snd⟩
  rw [← hmap]
  apply ((MeasurableEmbedding.subtype_coe hK.measurableSet).prodMap
    (MeasurableEmbedding.subtype_coe hK.measurableSet)).integrable_map_iff.mpr
  exact d.integrable πK

/-- Compactly carried original probabilities admit a global one-Lipschitz potential
whose calibrated couplings are exactly their entire distance-optimal face. No optimal
or calibrated plan, given potential, or dual-value premise is supplied. -/
theorem exists_optimal_calibration_of_compact_carrier
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set M} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (hν : ∀ᵐ x ∂ν, x ∈ K) (x₀ : K) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f x₀ = 0 ∧
      ∀ π : Measure (M × M), Vlasov.IsCoupling π μ ν →
        (IsOptimalCoupling edist μ ν π ↔
          ∀ᵐ z ∂π, f z.2 - f z.1 = dist z.1 z.2) := by
  obtain ⟨f, hf, hzero, hnonneg, hvalue⟩ :=
    Geometry.exists_optimal_lipschitz_potential_of_compact_carrier μ ν hK hμ hν x₀
  have hfμ : Integrable f μ := by
    have h := hf.continuous.continuousOn.integrableOn_compact hK (μ := μ)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h
  have hfν : Integrable f ν := by
    have h := hf.continuous.continuousOn.integrableOn_compact hK (μ := ν)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hν] at h
  exact ⟨f, hf, hzero, fun π hπ ↦
    isOptimalCoupling_edist_iff_calibrated_of_dual_attainment hf hfμ hfν hnonneg hvalue hπ
      (integrable_dist_of_compact_carrier hK hμ hν hπ).aestronglyMeasurable⟩

end OTSelector.Reconstruction

end
