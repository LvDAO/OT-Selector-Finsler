import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.LabelDisintegration
import OTSelector.Transport.Coupling.OptimalCalibration
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OptimalFaceDisintegration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OptimalFaceDisintegration`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OptimalFaceDisintegration

**Conditions:** Compactly carried probability marginals and measurable labels constant on calibrated pairs of a full-marginal Borel set; the required standard Borel structures are explicit.

**Objects:** One common calibrated potential and the whole original optimal face represented by conditional coupling kernels.

**Proof detail:** Construct a globally dual-attaining potential, disintegrate any calibrated coupling over its common label, and read conditional marginals; conversely mix calibrated conditional couplings to recover an optimal original plan.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110), Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (PDF pages 110–111); [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30), Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# The entire distance-optimal face over a measurable common-label relation

Compactly carried original probabilities determine an actual global optimal potential.
For any measurable full-marginal set and measurable labels constant on its calibrated
pairs, all original optimal plans are exactly the mixtures of forward calibrated
couplings of the original conditional marginals. The shared label marginal is derived,
not prescribed. Constructing the geometric labels and absolute continuity of their
conditional laws are separate tasks.
-/

open Set MeasureTheory ProbabilityTheory Filter

noncomputable section
namespace OTSelector.Reconstruction

variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]

/-- One constructed optimal potential describes the whole optimal face by actual
conditional couplings over every measurable label constant on calibrated pairs of a
full-marginal set. No optimal plan, potential, or balanced quotient law is an input. -/
theorem exists_optimal_face_disintegration_of_compact_carrier
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set M} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (hν : ∀ᵐ x ∂ν, x ∈ K) (x₀ : K) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f x₀ = 0 ∧
      ∀ (N : Set M), MeasurableSet N → (∀ᵐ x ∂μ, x ∈ N) → (∀ᵐ y ∂ν, y ∈ N) →
      ∀ (a b : M → Z), Measurable a → Measurable b →
      (∀ x ∈ N, ∀ y ∈ N, f y - f x = dist x y → a x = b y) →
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        μ.map a = ν.map b ∧ ∃ κ : Kernel Z (M × M), IsMarkovKernel κ ∧
          κ ∘ₘ μ.map a = π ∧ ∀ᵐ z ∂μ.map a,
            Vlasov.IsCoupling (κ z) (condDistrib id a μ z) (condDistrib id b ν z) ∧
              ∀ᵐ p ∂κ z, p.1 ∈ N ∧ p.2 ∈ N ∧ f p.2 - f p.1 = dist p.1 p.2 := by
  obtain ⟨f, hf, hzero, hopt⟩ :=
    exists_optimal_calibration_of_compact_carrier μ ν hK hμ hν x₀
  refine ⟨f, hf, hzero, ?_⟩
  intro N hN hμN hνN a b ha hb hlabel π
  let R : Set (M × M) := {p | p.1 ∈ N ∧ p.2 ∈ N ∧ f p.2 - f p.1 = dist p.1 p.2}
  have hR : MeasurableSet R := (measurable_fst hN).inter ((measurable_snd hN).inter
    (measurableSet_eq_fun
      ((hf.continuous.measurable.comp measurable_snd).sub
        (hf.continuous.measurable.comp measurable_fst))
      (continuous_fst.dist continuous_snd).measurable))
  have hiff : IsOptimalCoupling edist μ ν π ↔
      Vlasov.IsCoupling π μ ν ∧ ∀ᵐ p ∂π, p ∈ R := by
    constructor
    · intro hπ
      have hleft : ∀ᵐ p ∂π, p.1 ∈ N := ae_of_ae_map measurable_fst.aemeasurable
        (by rwa [hπ.1.1])
      have hright : ∀ᵐ p ∂π, p.2 ∈ N := ae_of_ae_map measurable_snd.aemeasurable
        (by rwa [hπ.1.2])
      refine ⟨hπ.1, ?_⟩
      filter_upwards [hleft, hright, (hopt π hπ.1).mp hπ] with p hp hq hcal
      exact ⟨hp, hq, hcal⟩
    · rintro ⟨hπ, hsupp⟩
      exact (hopt π hπ).mpr (hsupp.mono fun _ h ↦ h.2.2)
  exact hiff.trans (isCoupling_supported_iff_conditional_couplings ha hb hR
    (fun p hp ↦ hlabel p.1 hp.1 p.2 hp.2.1 hp.2.2))

end OTSelector.Reconstruction

end
end
