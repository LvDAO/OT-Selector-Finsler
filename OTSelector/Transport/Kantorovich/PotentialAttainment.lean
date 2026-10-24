import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.Transport.Coupling.Embedding
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.OptimalPotentialCompactness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.OptimalPotentialCompactness`; the selected original proof blocks follow. -/
section

/-!
Conditions: Probability laws on a compact metric space, or laws supported on a common compact carrier; normalization at an indicated point.

Objects: A maximizing normalized one-Lipschitz potential and a potential attaining the Wasserstein-1 coupling infimum.

Proof detail: Use Arzelà–Ascoli for compactness, continuity of integration for attainment and Kantorovich–Rubinstein duality for the value; pull back a compact carrier and extend by McShane.

Sources: Terence Tao, Section 1.8, Theorem 1.8.23 and proof, pp. 114–115 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=123); Gabriel Peyré, Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110); Terence Tao, Section 1.10, Exercise 1.10.8, p. 139 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=148).
Relation: Classical compactness/duality argument with subtype coupling transport and global extension adapters proved locally.
-/

/-!
# Attainment of the Lipschitz potential objective on compact carriers

The normalized one-Lipschitz family is genuinely compact in the uniform norm.
The difference of its two probability integrals therefore attains its maximum.
The existing verified Kantorovich--Rubinstein duality then identifies this maximum
with the infimum of the original extended-distance costs over all couplings.
-/

open Set Metric MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace OTSelector.Geometry

variable {E : Type*} [MetricSpace E] [CompactSpace E]

/-- One-Lipschitz real potentials normalized at the designated carrier point. -/
def normalizedLipschitzPotentials (x₀ : E) : Set (E →ᵇ ℝ) :=
  {f | LipschitzWith 1 f ∧ f x₀ = 0}

/-- Normalized one-Lipschitz potentials on a compact carrier form a compact set in the
uniform topology. No compactness or maximizing-sequence hypothesis is supplied. -/
theorem isCompact_normalizedLipschitzPotentials (x₀ : E) :
    IsCompact (normalizedLipschitzPotentials x₀) := by
  have hclosed : IsClosed (normalizedLipschitzPotentials x₀) := by
    have heq : normalizedLipschitzPotentials x₀ =
        (⋂ (x) (y), {f : E →ᵇ ℝ | dist (f x) (f y) ≤ dist x y}) ∩
          {f : E →ᵇ ℝ | f x₀ = 0} := by
      ext f
      simp [normalizedLipschitzPotentials, lipschitzWith_iff_dist_le_mul]
    rw [heq]
    refine (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_).inter
      (isClosed_eq (continuous_eval_const x₀) continuous_const)
    exact isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y))
      continuous_const
  apply BoundedContinuousFunction.arzela_ascoli₂
    (closedBall (0 : ℝ) (diam (univ : Set E))) (isCompact_closedBall _ _)
    (normalizedLipschitzPotentials x₀) hclosed
  · intro f x hf
    apply mem_closedBall.mpr
    calc
      dist (f x) 0 = dist (f x) (f x₀) := by rw [hf.2]
      _ ≤ dist x x₀ := by simpa using hf.1.dist_le_mul x x₀
      _ ≤ diam (univ : Set E) :=
        dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ x₀)
  · apply Metric.equicontinuous_of_continuity_modulus id (by simpa using Filter.tendsto_id)
    intro x y f
    simpa using f.property.1.dist_le_mul x y

variable [MeasurableSpace E] [OpensMeasurableSpace E]

omit [CompactSpace E] in
/-- On a probability measure, integration of bounded continuous real functions is
one-Lipschitz for their uniform distance. -/
theorem lipschitzWith_integral_potential (μ : Measure E) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (fun f : E →ᵇ ℝ ↦ ∫ x, f x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← integral_sub (f.integrable μ) (g.integrable μ)]
  exact (f - g).norm_integral_le_norm μ

/-- The actual difference of two probability integrals attains its maximum among all
one-Lipschitz potentials on a compact carrier; the maximizing potential is normalized. -/
theorem exists_maximizing_lipschitz_potential (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x₀ : E) :
    ∃ f : E → ℝ, LipschitzWith 1 f ∧ f x₀ = 0 ∧
      ∀ g : E → ℝ, LipschitzWith 1 g →
        (∫ x, g x ∂ν) - (∫ x, g x ∂μ) ≤ (∫ x, f x ∂ν) - (∫ x, f x ∂μ) := by
  have hne : (normalizedLipschitzPotentials x₀).Nonempty :=
    ⟨0, (LipschitzWith.const 0).weaken zero_le, rfl⟩
  have hcont : Continuous (fun f : E →ᵇ ℝ ↦ (∫ x, f x ∂ν) - (∫ x, f x ∂μ)) :=
    (lipschitzWith_integral_potential ν).continuous.sub
      (lipschitzWith_integral_potential μ).continuous
  obtain ⟨f, hf, hmax⟩ := (isCompact_normalizedLipschitzPotentials x₀).exists_isMaxOn
    hne hcont.continuousOn
  refine ⟨f, hf.1, hf.2, fun g hg ↦ ?_⟩
  let g' : E →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨g, hg.continuous⟩
  let k : E →ᵇ ℝ := g' - BoundedContinuousFunction.const E (g x₀)
  have hk : k ∈ normalizedLipschitzPotentials x₀ := by
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (g x - g x₀) (g y - g x₀) ≤ (1 : ℝ≥0) * dist x y
      simpa only [dist_sub_right] using hg.dist_le_mul x y
    · change g x₀ - g x₀ = 0
      exact sub_self _
  have h := hmax hk
  change (∫ x, g x - g x₀ ∂ν) - (∫ x, g x - g x₀ ∂μ) ≤ _ at h
  have hgν : Integrable g ν := g'.integrable ν
  have hgμ : Integrable g μ := g'.integrable μ
  simpa [integral_sub hgν (integrable_const _),
    integral_sub hgμ (integrable_const _)] using h

/-- On a compact metric Borel carrier, the actual coupling-cost infimum equals the
integral difference of a constructed normalized one-Lipschitz potential. Compactness
constructs the maximizer and the verified coupling duality identifies its value. -/
theorem exists_optimal_lipschitz_potential [BorelSpace E] (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x₀ : E) :
    ∃ f : E → ℝ, LipschitzWith 1 f ∧ f x₀ = 0 ∧
      0 ≤ (∫ x, f x ∂ν) - (∫ x, f x ∂μ) ∧
      ENNReal.ofReal ((∫ x, f x ∂ν) - (∫ x, f x ∂μ)) =
        Vlasov.wasserstein1Coupling μ ν := by
  obtain ⟨f, hf, hzero, hmax⟩ := exists_maximizing_lipschitz_potential μ ν x₀
  have hnonneg : 0 ≤ (∫ x, f x ∂ν) - (∫ x, f x ∂μ) := by
    simpa using hmax (fun _ ↦ 0) ((LipschitzWith.const 0).weaken zero_le)
  refine ⟨f, hf, hzero, hnonneg, ?_⟩
  have hdual : Vlasov.wasserstein1 ν μ =
      ENNReal.ofReal ((∫ x, f x ∂ν) - (∫ x, f x ∂μ)) := by
    rw [Vlasov.wasserstein1_eq_iSup_lipschitz]
    apply le_antisymm
    · exact iSup_le fun g ↦ iSup_le fun hg ↦ ENNReal.ofReal_le_ofReal (hmax g hg)
    · exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
  let d : E →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y ↦ dist y x₀, continuous_id.dist continuous_const⟩
  rw [← hdual, Vlasov.wasserstein1_comm]
  exact Vlasov.wasserstein1_eq_coupling μ ν x₀ (d.integrable μ) (d.integrable ν)

section Ambient

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
private theorem couplingInf_subtype {K : Set M} (hK : MeasurableSet K)
    {μ ν : Measure M} (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K) :
    Vlasov.wasserstein1Coupling (μ.comap ((↑) : K → M))
        (ν.comap ((↑) : K → M)) = Vlasov.wasserstein1Coupling μ ν := by
  have hcost (π : Measure (K × K)) :
      (∫⁻ z, edist z.1 z.2 ∂π.map (Prod.map ((↑) : K → M) ((↑) : K → M))) =
        ∫⁻ z, edist z.1 z.2 ∂π := by
    rw [((MeasurableEmbedding.subtype_coe hK).prodMap
      (MeasurableEmbedding.subtype_coe hK)).lintegral_map]
    rfl
  unfold Vlasov.wasserstein1Coupling
  apply le_antisymm
  · refine le_iInf fun κ ↦ le_iInf fun hκ ↦ ?_
    obtain ⟨π, ⟨hπ, hmap⟩, _⟩ :=
      OTSelector.Reconstruction.existsUnique_subtype_coupling_lift hK hK hμ hν hκ
    apply iInf_le_of_le π
    apply iInf_le_of_le hπ
    rw [← hmap, hcost]
  · refine le_iInf fun π ↦ le_iInf fun hπ ↦ ?_
    have hm := hπ.map ((↑) : K → M) ((↑) : K → M)
      measurable_subtype_coe measurable_subtype_coe
    rw [OTSelector.Reconstruction.map_comap_subtype_of_ae_mem hK hμ,
      OTSelector.Reconstruction.map_comap_subtype_of_ae_mem hK hν] at hm
    exact iInf_le_of_le _ (iInf_le_of_le hm (le_of_eq (hcost π)))

/-- Compactly carried probabilities on the original ambient metric space admit a global
one-Lipschitz potential attaining their original distance transport cost. The carrier
uses the restricted ambient distance; no compactness of the ambient space is assumed. -/
theorem exists_optimal_lipschitz_potential_of_compact_carrier
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set M} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (hν : ∀ᵐ x ∂ν, x ∈ K) (x₀ : K) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f x₀ = 0 ∧
      0 ≤ (∫ x, f x ∂ν) - (∫ x, f x ∂μ) ∧
      ENNReal.ofReal ((∫ x, f x ∂ν) - (∫ x, f x ∂μ)) =
        Vlasov.wasserstein1Coupling μ ν := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μK : Measure K := μ.comap ((↑) : K → M)
  let νK : Measure K := ν.comap ((↑) : K → M)
  have hμmap : μK.map ((↑) : K → M) = μ :=
    OTSelector.Reconstruction.map_comap_subtype_of_ae_mem hK.measurableSet hμ
  have hνmap : νK.map ((↑) : K → M) = ν :=
    OTSelector.Reconstruction.map_comap_subtype_of_ae_mem hK.measurableSet hν
  have : IsProbabilityMeasure (μK.map ((↑) : K → M)) := hμmap ▸ inferInstance
  have : IsProbabilityMeasure (νK.map ((↑) : K → M)) := hνmap ▸ inferInstance
  have : IsProbabilityMeasure μK := Measure.isProbabilityMeasure_of_map ((↑) : K → M)
  have : IsProbabilityMeasure νK := Measure.isProbabilityMeasure_of_map ((↑) : K → M)
  obtain ⟨f, hf, hzero, hnonneg, hvalue⟩ := exists_optimal_lipschitz_potential μK νK x₀
  let f₀ : M → ℝ := fun x ↦ if hx : x ∈ K then f ⟨x, hx⟩ else 0
  have hf₀ : LipschitzOnWith 1 f₀ K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [f₀, dite_eq_left hx, dite_eq_left hy, Subtype.dist_eq] using
      hf.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, hg, heq⟩ := hf₀.extend_real
  have hgf (x : K) : g x = f x := by
    simpa only [f₀, dite_eq_left x.property] using (heq x.property).symm
  have hμint : (∫ x, g x ∂μ) = ∫ x, f x ∂μK := by
    rw [← hμmap, (MeasurableEmbedding.subtype_coe hK.measurableSet).integral_map]
    exact integral_congr_ae (Filter.Eventually.of_forall hgf)
  have hνint : (∫ x, g x ∂ν) = ∫ x, f x ∂νK := by
    rw [← hνmap, (MeasurableEmbedding.subtype_coe hK.measurableSet).integral_map]
    exact integral_congr_ae (Filter.Eventually.of_forall hgf)
  refine ⟨g, hg, (hgf x₀).trans hzero, ?_, ?_⟩
  · simpa only [hμint, hνint] using hnonneg
  · rw [hμint, hνint, hvalue]
    exact couplingInf_subtype hK.measurableSet hμ hν

end Ambient
end OTSelector.Geometry

end
