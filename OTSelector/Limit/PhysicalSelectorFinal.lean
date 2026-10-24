import OTSelector.Limit.FinslerPressureUpperBound
import OTSelector.Limit.SupportedEmpiricalSelector
import OTSelector.Probability.RandomSetWeakConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Physical selector endpoint: carrier plans and the paper's conclusion

This module contains the final glue for passing from the ambient selector endpoint,
whose plans live on `M × M`, to the paper's conclusion for plans on two carriers
`A × B`.

The ambient empirical optimal face is monomorphic: `Pressure.empiricalOptimalFace X Y`
requires `X` and `Y` to have the same type, and `IsOptimalCoupling edist` requires both
marginal spaces to agree.  Consequently the cross-carrier objects here use

* `carrierEmpiricalFace X Y`, the set of optimal couplings of the empirical measures of
  `X : Fin n → A` and `Y : Fin n → B` for the cost `(x, y) ↦ edist (x : M) (y : M)`;
* `fun x y ↦ edist (x : M) (y : M)` in place of bare `edist`.

The main results are:

* `image_empiricalOptimalFace_subtype_prod`: pushforward by the product inclusion maps the
  entire cross-carrier empirical optimal face onto the ambient empirical optimal face.
  This is the paper-literal face identification behind the final transport.
* `isEmbedding_probabilityMeasure_map_subtype_prod`: pushforward of probability measures by
  the inclusion of a product of compact carriers is a topological embedding.  The proof
  composes the embedding of `ProbabilityMeasure` into `FiniteMeasure` with mathlib's
  closed-embedding pushforward embedding for finite measures.
* `tendsto_measureReal_exists_notMem_of_face_embedding`: outer-probability convergence of an
  ambient random face implies the same statement for the carrier-level face, for every
  neighborhood.  No measurability of the faces is required.

With these, the remaining construction of the physical `A × B` selector is: pull the ambient
selector back along the subtype inclusion, identify the two random faces almost everywhere on
the full-carrier event, and apply `tendsto_measureReal_exists_metric_le_of_forall_nhds`.
-/

open MeasureTheory Set Filter Topology
open scoped Topology ENNReal BoundedContinuousFunction

noncomputable section

namespace OTSelector.Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M]

/-- The empirical optimal face for source and target samples in two possibly different
carriers `A` and `B`.  The cost is the ambient distance between the images in `M`.

`Pressure.empiricalOptimalFace` is the special case `A = B = M`; it cannot be applied
directly to two different carrier types because its two sample families are required to
have a common type. -/
def carrierEmpiricalFace {A B : Set M} {n : ℕ} (X : Fin n → A) (Y : Fin n → B) :
    Set (ProbabilityMeasure (A × B)) :=
  {γ | IsOptimalCoupling (fun (x : A) (y : B) => edist (x : M) (y : M))
    (empiricalMeasure X) (empiricalMeasure Y) (γ : Measure (A × B))}

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
/-- Pushforward by the product inclusion maps the entire cross-carrier empirical optimal
face onto the ambient empirical optimal face.  Repeated observations are allowed; the
statement concerns the whole fractional face, with no measurable selection of an optimizer.

This is the two-carrier version of `image_empiricalOptimalFace_subtype`.  The left-hand side
uses `carrierEmpiricalFace` because `Pressure.empiricalOptimalFace` requires a common sample
type. -/
theorem image_empiricalOptimalFace_subtype_prod
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {n : Nat} [NeZero n] (X : Fin n -> A) (Y : Fin n -> B) :
    (fun π : ProbabilityMeasure (A × B) =>
      π.map ((MeasurableEmbedding.subtype_coe hA).measurable.prodMap
        (MeasurableEmbedding.subtype_coe hB).measurable).aemeasurable) ''
      carrierEmpiricalFace X Y =
    Pressure.empiricalOptimalFace (fun i => (X i : M)) (fun i => (Y i : M)) := by
  have h := image_optimalProbabilityCouplings_embedding
    (MeasurableEmbedding.subtype_coe hA) (MeasurableEmbedding.subtype_coe hB)
    (fun (x : A) (y : B) => edist (x : M) (y : M)) edist (fun _ _ => rfl)
    (empiricalProbabilityMeasure X) (empiricalProbabilityMeasure Y)
  simpa only [carrierEmpiricalFace, Pressure.empiricalOptimalFace,
    empiricalProbabilityMeasure_toMeasure,
    map_empiricalMeasure _ _ measurable_subtype_coe, Function.comp_def] using h

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ProperSpace M]

/-- Pushforward of probability measures by the inclusion of a product of compact carriers
is a topological embedding.

The proof composes the embedding `ProbabilityMeasure → FiniteMeasure` with mathlib's
`IsClosedEmbedding.isEmbedding_map_finiteMeasure`.  Properness supplies second countability
of the ambient space, hence the Borel and normal-space instances needed for the product. -/
theorem isEmbedding_probabilityMeasure_map_subtype_prod
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) :
    IsEmbedding (fun π : ProbabilityMeasure (A × B) =>
      π.map ((MeasurableEmbedding.subtype_coe hA.measurableSet).measurable.prodMap
        (MeasurableEmbedding.subtype_coe hB.measurableSet).measurable).aemeasurable) := by
  let incl : A × B → M × M := Prod.map ((↑) : A → M) ((↑) : B → M)
  have hincl_cont : Continuous incl := continuous_subtype_val.prodMap continuous_subtype_val
  have hincl_meas : Measurable incl :=
    (measurable_subtype_coe.prodMap measurable_subtype_coe)
  have hceA : IsClosedEmbedding ((↑) : A → M) := hA.isClosed.isClosedEmbedding_subtypeVal
  have hceB : IsClosedEmbedding ((↑) : B → M) := hB.isClosed.isClosedEmbedding_subtypeVal
  have hce : IsClosedEmbedding incl := hceA.prodMap hceB
  have hE' : IsEmbedding (fun μ : FiniteMeasure (A × B) => μ.map incl) :=
    FiniteMeasure.Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure incl hce
  have hTA : IsEmbedding (ProbabilityMeasure.toFiniteMeasure (Ω := A × B)) :=
    ProbabilityMeasure.toFiniteMeasure_isEmbedding _
  have hcomp : IsEmbedding (fun ν : ProbabilityMeasure (A × B) =>
      (ProbabilityMeasure.toFiniteMeasure ν).map incl) := hE'.comp hTA
  have hsq : (fun ν : ProbabilityMeasure (A × B) =>
      ProbabilityMeasure.toFiniteMeasure (ν.map hincl_meas.aemeasurable)) =
      (fun ν : ProbabilityMeasure (A × B) =>
        (ProbabilityMeasure.toFiniteMeasure ν).map incl) := by
    funext ν
    apply FiniteMeasure.toMeasure_injective
    rfl
  have hcompΦ : IsEmbedding (fun ν : ProbabilityMeasure (A × B) =>
      ProbabilityMeasure.toFiniteMeasure (ν.map hincl_meas.aemeasurable)) := by
    rw [hsq]
    exact hcomp
  have hcontΦ : Continuous (fun ν : ProbabilityMeasure (A × B) =>
      ν.map hincl_meas.aemeasurable) := ProbabilityMeasure.continuous_map hincl_cont
  have hTM : Continuous (ProbabilityMeasure.toFiniteMeasure (Ω := M × M)) :=
    (ProbabilityMeasure.toFiniteMeasure_isEmbedding (M × M)).continuous
  exact IsEmbedding.of_comp hcontΦ hTM hcompΦ

end OTSelector.Reconstruction

namespace OTSelector

/-- Pushforward of entire random faces along a topological embedding transports the outer
probability of escaping every neighborhood.  No measurability of the random faces is
required, and the source filter is `atTop` on the sample-size index.

If the ambient face `G n ω` is the image of the carrier face `F n ω` almost everywhere and
the ambient faces converge in outer probability to `y₀ = Φ x₀`, then the carrier faces
converge in the same sense to `x₀`. -/
theorem tendsto_measureReal_exists_notMem_of_face_embedding
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Φ : X → Y) (hΦ : IsEmbedding Φ) {x₀ : X} {y₀ : Y} (hΦx : Φ x₀ = y₀)
    (F : ∀ n, Ω n → Set X) (G : ∀ n, Ω n → Set Y)
    (hFG : ∀ n, ∀ᵐ ω ∂(P n), Φ '' F n ω = G n ω)
    (hG : ∀ V ∈ 𝓝 y₀, Tendsto (fun n ↦ (P n).real
      {ω | ∃ κ ∈ G n ω, κ ∉ V}) atTop (𝓝 0)) :
    ∀ U ∈ 𝓝 x₀, Tendsto (fun n ↦ (P n).real
      {ω | ∃ γ ∈ F n ω, γ ∉ U}) atTop (𝓝 0) := by
  intro U hU
  have hU' : U ∈ comap Φ (𝓝 (Φ x₀)) := by
    rw [← hΦ.isInducing.nhds_eq_comap x₀]
    exact hU
  rw [hΦx] at hU'
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hG V hV)
    (fun n ↦ measureReal_nonneg) (fun n ↦ ?_)
  have hsub : {ω | ∃ γ ∈ F n ω, γ ∉ U} ∩ {ω | Φ '' F n ω = G n ω} ⊆
      {ω | ∃ κ ∈ G n ω, κ ∉ V} := by
    rintro ω ⟨⟨γ, hγF, hγU⟩, hface⟩
    refine ⟨Φ γ, ?_, ?_⟩
    · rw [← hface]
      exact Set.mem_image_of_mem Φ hγF
    · intro hmem
      exact hγU (hVU hmem)
  have hGc : (P n).real {ω | ¬ (Φ '' F n ω = G n ω)} = 0 := by
    rw [measureReal_eq_zero_iff]
    exact ae_iff.mp (hFG n)
  have hE_sub : {ω | ∃ γ ∈ F n ω, γ ∉ U} ⊆
      ({ω | ∃ γ ∈ F n ω, γ ∉ U} ∩ {ω | Φ '' F n ω = G n ω}) ∪
        {ω | ¬ (Φ '' F n ω = G n ω)} := by
    intro ω hω
    by_cases h : Φ '' F n ω = G n ω
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr h
  calc (P n).real {ω | ∃ γ ∈ F n ω, γ ∉ U}
      ≤ (P n).real (({ω | ∃ γ ∈ F n ω, γ ∉ U} ∩ {ω | Φ '' F n ω = G n ω}) ∪
          {ω | ¬ (Φ '' F n ω = G n ω)}) := measureReal_mono hE_sub
    _ ≤ (P n).real ({ω | ∃ γ ∈ F n ω, γ ∉ U} ∩ {ω | Φ '' F n ω = G n ω}) +
          (P n).real {ω | ¬ (Φ '' F n ω = G n ω)} := measureReal_union_le _ _
    _ = (P n).real ({ω | ∃ γ ∈ F n ω, γ ∉ U} ∩ {ω | Φ '' F n ω = G n ω}) := by
        rw [hGc, add_zero]
    _ ≤ (P n).real {ω | ∃ κ ∈ G n ω, κ ∉ V} := measureReal_mono hsub

end OTSelector
