import OTSelector.Reconstruction.FinslerIntrinsicActiveNullLabel
import OTSelector.Geometry.Finsler.Calibration.GeometricDisintegration

/-!
# Transport construction of the intrinsic active ray geometry

This module supplies the geometric interface of
FinslerIntrinsicActiveNullLabel.lean from the constructed Finsler data, closing
the remaining geometric input of the structural invariance theorem
(main.tex:958).

## The geometry on the full-marginal regular domain

The Finsler geometric disintegration of FinslerGeometricDisintegration.lean
constructs one optimal potential `u` (the ray clock), a measurable regular
domain `N = F.potentialRegularDomain u` conull for both original probabilities,
and measurable labels `a : M → (ℚ → M)` from the rational curve codes of the
minimal calibrated arcs, with the two properties

* `(a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y` on `N`, and
* injectivity of `x ↦ (a x, u x)` on `N`.

Hence the label is constant on calibrated pairs *within* the full-marginal
domain `N`: `u y - u x = dist x y` implies `a x = a y`.  Locality outside `N`
is not asserted by the geometric construction (it is only needed on pairs that
carry mass, which are a.e. in `N`); we therefore record the interface with the
locality restricted to `N` as `IntrinsicActiveRayGeometryOn`, prove the wiring
theorem for it, and provide the upgrade `toGeometry` to the global interface
`IntrinsicActiveRayGeometry` under the (unnecessary for the wiring) global
locality hypothesis.

## Contents

* `IntrinsicActiveRayGeometryOn`: the interface with locality on a measurable
  full-marginal set `N`;
* `IntrinsicActiveRayGeometryOn.toGeometry`: upgrade to the global interface;
* `exists_block_matching_of_geometryOn`: the wiring theorem (conull-set
  null-label modification plus global injective block matching) for the
  restricted interface;
* `exists_intrinsicActiveRayGeometryOn_of_finsler`: the transport construction
  of the interface from the Finsler hypotheses;
* `exists_block_matching_of_finsler_face`: the composed statement, from the
  Finsler hypotheses to the block matching, with the ray data supplied by the
  optimal-face conditional couplings.

Remaining sub-gap: the component-cover hypothesis `IsComponentCover` (the
paper's cover identity `eq:intrinsic-active-cover` together with the
minimal-arc transport) is not constructed from the geometric data and remains
an explicit hypothesis; the paper's absolute-continuity of the conditional laws
is not used here.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The intrinsic active ray geometry on a full-marginal regular domain.**  The
constructed optimal potential (ray clock) and measurable label maps, with the
locality of the label on calibrated pairs *within the full-marginal set* `N`. -/
structure IntrinsicActiveRayGeometryOn (M Z : Type*) [MetricSpace M] [MeasurableSpace M]
    [MeasurableSpace Z] (N : Set M) where
  /-- The constructed optimal potential, used as the ray clock. -/
  potential : M → ℝ
  /-- First-label map (whole-ray label of the first marginal). -/
  labelFirst : M → Z
  /-- Second-label map (whole-ray label of the second marginal). -/
  labelSecond : M → Z
  measurable_labelFirst : Measurable labelFirst
  measurable_labelSecond : Measurable labelSecond
  measurable_potential : Measurable potential
  /-- The full-marginal regular domain is measurable. -/
  measurable_fullMarginal : MeasurableSet N
  /-- Locality of the whole-ray label on calibrated pairs of the full-marginal
  domain. -/
  label_constant_on_calibrated :
    ∀ ⦃x y : M⦄, x ∈ N → y ∈ N → potential y - potential x = dist x y →
      labelFirst x = labelSecond y

/-- Upgrade the restricted interface to the global one, under the (for the
wiring unused) global locality hypothesis. -/
def IntrinsicActiveRayGeometryOn.toGeometry {M Z : Type*} [MetricSpace M]
    [MeasurableSpace M] [MeasurableSpace Z] {N : Set M}
    (G : IntrinsicActiveRayGeometryOn M Z N)
    (hloc : ∀ ⦃x y : M⦄, G.potential y - G.potential x = dist x y →
      G.labelFirst x = G.labelSecond y) :
    IntrinsicActiveRayGeometry M Z where
  potential := G.potential
  labelFirst := G.labelFirst
  labelSecond := G.labelSecond
  measurable_labelFirst := G.measurable_labelFirst
  measurable_labelSecond := G.measurable_labelSecond
  measurable_potential := G.measurable_potential
  label_constant_on_calibrated := hloc

/-- **Wiring theorem for the restricted interface.**  Consuming the geometry on
the full-marginal domain and the face-disintegration hypotheses (two optimal
plans as conditional mixtures over the labels, with the a.e. conditional-coupling
property), there is a conull label set `S` such that the two surpluses and their
positivity sets agree on `S`, the second ray data modified only on the null label
set `Sᶜ` admits the injective block matching with the first, and the modification
leaves the surplus unchanged off `S`. -/
theorem exists_block_matching_of_geometryOn {M Z : Type*} [MetricSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]
    {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : Set M} (G : IntrinsicActiveRayGeometryOn M Z N)
    (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ₁ z)
      (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z))
    (h₂ : ∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ₂ z)
      (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z))
    (A B : IntrinsicActiveRayData Z)
    (hAflux : ∀ z : Z, A.flux z = rayFlux (rayCoupling (κ₁ z) G.potential))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (rayCoupling (κ₂ z) G.potential))
    (hA : IsComponentCover A) (hB : IsComponentCover B) :
    ∃ (S : Set Z) (T : Z → ℕ → ℕ),
      (μ.map G.labelFirst) Sᶜ = 0 ∧
      (∀ z ∈ S, A.flux z = B.flux z) ∧
      (∀ z ∈ S, ∀ r : ℝ, 0 < A.flux z r ↔ 0 < B.flux z r) ∧
      (∀ z j, A.block z j = (nullLabelModification A B S).block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) ∧
      (∀ z ∉ S, (nullLabelModification A B S).flux z = A.flux z) := by
  obtain ⟨S, hS, hfluxS, hposS⟩ := exists_conull_flux_agree_set (u := G.potential)
    G.measurable_potential κ₁ κ₂ h₁ h₂ A B hAflux hBflux
  obtain ⟨T, hT, hinj⟩ := exists_block_matching_nullLabel A B S hposS hA hB
  exact ⟨S, T, hS, hfluxS, hposS, hT, hinj,
    fun z hz => nullLabelModification_flux_of_notMem hz⟩

/-! ## The transport construction from the Finsler data -/

section FinslerConstruction

open Manifold OTSelector.Geometry
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Geometry.ContinuousFinslerNorm E M}

/-- **Transport construction of the intrinsic active ray geometry.**  From the
constructed Finsler data (complete smooth reversible strongly convex norm,
chartwise absolutely continuous original probabilities, disjoint compactly
carried supports) we obtain: one optimal potential `u` used as the ray clock, a
measurable full-marginal regular domain `N` conull for both probabilities, and
measurable labels `a : M → (ℚ → M)` of the minimal calibrated arcs such that
the whole-ray label is constant on calibrated pairs of `N`, the two label laws
balance, and the whole optimal face is described by the actual conditional
couplings of the original conditional marginals. -/
theorem exists_intrinsicActiveRayGeometryOn_of_finsler (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instTransportStatementMetric : MetricSpace M := F.metricSpace
    let _instTransportStatementProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instTransportStatementBorel : StandardBorelSpace M := inferInstance
    let _instTransportStatementNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
    ∃ (N : Set M) (G : IntrinsicActiveRayGeometryOn M (ℚ → M) N),
      LipschitzWith 1 G.potential ∧ MeasurableSet N ∧ μ Nᶜ = 0 ∧ ν Nᶜ = 0 ∧
      (∀ x ∈ N, ∀ y ∈ N,
        (G.labelFirst x = G.labelSecond y ∧ G.potential x ≤ G.potential y) ↔
          G.potential y - G.potential x = dist x y) ∧
      (∀ x ∈ N, ∀ y ∈ N, G.potential y - G.potential x = dist x y →
        G.labelFirst x = G.labelSecond y) ∧
      μ.map G.labelFirst = ν.map G.labelSecond ∧
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ κ : Kernel (ℚ → M) (M × M), IsMarkovKernel κ ∧
          κ ∘ₘ μ.map G.labelFirst = π ∧
          ∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ z)
            (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z) ∧
            ∀ᵐ p ∂κ z, p.1 ∈ N ∧ p.2 ∈ N ∧
              G.labelFirst p.1 = G.labelSecond p.2 ∧
              G.potential p.1 ≤ G.potential p.2 := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : StandardBorelSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hdisint⟩ :=
    exists_finsler_geometric_disintegration hF hcomplete m μ ν hμchart hνchart
      hA hB hAB hμ hν
  have hloc : ∀ ⦃x y : M⦄, x ∈ F.potentialRegularDomain u →
      y ∈ F.potentialRegularDomain u → u y - u x = dist x y → a x = a y := by
    intro x y hx hy hcal
    have hle : u x ≤ u y := by
      rw [← sub_nonneg, hcal]
      exact dist_nonneg
    exact ((horder x hx y hy).mpr hcal).1
  have hμN0 : μ (F.potentialRegularDomain u)ᶜ = 0 := by
    have h : μ {x : M | ¬ x ∈ F.potentialRegularDomain u} = 0 :=
      MeasureTheory.ae_iff.mp hμN
    have hset : (F.potentialRegularDomain u)ᶜ
        = {x : M | ¬ x ∈ F.potentialRegularDomain u} := by
      ext x
      simp
    rw [hset]
    exact h
  have hνN0 : ν (F.potentialRegularDomain u)ᶜ = 0 := by
    have h : ν {y : M | ¬ y ∈ F.potentialRegularDomain u} = 0 :=
      MeasureTheory.ae_iff.mp hνN
    have hset : (F.potentialRegularDomain u)ᶜ
        = {y : M | ¬ y ∈ F.potentialRegularDomain u} := by
      ext y
      simp
    rw [hset]
    exact h
  have hloc' : ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      u y - u x = dist x y → a x = a y :=
    fun x hx y hy hcal => hloc hx hy hcal
  refine ⟨F.potentialRegularDomain u,
    ⟨u, a, a, ha, ha, hu.continuous.measurable, hN, hloc⟩,
    hu, hN, hμN0, hνN0, horder, hloc', hbalance, ?_⟩
  exact hdisint

/-- **From the Finsler data to the active-block matching.**  Composed form of the
transport construction and the wiring theorem: the Finsler hypotheses supply the
intrinsic active ray geometry `G` on the full-marginal regular domain, and for
any two optimal plans' conditional scalar couplings (kernels with the a.e.
conditional-coupling property) and any ray data whose surpluses are the
corresponding rayFluxes in the constructed potential clock, the conull-set
null-label modification and the global injective block matching hold. -/
theorem exists_block_matching_of_finsler_face (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instTransportFinalMetric : MetricSpace M := F.metricSpace
    let _instTransportFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instTransportFinalBorel : StandardBorelSpace M := inferInstance
    let _instTransportFinalNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
    ∃ (N : Set M) (G : IntrinsicActiveRayGeometryOn M (ℚ → M) N),
      LipschitzWith 1 G.potential ∧ MeasurableSet N ∧ μ Nᶜ = 0 ∧ ν Nᶜ = 0 ∧
      (∀ x ∈ N, ∀ y ∈ N,
        (G.labelFirst x = G.labelSecond y ∧ G.potential x ≤ G.potential y) ↔
          G.potential y - G.potential x = dist x y) ∧
      (∀ x ∈ N, ∀ y ∈ N, G.potential y - G.potential x = dist x y →
        G.labelFirst x = G.labelSecond y) ∧
      μ.map G.labelFirst = ν.map G.labelSecond ∧
      (∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ κ : Kernel (ℚ → M) (M × M), IsMarkovKernel κ ∧
          κ ∘ₘ μ.map G.labelFirst = π ∧
          ∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ z)
            (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z) ∧
            ∀ᵐ p ∂κ z, p.1 ∈ N ∧ p.2 ∈ N ∧
              G.labelFirst p.1 = G.labelSecond p.2 ∧
              G.potential p.1 ≤ G.potential p.2) ∧
      ∀ (κ₁ κ₂ : Kernel (ℚ → M) (M × M)),
        (∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ₁ z)
          (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z)) →
        (∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ₂ z)
          (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z)) →
        ∀ (D₁ D₂ : IntrinsicActiveRayData (ℚ → M)),
          (∀ z : ℚ → M, D₁.flux z = rayFlux (rayCoupling (κ₁ z) G.potential)) →
          (∀ z : ℚ → M, D₂.flux z = rayFlux (rayCoupling (κ₂ z) G.potential)) →
          IsComponentCover D₁ → IsComponentCover D₂ →
          ∃ (S : Set (ℚ → M)) (T : (ℚ → M) → ℕ → ℕ),
            (μ.map G.labelFirst) Sᶜ = 0 ∧
            (∀ z ∈ S, D₁.flux z = D₂.flux z) ∧
            (∀ z ∈ S, ∀ r : ℝ, 0 < D₁.flux z r ↔ 0 < D₂.flux z r) ∧
            (∀ z j, D₁.block z j = (nullLabelModification D₁ D₂ S).block z (T z j)) ∧
            (∀ z j k, T z j = T z k → j = k) ∧
            (∀ z ∉ S, (nullLabelModification D₁ D₂ S).flux z = D₁.flux z) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : StandardBorelSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨N, G, hu, hN, hμN, hνN, horder, hloc, hbalance, hdisint⟩ :=
    exists_intrinsicActiveRayGeometryOn_of_finsler hF hcomplete m μ ν hμchart hνchart
      hA hB hAB hμ hν
  refine ⟨N, G, hu, hN, hμN, hνN, horder, hloc, hbalance, hdisint, ?_⟩
  intro κ₁ κ₂ h₁ h₂ D₁ D₂ hf₁ hf₂ hc₁ hc₂
  exact exists_block_matching_of_geometryOn G κ₁ κ₂ h₁ h₂ D₁ D₂ hf₁ hf₂ hc₁ hc₂

end FinslerConstruction

end OTSelector.Reconstruction