import OTSelector.Reconstruction.FinslerOriginalSceneCloudCountIdentity

/-!
# Coupling-side cardinality transport for the Palm scene-to-cloud count identity

This module attacks the last step of the scene-to-cloud count identity: the
transport of the scene's counted edge shells to the cloud's realized matching
cardinality along the Palm coupling.

## What is unconditional

For a scene that is a full original input matching:

1. sceneSupportEdgeIndex: the anchored edge index map, sending an occupied
   source input atom to its unique support edge (the edge anchored at it).  This
   is the edge index map of the scene.
2. sceneSupportEdgeIndex_injective and sceneSupportEdgeIndex_bijective: the map
   is injective, and a bijection onto the scene support subtype.  Hence the
   scene side needs no a.e. argument: its counted edges are indexed bijectively
   by occupied source atoms.
3. scene_shellSum_eq_edge_mass: the shell-cardinality sum
   sum over n of (sceneEdgeConfig hs n).card equals the scene edge total mass.

For the cloud side:

4. realizedPlanMass_eq_legalMaximumCard: the realized optimal plan mass of a
   cloud state is the maximum cardinality of its realized legal graph.
5. ae_realizedPlanMass_eq_minCount: unconditionally in the cloud law (given
   a.e. increasing clocks) this mass is min (mSourceCount w) (mTargetCount w).

## The exact remaining identification

The two sides live on DIFFERENT objects: the scene is a
LegalMarkedOptimalInputScene (edge measure plus coloured input measure) while
the cloud is a TwoMarkedCloudSpace (two counts plus two marked cube sequences).
In this library the scene law and the cloud law are related only through the
Palm/rooted constructions, and the Palm mark space PhysicalPairPalmMark does not
contain the scene edge measure or the cloud counts.  There is no coupling object
exposing the edge map, so the transport cannot be proved pointwise for an
arbitrary pair (s, w); it is exactly one named a.e. statement:

  PalmSceneCloudCouplingTransport hs alpha beta rho:
  for a.e. cloud state w under twoMarkedCloudLaw q R R alpha beta rho,
  sum over n of (sceneEdgeConfig hs n).card equals
  legalMaximumCard (legalMarkedGraph q (mSourceCount w) (mTargetCount w) id id w).

The module proves that this identification is EQUIVALENT to the pure
shell-cardinality identity PalmSceneCloudShellCardinalityIdentity (sum of shell
cards equals min (mSourceCount w) (mTargetCount w) a.e.), equivalent to a.e.
PalmSceneCloudMassTransfer, and that it implies a.e.
PalmSceneCloudCountTransfer.  Thus a proof of this single named a.e.
identification discharges the count identity; everything else is unconditional.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## The anchored edge index map of the scene -/

/-- **The anchored edge index map**: an occupied source input atom is sent to
the unique support edge anchored at it. -/
noncomputable def sceneSupportEdgeIndex {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    {x : LegalMarkedPhysicalPoint q //
      (s.2 : Measure (LegalColoredInputPoint q)) {(x, 0)} ≠ 0} →
      {e : LegalMarkedPhysicalEdge q //
        e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support} :=
  fun p => ⟨sceneSupportSourceFun hs p, sceneSupportSourceFun_mem_support hs p⟩

/-- **The anchored edge index map is injective** (unconditional; distinct
occupied source atoms give distinct support edges). -/
theorem sceneSupportEdgeIndex_injective {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    Function.Injective (sceneSupportEdgeIndex hs) :=
  (sceneSupportSourceFun_bijective hs).1

/-- **The anchored edge index map is a bijection onto the scene support**
(unconditional). -/
theorem sceneSupportEdgeIndex_bijective {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    Function.Bijective (sceneSupportEdgeIndex hs) :=
  sceneSupportSourceFun_bijective hs

/-- **Unconditional scene-side cardinality**: the shell-cardinality sum of the
representing configuration equals the scene edge total mass. -/
theorem scene_shellSum_eq_edge_mass {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) :
    (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ :=
  (scene_edge_totalMass hs).symm

/-- **Unconditional cloud-side cardinality**: the realized optimal plan mass of
a cloud state is the maximum cardinality of its realized legal graph. -/
theorem realizedPlanMass_eq_legalMaximumCard (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedOptimalPlan q L r kin g t ω Set.univ =
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞) :=
  legalMarkedOptimalPlan_univ q L r kin g t ω

/-- **Unconditional a.e. cloud-side cardinality**: for a.e. cloud state the
realized plan mass is the minimum of the cloud counts. -/
theorem ae_realizedPlanMass_eq_minCount (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      legalMarkedOptimalPlan q L r kin g t ω Set.univ =
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞) :=
  ae_legalMarkedOptimalPlan_univ_eq_min q L r kin g t α β ρ horder

/-! ## The isolated a.e. coupling identification -/

/-- **The single remaining a.e. coupling identification.**  Along the
Palm/cloud coupling, the scene's counted edge shells have the cardinality of the
realized legal matching of the cloud state.

Precise type: for a.e. w under twoMarkedCloudLaw q R R alpha beta rho,
the shell sum equals legalMaximumCard (legalMarkedGraph q (mSourceCount w)
(mTargetCount w) id id w).  A proof of this statement is the only missing input
of the scene-to-cloud count identity. -/
def PalmSceneCloudCouplingTransport {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (α β : Measure ℝ)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
    (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞)

/-- **The equivalent pure shell-cardinality form** of the isolated
identification: a.e. the scene's shell-cardinality sum is the minimum of the
cloud counts. -/
def PalmSceneCloudShellCardinalityIdentity {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (α β : Measure ℝ)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
    (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞)

/-- **The transport implies the a.e. shell-cardinality identity.** -/
theorem ae_shellSum_eq_min_of_couplingTransport
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2)
    (htransport : PalmSceneCloudCouplingTransport (q := q) hs α β ρ) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ≥0∞) := by
  filter_upwards [htransport,
    ae_legalMaximumCard_eq_min q α β ρ id id horder] with ω hω hcard
  rw [hω, hcard]

/-- **The isolated identification is equivalent to its shell-cardinality
form.** -/
theorem couplingTransport_iff_shellCardinalityIdentity
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2) :
    PalmSceneCloudCouplingTransport (q := q) hs α β ρ ↔
      PalmSceneCloudShellCardinalityIdentity (q := q) hs α β ρ := by
  constructor
  · exact ae_shellSum_eq_min_of_couplingTransport hs α β ρ horder
  · intro hmin
    show ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
        (PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞)
    filter_upwards [hmin,
      ae_legalMaximumCard_eq_min q α β ρ id id horder] with ω hminω hcard
    rw [hminω, hcard]

/-- **The isolated identification is equivalent to a.e. Palm mass transfer**
(the named hypothesis of the earlier reduction). -/
theorem couplingTransport_iff_ae_massTransfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) :
    PalmSceneCloudCouplingTransport (q := q) hs α β ρ ↔
      ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
        PalmSceneCloudMassTransfer L r kin g t s ω := by
  constructor
  · intro h
    show ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
        legalMarkedOptimalPlan q L r kin g t ω Set.univ
    filter_upwards [show ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
        (PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) :
            ℝ≥0∞) from h] with ω hω
    rw [scene_edge_totalMass hs, hω, ← legalMarkedOptimalPlan_univ q L r kin g t ω]
  · intro h
    show ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
        (PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞)
    filter_upwards [h] with ω hω
    unfold PalmSceneCloudMassTransfer at hω
    rw [← scene_edge_totalMass hs, hω, legalMarkedOptimalPlan_univ]

/-- **The transport implies a.e. Palm count transfer** (the count identity with
the scene edge measure and the realized legal graph). -/
theorem ae_countTransfer_of_couplingTransport
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (htransport : PalmSceneCloudCouplingTransport (q := q) hs α β ρ) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ, PalmSceneCloudCountTransfer s ω := by
  show ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) Set.univ =
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞)
  filter_upwards [show ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
    (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
      (PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞)
    from htransport] with ω hω
  rw [scene_edge_totalMass hs]
  exact hω

/-- **The isolated identification is equivalent to a.e. Palm count transfer.** -/
theorem couplingTransport_iff_ae_countTransfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) :
    PalmSceneCloudCouplingTransport (q := q) hs α β ρ ↔
      ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ, PalmSceneCloudCountTransfer s ω := by
  constructor
  · exact ae_countTransfer_of_couplingTransport hs α β ρ
  · intro h
    show ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      (∑' n, ((sceneEdgeConfig hs n).card : ℝ≥0∞)) =
        (PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℝ≥0∞)
    filter_upwards [h] with ω hω
    unfold PalmSceneCloudCountTransfer at hω
    rw [← scene_edge_totalMass hs]
    exact hω

/-- **Final reduction**: the pure shell-cardinality identity is equivalent to
a.e. Palm count transfer.  Together with the unconditional facts above, the
scene-to-cloud count identity reduces to the single named a.e. identification
PalmSceneCloudCouplingTransport. -/
theorem shellCardinalityIdentity_iff_ae_countTransfer
    {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    (horder : ∀ᵐ p ∂α.prod β, p.1 < p.2) :
    PalmSceneCloudShellCardinalityIdentity (q := q) hs α β ρ ↔
      ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ, PalmSceneCloudCountTransfer s ω := by
  constructor
  · intro h
    exact ae_countTransfer_of_couplingTransport hs α β ρ
      ((couplingTransport_iff_shellCardinalityIdentity hs α β ρ horder).mpr h)
  · intro h
    exact (couplingTransport_iff_shellCardinalityIdentity hs α β ρ horder).mp
      ((couplingTransport_iff_ae_countTransfer hs α β ρ).mpr h)

end OTSelector.Reconstruction
