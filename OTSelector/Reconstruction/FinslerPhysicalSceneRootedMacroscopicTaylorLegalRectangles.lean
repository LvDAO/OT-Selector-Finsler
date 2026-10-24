import OTSelector.Reconstruction.FinslerQuadraticCostDifferenceCore
import OTSelector.Transport.CyclicMonotonicity.OpenDomainCycleSupport
import OTSelector.Probability.CavitySemidiscreteSpatialBasis

/-!
# Legal strict rectangles for the original frozen coefficient

Continuity is taken directly from one retained original coefficient core,
restricted to its original scalar pair region. The existing countable legal
cycle-witness producer handles strict gaps. Open scalar bins and their retained
outer endpoint and separation bounds supply all four legal clock pairs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace RationalScalarPairWindow

/-- Two original closed scalar bins and one uniform endpoint separation place
their entire product in the same original rational pair region. -/
theorem closed_bins_prod_subset_region (q : RationalScalarPairWindow)
    {sL sR tL tR : ℝ}
    (hs : Icc sL sR ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ))
    (hgap : (q.val.2.2 : ℝ) ≤ tL - sR) :
    Icc sL sR ×ˢ Icc tL tR ⊆ q.region := by
  rintro ⟨s, t⟩ ⟨hs', ht'⟩
  refine ⟨⟨hs hs', ht ht'⟩, ?_⟩
  change (q.val.2.2 : ℝ) ≤ t - s
  change s ∈ Icc sL sR at hs'
  change t ∈ Icc tL tR at ht'
  linarith [hs'.2, ht'.1]

/-- The individual two-source and two-target bin tests imply all four actual
clock-pair tests; diagonal legality alone is not an input to this lemma. -/
theorem four_clock_pairs_mem_region_of_closed_bins (q : RationalScalarPairWindow)
    {sL sR tL tR : ℝ}
    (hs : Icc sL sR ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc (q.val.1 : ℝ) (q.val.2.1 : ℝ))
    (hgap : (q.val.2.2 : ℝ) ≤ tL - sR)
    (source target : Fin 2 → ℝ)
    (hsource : ∀ i, source i ∈ Icc sL sR) (htarget : ∀ j, target j ∈ Icc tL tR) :
    ∀ i j, (source i, target j) ∈ q.region :=
  fun i j ↦ q.closed_bins_prod_subset_region hs ht hgap ⟨hsource i, htarget j⟩

end RationalScalarPairWindow

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- The existing original fixed-root cost is jointly continuous on the
original clock-region preimage. No extension across illegal clocks is asserted. -/
theorem continuousOn_frozenQuadraticCost_clock_region
    {c : Z} (hc : c ∈ C.roots) :
    ContinuousOn (Function.uncurry (C.frozenQuadraticCost c))
      (C.frozenQuadraticLegalDomain id) := by
  let X := (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ
  have hA : ContinuousOn
      (fun p : ℝ × ℝ ↦ populationSeedRootCoefficient (P C.seedIndex).seed a
        (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (c, p)) C.window.region :=
    C.coefficient_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp ↦ ⟨hc, hp⟩)
  have hclock : Continuous (fun p : X × X ↦ (p.1.2, p.2.2)) :=
    continuous_fst.snd.prodMk continuous_snd.snd
  have hdelta : Continuous (fun p : X × X ↦ p.2.1 - p.1.1) :=
    continuous_snd.fst.sub continuous_fst.fst
  have hcoeff := hA.comp hclock.continuousOn (fun p hp ↦ hp)
  exact continuous_matrixQuadratic.comp_continuousOn (hcoeff.prodMk hdelta.continuousOn)

/-- The fixed marked spatial basis gives a countable family of legal strict
cycle indices for this original seed coordinate space. -/
theorem countable_frozenQuadratic_cycle_indices :
    Countable (CavityBasisCycleIndex
      (cavitySpatialBasis
        (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ))
      (cavitySpatialBasis
        (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ))) := by
  let _instBasis : Countable (cavitySpatialBasis
    (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ)) :=
    countable_cavitySpatialBasis.to_subtype
  infer_instance

/-- Any actual open legal subdomain of the original clock region inherits
countable strict rectangles from the existing legal cycle-witness producer. -/
theorem exists_frozenQuadratic_open_legal_cycle_rectangles
    {c : Z} (hc : c ∈ C.roots)
    {D : Set
      (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
        ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ))}
    (hD : IsOpen D) (hsub : D ⊆ C.frozenQuadraticLegalDomain id)
    (x x' y y' : (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)
    (hxy : (x, y) ∈ D) (hxy' : (x', y') ∈ D)
    (hcross : (x, y') ∈ D) (hcross' : (x', y) ∈ D)
    (hbad : C.frozenQuadraticCost c x y' + C.frozenQuadraticCost c x' y <
      C.frozenQuadraticCost c x y + C.frozenQuadraticCost c x' y') :
    ∃ i : CavityBasisCycleIndex
      (cavitySpatialBasis
        (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ))
      (cavitySpatialBasis
        (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ)),
      CavityLegalBasisCycleValid (C.frozenQuadraticCost c) D i ∧
      (x, y) ∈ i.1.1.1.val ×ˢ i.1.1.2.val ∧
      (x', y') ∈ i.1.2.1.val ×ˢ i.1.2.2.val ∧
      Disjoint i.1.1.1.val i.1.2.1.val ∧ Disjoint i.1.1.2.val i.1.2.2.val ∧
      ∃ phaseSize > 0, ∃ offset :
        Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
        ∀ s ∈ i.1.1.1.val ∪ i.1.2.1.val,
          s.1 - offset ∈ cavityGridPhaseCell _ phaseSize := by
  obtain ⟨i, hi, hleft, hright⟩ := exists_cavityLegalBasisCycleIndex_of_strict_cycle
    (C.frozenQuadraticCost c) D hD
    ((C.continuousOn_frozenQuadraticCost_clock_region hc).mono hsub)
    isTopologicalBasis_cavitySpatialBasis isTopologicalBasis_cavitySpatialBasis
    x x' y y' hxy hxy' hcross hcross' hbad
  obtain ⟨hsource, htarget⟩ := hi.1.disjoint ⟨(x, y), hleft⟩ ⟨(x', y'), hright⟩
  obtain ⟨phaseSize, hphaseSize, offset, hphase⟩ :=
    exists_phaseCell_of_cavitySpatialBasis i.1.1.1.property i.1.2.1.property
  exact ⟨i, hi, hleft, hright, hsource, htarget, phaseSize, hphaseSize, offset, hphase⟩

/-- The actual open source-clock/target-clock rectangle used by the strict
cycle adapter. Its endpoints and original separation remain explicit inputs. -/
def frozenClockOpenRectangle (sL sR tL tR : ℝ) : Set
    (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)) :=
  {p | p.1.2 ∈ Ioo sL sR ∧ p.2.2 ∈ Ioo tL tR}

/-- Strict membership in both clock intervals makes the endpoint-pair domain open. -/
theorem isOpen_frozenClockOpenRectangle (sL sR tL tR : ℝ) :
    IsOpen (C.frozenClockOpenRectangle sL sR tL tR) :=
  (isOpen_Ioo.preimage continuous_fst.snd).inter
    (isOpen_Ioo.preimage continuous_snd.snd)

/-- Closed-bin containment and the same original endpoint separation imply
legality of every marked edge in the actual open clock rectangle. -/
theorem frozenClockOpenRectangle_subset_original_region
    {sL sR tL tR : ℝ}
    (hs : Icc sL sR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (hgap : (C.window.val.2.2 : ℝ) ≤ tL - sR) :
    C.frozenClockOpenRectangle sL sR tL tR ⊆ C.frozenQuadraticLegalDomain id := by
  intro p hp
  exact C.window.closed_bins_prod_subset_region hs ht hgap
    ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩

/-- Individual strict clock-bin tests suffice for all four legal edge inputs
to the existing strict rectangle witness. The output gap is internally rational. -/
theorem exists_frozenQuadratic_clock_rectangle_cycle
    {c : Z} (hc : c ∈ C.roots) {sL sR tL tR : ℝ}
    (hs : Icc sL sR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (hgap : (C.window.val.2.2 : ℝ) ≤ tL - sR)
    (x x' y y' : (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)
    (hx : x.2 ∈ Ioo sL sR) (hx' : x'.2 ∈ Ioo sL sR)
    (hy : y.2 ∈ Ioo tL tR) (hy' : y'.2 ∈ Ioo tL tR)
    (hbad : C.frozenQuadraticCost c x y' + C.frozenQuadraticCost c x' y <
      C.frozenQuadraticCost c x y + C.frozenQuadraticCost c x' y') :
    ∃ i : CavityBasisCycleIndex
      (cavitySpatialBasis
        (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ))
      (cavitySpatialBasis
        (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ)),
      CavityLegalBasisCycleValid (C.frozenQuadraticCost c)
        (C.frozenClockOpenRectangle sL sR tL tR) i ∧
      (x, y) ∈ i.1.1.1.val ×ˢ i.1.1.2.val ∧
      (x', y') ∈ i.1.2.1.val ×ˢ i.1.2.2.val ∧
      Disjoint i.1.1.1.val i.1.2.1.val ∧ Disjoint i.1.1.2.val i.1.2.2.val ∧
      ∃ phaseSize > 0, ∃ offset :
        Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
        ∀ s ∈ i.1.1.1.val ∪ i.1.2.1.val,
          s.1 - offset ∈ cavityGridPhaseCell _ phaseSize := by
  exact C.exists_frozenQuadratic_open_legal_cycle_rectangles hc
    (C.isOpen_frozenClockOpenRectangle sL sR tL tR)
    (C.frozenClockOpenRectangle_subset_original_region hs ht hgap)
    x x' y y' ⟨hx, hy⟩ ⟨hx', hy'⟩ ⟨hx, hy'⟩ ⟨hx', hy⟩ hbad

end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
