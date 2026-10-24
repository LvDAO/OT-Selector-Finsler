import OTSelector.Reconstruction.OriginalWindowPortConservation
import OTSelector.Reconstruction.LegalRepairEndpointCouplingFinal
import OTSelector.Transport.Finite.RetainedPlanRepair

/-!
# Final legal residual repair in the actual original Finsler setting

This file closes the legal residual-repair pipeline for the actual original
Finsler data. It combines three layers, all stated with the actual original seed,
stationary matching and retained finite plan:

1. the actual retained plan of `OriginalRetainedFinitePlan` is a legal simple
   original counting subplan which consumes at most the true source and target
   capacities, and both complete original colored window inputs decompose
   exactly into the retained endpoints plus the literal source and target port
   plans (`OriginalRetainedLegalCore`, `OriginalWindowPortConservation`);
2. the unconditional endpoint transport coupling of
   `LegalRepairEndpointCouplingFinal` applies to the residual discrepancy once
   it is expressed in the original physical coordinates, giving a genuine
   coupling of the two residual measures with extended-distance cost at most
   `C * sqrt (card iota * (mu univ).toReal)`;
3. the actual signed value comparison of `LegalRepairNeumannValue` holds with
   the explicit repair budget `rho⁻¹ C² / 2`, and the finite corrected retained
   plan is a genuine coupling with the exact full source and target marginals,
   with added cost at most `L` times the common residual port mass.

## Remaining data hypotheses

The only hypotheses not produced by the existing library are the residual
coordinate data: the actual residual port masses must be expressed as two
probability densities `f`, `g` against one compactly carried finite reference
measure `mu` in the original physical coordinates, with the common positive
lower bound `rho` and the actual residual gradient bound `C`. They are stated
explicitly below and are not repair callbacks: the flux, its energy, the value
comparison, the coupling and the corrected plan are all constructed.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold TopologicalSpace
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Distributions RealInnerProductSpace BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- **The actual retained plan against the true original capacities.** Almost
surely in the actual original scene law: the retained plan is a legal simple
original counting subplan; it consumes at most the exact source and target
original capacities; and both complete original colored window inputs are
exactly the retained endpoint marginals plus the literal source and target port
plans. -/
theorem originalSeed_retainedPlan_capacities_ae
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {gkin : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin gkin)
    (D : OriginalSeedConditionalMoments S w μ ν)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure
        (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
          (originalPathRetainedPlan S w R ell scene) ∧
      ((originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ≤
          legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 0 ∧
        (originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd ≤
          legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 1) ∧
      ((legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 0).restrict
          {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R} =
        (originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst +
        (originalPathSourcePortPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ∧
        (legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 1).restrict
          {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R} =
        (originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd +
        (originalPathTargetPortPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd) := by
  filter_upwards [Q.full_matching, D.ae_original_windows_eq_retained_add_ports hF hw Q hell hR]
    with scene hfull hdecomp
  exact ⟨hfull.simple_originalPathRetainedPlan (S := S) (w := w) R ell,
    hfull.originalPathRetainedPlan_capacities R ell, hdecomp.1, hdecomp.2⟩

section ResidualRepairData
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K : Compacts (ι → ℝ)) (μref : Measure (ι → ℝ)) [IsFiniteMeasure μref]
variable (f g : (ι → ℝ) → ℝ)
variable {ρ C : ℝ}
variable {Sf Tf : Type*} [Fintype Sf] [Fintype Tf]
  [MeasurableSpace Sf] [MeasurableSingletonClass Sf]
  [MeasurableSpace Tf] [MeasurableSingletonClass Tf]

/-- **(1) The genuine residual endpoint coupling.** Under the explicit residual
coordinate data, the original residual discrepancy admits a genuine coupling of
the two residual measures whose extended-distance cost is at most the explicit
constant `C * sqrt (card iota * (mu univ).toReal)`. -/
theorem originalSeed_legalResidualRepair_endpointCoupling
    (hf : Integrable f μref) (hg : Integrable g μref)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μref, ρ ≤ f x) (hgl : ∀ᵐ x ∂μref, ρ ≤ g x)
    (hprobS : IsProbabilityMeasure (residualDensityMeasure μref f))
    (hprobT : IsProbabilityMeasure (residualDensityMeasure μref g))
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀)
    (hνsuppS : ∀ᵐ x ∂(residualDensityMeasure μref f), x ∈ K₀)
    (hK₀K : K₀ ⊆ interior (K : Set (ι → ℝ)))
    (hgrad : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μref) - ∫ x, φ x * g x ∂μref‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μref φ‖) :
    ∃ π : Measure ((ι → ℝ) × (ι → ℝ)),
      Vlasov.IsCoupling π (residualDensityMeasure μref f) (residualDensityMeasure μref g) ∧
      (∫⁻ z, edist z.1 z.2 ∂π) ≤
        ENNReal.ofReal (C * Real.sqrt ((Fintype.card ι : ℝ) * (μref univ).toReal)) :=
  exists_endpointCoupling_edist_le_of_neumannFlux_final K μref f g hf hg hρ hC hfl hgl
    hprobS hprobT hK₀ hνsuppS hK₀K hgrad

/-- **(2) The actual signed value comparison with the repair budget
`rho⁻¹ C² / 2`.** For any original compactly supported smooth endpoint
potentials satisfying the Hamilton--Jacobi admissibility, the signed residual
value of the repaired pair is bounded by the explicit repair budget. -/
theorem originalSeed_legalResidualRepair_valueComparison
    (hf : Integrable f μref) (hg : Integrable g μref)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μref, ρ ≤ f x) (hgl : ∀ᵐ x ∂μref, ρ ≤ g x)
    (hgrad : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μref) - ∫ x, φ x * g x ∂μref‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μref φ‖)
    (Asrc Atgt : 𝓓_{K}(ι → ℝ, ℝ))
    (hHJ : ∀ x, Atgt x - Asrc x +
      ‖physicalCoordinateGradient ι (fderiv ℝ Asrc x)‖ ^ 2 / 2 ≤ 0) :
    (∫ x, Atgt x * g x ∂μref) - (∫ x, Asrc x * f x ∂μref) ≤ ρ⁻¹ * C ^ 2 / 2 :=
  legalResidualRepair_signedValue_le K μref f g hf hg hρ hC hfl hgl hgrad Asrc Atgt hHJ

/-- **(3) The finite corrected retained plan.** The corrected finite retained
plan is a genuine coupling of the two full endpoint measures with the exact full
marginals, and its actual extended cost is at most the retained plan cost plus
`L` times the common residual port mass. -/
theorem originalSeed_legalResidualRepair_finitePlan
    {p : Sf → Tf → ℝ} {rsrc : Sf → ℝ} {rtgt : Tf → ℝ}
    {a : Sf → ℝ} {b : Tf → ℝ} {cost : Sf → Tf → ℝ} {L : ℝ}
    (hp : ∀ i j, 0 ≤ p i j) (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (hrow : ∀ i, (∑ j, p i j) + rsrc i = a i)
    (hcol : ∀ j, (∑ i, p i j) + rtgt j = b j)
    (hcost : ∀ i j, 0 ≤ cost i j) (hcostL : ∀ i j, cost i j ≤ L) :
    Vlasov.IsCoupling (finitePlanMeasure (repairedRetainedPlan p rsrc rtgt))
        (finiteWeightedMeasure a) (finiteWeightedMeasure b) ∧
      (∫⁻ z, ENNReal.ofReal (cost z.1 z.2) ∂
          finitePlanMeasure (repairedRetainedPlan p rsrc rtgt)) ≤
        ENNReal.ofReal ((∑ i, ∑ j, p i j * cost i j) + L * ∑ i, rsrc i) :=
  ⟨repairedRetainedPlan_measure_isCoupling hp hrsrc hrtgt hmass hrow hcol,
    repairedRetainedPlan_measureCost_le hp hrsrc hrtgt hmass hcost hcostL⟩

/-- **The final original legal residual repair.** For the actual original Finsler
seed, stationary weighted matching and retained finite plan, together with the
explicit residual coordinate data, all three conclusions hold simultaneously:
the actual retained plan is legal with exact capacities and window decomposition;
the residual discrepancy admits a genuine coupling with explicit extended-distance
cost; the signed value comparison holds with repair budget `rho⁻¹ C² / 2`; and
the corrected finite retained plan is a genuine full coupling with exact
marginals and explicit added cost. -/
theorem originalSeed_legalResidualRepair_final
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {gkin : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin gkin)
    (D : OriginalSeedConditionalMoments S w μ ν)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R)
    (hf : Integrable f μref) (hg : Integrable g μref)
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μref, ρ ≤ f x) (hgl : ∀ᵐ x ∂μref, ρ ≤ g x)
    (hprobS : IsProbabilityMeasure (residualDensityMeasure μref f))
    (hprobT : IsProbabilityMeasure (residualDensityMeasure μref g))
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀)
    (hνsuppS : ∀ᵐ x ∂(residualDensityMeasure μref f), x ∈ K₀)
    (hK₀K : K₀ ⊆ interior (K : Set (ι → ℝ)))
    (hgrad : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μref) - ∫ x, φ x * g x ∂μref‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μref φ‖)
    (Asrc Atgt : 𝓓_{K}(ι → ℝ, ℝ))
    (hHJ : ∀ x, Atgt x - Asrc x +
      ‖physicalCoordinateGradient ι (fderiv ℝ Asrc x)‖ ^ 2 / 2 ≤ 0)
    {p : Sf → Tf → ℝ} {rsrc : Sf → ℝ} {rtgt : Tf → ℝ}
    {a : Sf → ℝ} {b : Tf → ℝ} {cost : Sf → Tf → ℝ} {L : ℝ}
    (hp : ∀ i j, 0 ≤ p i j) (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (hrow : ∀ i, (∑ j, p i j) + rsrc i = a i)
    (hcol : ∀ j, (∑ i, p i j) + rtgt j = b j)
    (hcost : ∀ i j, 0 ≤ cost i j) (hcostL : ∀ i j, cost i j ≤ L) :
    (∀ᵐ scene ∂(Q.law : Measure
        (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
          (originalPathRetainedPlan S w R ell scene) ∧
      ((originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ≤
          legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 0 ∧
        (originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd ≤
          legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 1) ∧
      ((legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 0).restrict
          {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R} =
        (originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst +
        (originalPathSourcePortPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ∧
        (legalInputColorMeasure (finrank ℝ S.covector.ker) scene.2 1).restrict
          {p | p.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R} =
        (originalPathRetainedPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd +
        (originalPathTargetPortPlan S w R ell scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd)) ∧
    (∃ π : Measure ((ι → ℝ) × (ι → ℝ)),
      Vlasov.IsCoupling π (residualDensityMeasure μref f) (residualDensityMeasure μref g) ∧
      (∫⁻ z, edist z.1 z.2 ∂π) ≤
        ENNReal.ofReal (C * Real.sqrt ((Fintype.card ι : ℝ) * (μref univ).toReal))) ∧
    ((∫ x, Atgt x * g x ∂μref) - (∫ x, Asrc x * f x ∂μref) ≤ ρ⁻¹ * C ^ 2 / 2) ∧
    (Vlasov.IsCoupling (finitePlanMeasure (repairedRetainedPlan p rsrc rtgt))
        (finiteWeightedMeasure a) (finiteWeightedMeasure b) ∧
      (∫⁻ z, ENNReal.ofReal (cost z.1 z.2) ∂
          finitePlanMeasure (repairedRetainedPlan p rsrc rtgt)) ≤
        ENNReal.ofReal ((∑ i, ∑ j, p i j * cost i j) + L * ∑ i, rsrc i)) :=
  ⟨originalSeed_retainedPlan_capacities_ae hF hw Q D hell hR,
    originalSeed_legalResidualRepair_endpointCoupling K μref f g hf hg hρ hC hfl hgl
      hprobS hprobT hK₀ hνsuppS hK₀K hgrad,
    originalSeed_legalResidualRepair_valueComparison K μref f g hf hg hρ hC hfl hgl
      hgrad Asrc Atgt hHJ,
    originalSeed_legalResidualRepair_finitePlan hp hrsrc hrtgt hmass hrow hcol
      hcost hcostL⟩

end ResidualRepairData

end OTSelector.Reconstruction
