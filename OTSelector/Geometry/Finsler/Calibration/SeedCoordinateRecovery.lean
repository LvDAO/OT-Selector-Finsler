import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Calibration.FixedSeedCoordinates
import OTSelector.Geometry.Finsler.Calibration.RootLabelValue
import OTSelector.Geometry.Finsler.Calibration.SeedRootPartition
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicLabelGeometry.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicLabelGeometry`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.SeedCoordinateRecovery

* **Conditions:** The same fixed seed observation and a point/root in the actual original selected seed piece.
* **Objects:** Exact recovery of the inverse seed vector and its original population label from the unchanged basis coordinates.
* **Proof detail:** Cancel the basis equivalence and its inverse, then apply the actual inverse seed-label identity on its image.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (adapter): Only the three exact root-readout identities are selected; macroscopic/residual decompositions and continuity refinements are outside scope.
-/

/-!
# Original seed labels at the actual macroscopic root

The fixed original seed basis recovers the original population label exactly.
The actual scaled observation separates into its macroscopic root and local
residual. On a compact continuous-label core, original root recovery supplies
inverse continuity, hence a genuine root-neighborhood test from these labels.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false





variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}

/-- The inverse fixed seed basis reads exactly the actual original root label. -/
theorem physicalSceneOriginalSeedBasisPosition_symm (j : ℕ) (x : M) :
    (Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm
      (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x) =
      populationSeedRootLabelValue (P j).seed a (a x) := by
  simp only [physicalSceneOriginalSeedBasisPosition, LinearEquiv.symm_apply_apply]

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj in
/-- On the fixed original seed piece the actual original label belongs to the
seed and its zero-time curve recovers exactly the original population root. -/
theorem fixed_seed_rootLabel_recovery (j : ℕ) {z : ℚ → M}
    (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    populationSeedRootLabelValue (P j).seed a z ∈ (P j).seed.labels ∧
      a ((P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) 0) = z := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hz⟩]
  exact ⟨(populationSeedPieceLabel P a κ lambda j ⟨z, hz⟩).property,
    populationSeedPieceLabel_root P a κ lambda j ⟨z, hz⟩⟩

include hF hcomplete hu ha hinj in
/-- Every actual endpoint in the fixed physical source piece has exact
zero-time original root recovery in the same fixed basis. -/
theorem physicalSceneOriginalSeedBasisPosition_root_recovery (j : ℕ) {x : M}
    (hx : x ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j) :
    let w := (Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm
      (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x)
    w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = a x := by
  dsimp only
  rw [physicalSceneOriginalSeedBasisPosition_symm]
  exact fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj j hx











end OTSelector.Reconstruction

end
end
