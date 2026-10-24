import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Calibration.FixedSeedCoordinates
import OTSelector.Geometry.Finsler.Calibration.RootLabelValue
import OTSelector.Geometry.Finsler.Calibration.SeedCoordinateRecovery
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedPairReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedPairReadout`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.SeedPairReadout

* **Conditions:** A fixed calibrated window atlas and original labels, with the stated finite label/reference measures and original regular same-ray carrier.
* **Objects:** A measurable pair readout consisting of transverse cube coordinates and both potential clocks, injective on its declared regular same-ray carrier.
* **Proof detail:** Invert the original seed coordinate to recover the population label, then use injectivity of label plus potential to identify each of the two endpoints.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (adapter): An actual readout-injectivity adapter. The exact domain and inherited constructed coordinate data are retained in the source telescope.
-/

/-!
# Original regular ray pairs are determined by the actual seed probe

The original fixed seed coordinate recovers its original population label.
Together with the two unchanged potential clocks it identifies both physical
endpoints on the original regular same-ray carrier.
-/
open Set Function MeasureTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}

/-- The actual original seed coordinate and both original endpoint clocks. -/
def physicalSceneOriginalSeedPairReadout (j : ℕ) (p : M × M) :
    (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ) :=
  (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j p.1, (u p.1, u p.2))

/-- The original fixed source seed, regular endpoints and their unchanged common ray label. -/
def physicalSceneOriginalSeedRegularRayPairs (j : ℕ) : Set (M × M) :=
  {p | p.1 ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) j ∧ p.1 ∈ F.potentialRegularDomain u ∧
    p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2}

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- Actual original seed probes are measurable without a new coordinate law. -/
theorem measurable_physicalSceneOriginalSeedPairReadout (j : ℕ) :
    Measurable (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hpos : Measurable (physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j) :=
    (Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.continuous.measurable.comp
      ((measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj).comp ha)
  exact (hpos.comp measurable_fst).prodMk
    ((hu.continuous.measurable.comp measurable_fst).prodMk
      (hu.continuous.measurable.comp measurable_snd))

/-- The original regular same-ray carrier is Borel in the physical pair space. -/
theorem measurableSet_physicalSceneOriginalSeedRegularRayPairs
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] (j : ℕ) :
    MeasurableSet (physicalSceneOriginalSeedRegularRayPairs (P := P) (a := a) (κ := κ)
      (lambda := lambda) j) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hreg := hF.measurableSet_potentialRegularDomain hcomplete u
  exact ((measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j).preimage
    measurable_fst).inter ((hreg.preimage measurable_fst).inter
      ((hreg.preimage measurable_snd).inter
        (measurableSet_eq_fun (ha.comp measurable_fst) (ha.comp measurable_snd))))

/-- No original pair information is lost by the source seed coordinate and the
unchanged clocks on the actual regular same-ray carrier. -/
theorem physicalSceneOriginalSeedPairReadout_injOn (j : ℕ) :
    InjOn (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j)
      (physicalSceneOriginalSeedRegularRayPairs (P := P) (a := a) (κ := κ)
        (lambda := lambda) j) := by
  intro p hp q hq heq
  have hposition : physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j p.1 =
      physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j q.1 := congrArg Prod.fst heq
  have hclockSource : u p.1 = u q.1 := congrArg (fun t ↦ t.2.1) heq
  have hclockTarget : u p.2 = u q.2 := congrArg (fun t ↦ t.2.2) heq
  have hrp := physicalSceneOriginalSeedBasisPosition_root_recovery hF hcomplete hu ha hinj j hp.1
  have hrq := physicalSceneOriginalSeedBasisPosition_root_recovery hF hcomplete hu ha hinj j hq.1
  dsimp only at hrp hrq
  have hroot : a p.1 = a q.1 := by
    rw [← hrp.2, ← hrq.2, hposition]
  have hsource : p.1 = q.1 := by
    have hs : (⟨p.1, hp.2.1⟩ : F.potentialRegularDomain u) = ⟨q.1, hq.2.1⟩ :=
      hinj (Prod.ext hroot hclockSource)
    exact congrArg Subtype.val hs
  have htargetRoot : a p.2 = a q.2 := hp.2.2.2.symm.trans (hroot.trans hq.2.2.2)
  have htarget : p.2 = q.2 := by
    have ht : (⟨p.2, hp.2.2.1⟩ : F.potentialRegularDomain u) = ⟨q.2, hq.2.2.1⟩ :=
      hinj (Prod.ext htargetRoot hclockTarget)
    exact congrArg Subtype.val ht
  exact Prod.ext hsource htarget

end OTSelector.Reconstruction

end
end
