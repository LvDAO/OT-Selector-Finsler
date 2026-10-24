import OTSelector.Geometry.Finsler.Calibration.FixedSeedCoordinates
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceTestEscape

/-!
# Geometry.Finsler.Calibration.FixedSeedCoordinates

* **Conditions:** A fixed original calibrated window atlas, population label map and its existing selected root pieces.
* **Objects:** The fixed physical source piece and its original basis-coordinate seed observation, with measurable source membership.
* **Proof detail:** Take the label preimage of the existing Borel piece and express its zero-extended inverse label in the finite seed basis.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (adapter): Only the two definitions and source-set measurability are selected; auxiliary accuracies, near-edge events and pressure statements are excluded.
-/

/-!
# One fixed original seed scene across auxiliary accuracies

The physical source piece and scaled seed basis observation are defined directly
from the original atlas. They do not depend on an auxiliary finite core. Every
auxiliary near edge stays in one original seed piece, and its same-seed position
agrees exactly with the fixed observation. Crossings of a fixed source piece are
therefore part of the full original non-near complement at every core accuracy.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
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
  [IsFiniteMeasure lambda] {μ ν : Measure M}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞} [∀ j, SigmaFinite (κ j)]





/-- The fixed original seed basis observation at the actual spatial scale. -/
def physicalSceneOriginalSeedScaledPosition (j : ℕ) (scale : ℝ) (x : M) :
    Fin (finrank ℝ (P j).seed.covector.ker) → ℝ :=
  scale • physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j x

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)

/-- On an actual near edge, source membership in one fixed original seed piece
identifies exactly the seed index of the auxiliary coefficient core. -/
theorem nearDisplacement_source_mem_fixed_seed_iff
    (i : Fin D.haar.continuous.count) (j : ℕ) {radius : ℝ} {p : M × M}
    (hp : p ∈ D.nearDisplacementEvent i radius) :
    p.1 ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ↔
      (D.haar.continuous.coefficient i).seedIndex = j := by
  have hi := (D.haar.continuous.coefficient i).roots_subset_piece hp.1
  constructor
  · intro hj
    by_contra h
    exact Set.disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ lambda h) hi hj
  · intro h
    simpa only [h, physicalSceneOriginalSeedSource, mem_preimage] using hi

/-- An actual near edge never crosses any fixed original seed piece, even
when the auxiliary scalar windows and compact root cores change. -/
theorem nearDisplacement_fixed_seed_source_iff_target
    (i : Fin D.haar.continuous.count) (j : ℕ) {radius : ℝ} {p : M × M}
    (hp : p ∈ D.nearDisplacementEvent i radius) :
    p.1 ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ↔
      p.2 ∈ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j := by
  have hi := (D.haar.continuous.coefficient i).roots_subset_piece hp.2.1
  rw [D.nearDisplacement_source_mem_fixed_seed_iff i j hp]
  constructor
  · intro h
    simpa only [h, physicalSceneOriginalSeedSource, mem_preimage] using hi
  · intro hj
    by_contra h
    exact Set.disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ lambda h) hi hj

/-- The same-seed physical coordinate is unchanged by auxiliary core selection. -/
theorem scaledPhysicalBasisPosition_heq_fixed_seed
    (i : Fin D.haar.continuous.count) (j : ℕ)
    (hseed : (D.haar.continuous.coefficient i).seedIndex = j) (scale : ℝ) (x : M) :
    HEq (D.scaledPhysicalBasisPosition i scale x)
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale x) := by
  subst j
  rfl

/-- The scalar displacement energy in the fixed seed frame agrees exactly
with that of every same-seed auxiliary coefficient core. -/
theorem fixed_seed_scaled_displacement_sq_eq
    (i : Fin D.haar.continuous.count) (j : ℕ)
    (hseed : (D.haar.continuous.coefficient i).seedIndex = j)
    (scale : ℝ) (x y : M) :
    ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale y -
      physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale x‖ ^ 2 =
      ‖D.scaledPhysicalBasisPosition i scale y - D.scaledPhysicalBasisPosition i scale x‖ ^ 2 := by
  subst j
  rfl

/-- Every crossing of a fixed original seed piece lies in the complete global
non-near event of any auxiliary finite core. -/
theorem fixed_seed_crossing_subset_global_nonNear
    (j : ℕ) (A B : Set M) (radius : ℝ) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
    ((H ×ˢ Hᶜ) ∪ (Hᶜ ×ˢ H)) ∩ (A ×ˢ B) ⊆
      (A ×ˢ B) \ ⋃ i, D.nearDisplacementEvent i radius := by
  intro H p hp
  refine ⟨hp.2, ?_⟩
  intro hn
  obtain ⟨i, hi⟩ := mem_iUnion.mp hn
  have he := D.nearDisplacement_fixed_seed_source_iff_target i j hi
  rcases hp.1 with hc | hc
  · exact hc.2 (he.mp hc.1)
  · exact hc.1 (he.mpr hc.2)

end PopulationLocalPressureCore

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj



/-- The same fixed original seed coordinate is measurable before any auxiliary
accuracy core is chosen. -/
theorem measurable_physicalSceneOriginalSeedScaledPosition (j : ℕ) (scale : ℝ) :
    Measurable (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  exact ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.continuous.measurable.comp
    ((measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj).comp ha)).const_smul scale

end OTSelector.Reconstruction
