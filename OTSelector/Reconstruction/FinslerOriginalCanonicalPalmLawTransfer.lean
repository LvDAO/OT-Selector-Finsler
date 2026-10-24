import OTSelector.Reconstruction.FinslerOriginalCanonicalGrootElimination
import OTSelector.Reconstruction.FinslerOriginalPalmSampleLawProof
import OTSelector.Reconstruction.FinslerOriginalTileCountingLaw
import OTSelector.Reconstruction.FinslerOriginalRootedTileSingleInstantiation
import OTSelector.Reconstruction.FinslerOriginalTileSingleConvergenceProof

/-!
# Transfer of the canonical Palm law and Palm LLN from population inputs

FinslerOriginalCanonicalGrootElimination eliminated the atlas root family Groot
and the gluing binder hgt by fixing the root family to the canonical rooted
integrand family fun j z => rootedFrozenIntegrand ... f t j z.  The readout of
the lane then rests on two (f,t)-indexed predicates at the canonical family:

* CanonicalRootedTilePalmLaw: the tile Palm sample law at every probe, tilt and
  retained tile, with population value the tile Campbell value of the canonical
  family at that (f,t);
* CanonicalRootedTileMeanLaw: the Palm LLN (paper F16), i.e. the rooted tile mean
  convergence of the counted per-tile frozen means towards those tile values.

This module closes the gap reported with that delivery, i.e. the missing
transfer of the Palm law and the Palm LLN to the canonical family.  It records:

1. the (f,t)-indexing is definitionally the same: a single TilePalmSampleLaw
   family at the canonical integrand family IS CanonicalRootedTilePalmLaw, so
   the Palm-law transfer needs no extra hypothesis
   (canonicalRootedTilePalmLaw_of_tilePalmSampleLaw);
2. the V7 hlln + hpop binders, read per (f,t) with the population value of the
   corresponding canonical root family, produce that Palm law family
   (canonicalRootedTilePalmLaw_of_populationSamplingLaws);
3. the per-(f,t) Palm LLN at the corresponding canonical root family, in the
   per-tile iid form TileMeanConvergence produced from hlln + hpop by
   tileMeanConvergence_of_palmSampleLaw, produces CanonicalRootedTileMeanLaw
   through the generic-population chain of the repo
   (rootedTileMeanConvergence_of_single <-
   rootedTileSingleConvergence_of_inProbability <-
   rootedTileSingleConvergenceInProbability_of_tileMeanConvergence);
   its reindexing form from the per-(f,t) RootedTileMeanConvergence is recorded
   as canonicalRootedTileMeanLaw_of_populationPalmLLN;
4. the covering identity transfers by reindexing: the per-(f,t) population atlas
   covering identity PopulationAtlasCovering at the canonical family is exactly
   CanonicalRootedCovering (canonicalRootedCovering_of_populationAtlasCovering);
   the alternative producer from per-(f,t) PieceCellRefinement and vanishing
   atlas tails is canonicalRootedCovering_of_cellRefinement of the previous
   module;
5. the lane hId follows from the population-level inputs alone:
   frozenCampbellMeanIdentification_sceneCloud_of_canonicalPopulationInputs.

Exact remaining inputs are listed in the docstrings.  The fixed-root family
Palm LLN of V7 (a single G) cannot produce the canonical Palm LLN through the
repo chain because tileMeanConvergence_of_palmSampleLaw is stated at a single
fixed root family G; the canonical readout needs the root family to depend on
(f,t), which is precisely why Groot and hgt could be eliminated.  The inputs
below are therefore stated per (f,t) at the corresponding root family: this is
F16 read at each fixed probe and tilt, not V7's single-G instance.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

open OTSelector.Geometry
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.Reconstruction.PopulationLocalPressureCore.TaylorTiles

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} {A B : Set M}

/-! ## 1. The Palm law at the canonical integrand: definitionally the same thing -/

/-- **The canonical Palm law from the single tile Palm law family at the
canonical integrand.**

The hypothesis is the (f,t)-indexed TilePalmSampleLaw family of the paper's F16
Palm input, with population value the tile Campbell value of the canonical root
family at the same (f,t).  The conclusion is CanonicalRootedTilePalmLaw, whose
body is exactly that family: the (f,t)-indexing of the law and of the canonical
family coincide definitionally (both are functions of the probe f and the tilt
t), so the transfer carries no extra hypothesis and no extra gap. -/
def canonicalRootedTilePalmLaw_of_tilePalmSampleLaw
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hlaw : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)) :
    CanonicalRootedTilePalmLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  hlaw

/-! ## 2. The Palm law from the V7 sampling-law binders hlln + hpop -/

/-- **The canonical Palm law from hlln + hpop at the canonical root family.**

hlln is the empirical Palm LLN (paper F16 identity of the scene-cloud average
with the population readout popReadout f t c), and hpop is the population
normalization identity, here read with the tile Campbell value of the canonical
root family of the SAME probe f and tilt t.  Both binders are quantified per
(f,t,c), so their per-(f,t) instance is the input of
tilePalmSampleLaw_sceneCloud_of_LLN, applied at the canonical family
fun j z => rootedFrozenIntegrand ... f t j z.  No hypothesis beyond hlln and
hpop is used. -/
noncomputable def canonicalRootedTilePalmLaw_of_populationSamplingLaws
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (popReadout : FinalProbeSpace A B → ℝ → T.Index → ℕ → ℝ)
    (hlln : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.sceneCloudAverage pcloud qcloud n c -
        popReadout f t c n) atTop (𝓝 0))
    (hpop : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * popReadout f t c n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
        atTop (𝓝 0)) :
    CanonicalRootedTilePalmLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  fun f t c ↦ tilePalmSampleLaw_sceneCloud_of_LLN (T := T) (A := A) (B := B)
    pcloud qcloud f t c (popReadout f t c)
    (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q f t)
    (hlln f t c) (hpop f t c)

/-! ## 3. The Palm LLN at the canonical integrand -/

/-- **The canonical Palm LLN from the per-(f,t) tile mean convergence.**

The hypothesis is the per-tile iid LLN TileMeanConvergence at the canonical
population values, read at each fixed probe and tilt with the corresponding
canonical root family.  This is the form in which hlln + hpop enter the repo
chain: tileMeanConvergence_of_palmSampleLaw (FinslerOriginalPressureLowerReadout)
produces TileMeanConvergence from the Palm sample law family, and the per-(f,t)
instance here is obtained from the canonical Palm law of the previous section.

The generic-population chain of the repo (all steps generic in the population
value function) then produces the rooted tile mean convergence
RootedTileMeanConvergence at the canonical values:
rootedTileSingleConvergenceInProbability_of_tileMeanConvergence gives the
single-tile convergence in probability,
rootedTileSingleConvergence_of_inProbability the deterministic single-tile
convergence, and rootedTileMeanConvergence_of_single the Palm LLN. -/
theorem canonicalRootedTileMeanLaw_of_populationTileMeanConvergence
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hmean : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      T.TileMeanConvergence (K := A ∪ B)
        (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
        sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (uniformTilePlan (fun n ↦ Fin (n + 1)))) :
    CanonicalRootedTileMeanLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  T.rootedTileMeanConvergence_of_single (K := A ∪ B)
    (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
        (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
    sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
    (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
    (uniformTilePlan (fun n ↦ Fin (n + 1)))
    (T.rootedTileSingleConvergence_of_inProbability (K := A ∪ B)
      (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
      sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1)))
      (T.rootedTileSingleConvergenceInProbability_of_tileMeanConvergence
        (K := A ∪ B)
        (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦
          T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q)
            (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
              (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
        sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (uniformTilePlan (fun n ↦ Fin (n + 1)))
        (fun f t c ↦ hmean f t f t c)))

/-- **The canonical Palm LLN from the per-(f,t) rooted tile mean convergence.**

The hypothesis is F16 read at each fixed probe and tilt with the canonical root
family of that probe and tilt: the rooted tile mean convergence of the counted
per-tile frozen means towards the tile Campbell values of that root family.
Since RootedTileMeanConvergence quantifies the probe and tilt outside its
existential error witnesses, the canonical Palm LLN is the diagonal instance
fun f t => h f t f t: the population values agree definitionally at the
diagonal, and the index (f,t) of the hypothesis is the same index as that of
CanonicalRootedTileMeanLaw.  This is the exact reindexing of the per-probe,
per-tilt single-root Palm LLN to the canonical Palm LLN. -/
theorem canonicalRootedTileMeanLaw_of_populationPalmLLN
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (h : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      T.RootedTileMeanConvergence (K := A ∪ B)
        (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
        sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (uniformTilePlan (fun n ↦ Fin (n + 1)))) :
    CanonicalRootedTileMeanLaw (A := A) (B := B) T pcloud qcloud base q
      α β coef probeFam Mst :=
  fun f t ↦ h f t f t

/-! ## 4. The covering identity at the canonical family -/

/-- **The canonical covering identity from the population atlas covering
identity.**

The hypothesis is the population atlas covering identity PopulationAtlasCovering
read at each fixed probe and tilt with the canonical root family of that probe
and tilt.  The body of PopulationAtlasCovering is exactly the body of
CanonicalRootedCovering (the Campbell series of the root family equals the sum
of its per-tile population Campbell values), so the transfer is the reindexing
fun f t => h f t with no extra hypothesis and no gap.  The alternative producer
from per-(f,t) PieceCellRefinement and vanishing atlas tails is
canonicalRootedCovering_of_cellRefinement (FinslerOriginalCanonicalGrootElimination). -/
theorem canonicalRootedCovering_of_populationAtlasCovering
    (T : D.TaylorTiles ε) {A B : Set M} (q : ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hcover : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      PopulationAtlasCovering (P := P) (a := a) (κ := κ) (lambda := lambda)
        T q (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t)) :
    CanonicalRootedCovering (A := A) (B := B) T q α β coef probeFam Mst :=
  fun f t ↦ hcover f t

/-! ## 5. The lane hId from population-level inputs alone -/

/-- **The lane hId from the population-level inputs at the canonical family.**

Combines the two transfers above with the main theorem of
FinslerOriginalCanonicalGrootElimination: from the per-(f,t) population atlas
covering identity at the canonical family and the per-(f,t) tile mean
convergence at the canonical family, plus the geometric lane data (hF,
hcomplete, hu, ha, hinj), the rooted tile Campbell mean identification of the
frozen readout follows.  No atlas root family Groot and no gluing binder hgt
occurs; the frozen-cost integrability and the identification of the hprob frozen
cost family are discharged inside the collapsed theorem. -/
theorem frozenCampbellMeanIdentification_sceneCloud_of_canonicalPopulationInputs
    (T : D.TaylorTiles ε) {A B : Set M}
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) →
      StationaryForwardMatching α β)
    (hcover : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      PopulationAtlasCovering (P := P) (a := a) (κ := κ) (lambda := lambda)
        T q (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
          (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t))
    (hmean : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      T.TileMeanConvergence (K := A ∪ B)
        (fun (f : FinalProbeSpace A B) (t : ℝ) (c : T.Index) ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q)
          (canonicalRootedIntegrand (A := A) (B := B) (P := P) (a := a)
            (κ := κ) (lambda := lambda) α β coef probeFam Mst q f t) c)
        sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (uniformTilePlan (fun n ↦ Fin (n + 1))))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCanonicalTransferMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    RootedTileCampbellMeanIdentification (K := A ∪ B) P a κ lambda
      (frozenRootedCostReadout (F := F) (u := u) (Seed := P) (a := a)
        (κ := κ) (lambda := lambda) (Z := ℚ → M) (A := A) (B := B)
        α β coef probeFam Mst q) q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) (T := T) (sceneCloudX pcloud)
        (sceneCloudY qcloud) base (uniformTilePlan (fun n ↦ Fin (n + 1)))
        tileScale) T.Index :=
  frozenCampbellMeanIdentification_sceneCloud_of_canonicalRootedIntegrand
    (A := A) (B := B) T pcloud qcloud base q α β coef probeFam Mst
    (canonicalRootedCovering_of_populationAtlasCovering (A := A) (B := B) T q
      α β coef probeFam Mst hcover)
    (canonicalRootedTileMeanLaw_of_populationTileMeanConvergence (A := A)
      (B := B) T pcloud qcloud base q α β coef probeFam Mst hmean)
    hF hcomplete hu ha hinj

end OTSelector.Reconstruction
