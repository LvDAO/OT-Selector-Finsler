import OTSelector.Reconstruction.FinslerOriginalParentChartProducer
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.C11FiniteLevelSeeds

/-!
# Window chart data from the pre-atlas rational chart construction

`FinslerOriginalParentChartProducer.lean` reduced the remaining producer gap to
`WindowChartData`: per window index, a chart datum, a compact parent core inside
the open chart domain, and the linear identification of the window seed label
space with the chart label space, with its label and curve equations.  This file
constructs that field from the pre-atlas rational chart construction.

## What the pre-atlas construction supplies

The pre-atlas construction is `exists_countable_calibrated_C11_family_cover`: a
countable family of charts, each carrying

* a compact core `K i` in the chart target with a C1,1 potential `G i` matching
  `u` and its derivative on `K i` and differentiating `u` there;
* a reachable compact endpoint set `B i` at distance `δ i > 0`, giving the
  calibration partners of every core point;
* an open chart neighbourhood `U i` of `K i` carrying ambient
  Euler--Lagrange curves `Γ i` with the initial and momentum conditions.

The finite level-seed construction `exists_finite_original_levelSeeds` supplies,
for every rational level `q`, finitely many level sections `σ x` on label balls
`ball 0 (a x)`, with all section properties (C1,1 regularity, immersion at the
label, injectivity, the rank equation, and the level equation).

## What this file proves

`PreAtlasChartDatum` is the exact per-window constructor datum extracted from the
pre-atlas family: a chart datum on a compact core with its partners, ambient
curves on the open neighbourhood, and a level section with label ball.  Then

* `preAtlasChartDatum_of_preAtlasFamily`: every chart index, rational level, core
  point at that level, and level section with label ball gives a
  `PreAtlasChartDatum`;
* `coreSectionChartData_of_preAtlasChartDatum`: the datum yields the
  `CoreSectionChartData` consumed by the refinement constructor once the four
  open-neighbourhood inputs are supplied (see the residual gap below);
* `windowChartData_of_coreSectionChartData`: a chart datum and compact core yield
  a `WindowChartData` for a constant `ℕ`-indexed window family;
* `exists_windowChartData_of_preAtlasFamily`: the combined construction of the
  atlas-level field from the pre-atlas family;
* `exists_preAtlas_finiteLevelSeeds`: the finite rational level-seed data on a
  chart of the pre-atlas family, `sectionData_of_finiteLevelSeeds`: a section of
  that family supplies the constructor's section data, and
  `exists_windowChartData_of_finiteLevelSeeds`: the resulting atlas-level field.

## Exact remaining sub-gap

The pre-atlas cover supplies the potential data and the calibration partners on
the *compact* core `K i` only, while `CoreSectionChartData` stores them on the
*open* chart domain `U i`.  The four extension inputs

* `hmatchU : EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ chart⁻¹)) U`,
* `hvalU : EqOn G (u ∘ chart⁻¹) U`,
* `hactualU : ∀ y ∈ U, HasFDerivAt (u ∘ chart⁻¹) (fderiv ℝ G y) y`,
* `hpartnersU : CalibratedPartners F u old δ U`

are therefore kept as explicit hypotheses.  They are exactly the "producer
geometry" fields: extending the C1,1 potential and its calibration partners from
the compact core to an open chart neighbourhood.  Everything else — chart datum,
compact core, level section, labels, curves and the linear label identification —
is constructed from the pre-atlas modules.  A second producer input is the choice
of a chart index, a rational level and a nonempty level set (a level section): the
finite level-seed data are parameterized by the chosen section `y ∈ J`.  Both are
producer/geometry inputs of the paper, not consequences of the cover theorem.
-/
open Set Function MeasureTheory Manifold OTSelector.Geometry
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe uE uM uZ

variable {E : Type uE} {M : Type uM} {Z : Type uZ}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## Calibration partners as a reusable predicate -/

/-- The calibration-partner condition at distance `δ` on a chart set: every point
of the set has a point at distance exactly `δ` below it and one at distance
exactly `δ` above it, both with potential difference `δ`. -/
def CalibratedPartners (F : ContinuousFinslerNorm E M) (u : M → ℝ) (old : M)
    (δ : ℝ) (S : Set E) : Prop :=
  letI : MetricSpace M := F.metricSpace
  ∀ x ∈ S, ∃ a b : M,
    dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
    u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
    dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
    u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ

/-! ## The pre-atlas chart family -/

/-- The calibrated interior of the potential at the manifold metric carried by
`F`. -/
def chartInterior (F : ContinuousFinslerNorm E M) (u : M → ℝ) : Set M :=
  letI : MetricSpace M := F.metricSpace
  OTSelector.Geometry.calibratedInterior u

/-- The countable calibrated C1,1 chart family produced by the pre-atlas rational
construction, with every field separated for direct use. -/
structure PreAtlasC11Family (F : ContinuousFinslerNorm E M) (u : M → ℝ) where
  ι : Type (max uE uM)
  countable : Countable ι
  old : ι → M
  K : ι → Set E
  U : ι → Set E
  G : ι → E → ℝ
  L : ι → ℝ≥0
  delta : ι → ℝ
  B : ι → Set M
  Gamma : ι → E → ℝ → M
  K_compact : ∀ i, IsCompact (K i)
  K_target : ∀ i, K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target
  G_contDiff : ∀ i, ContDiff ℝ 1 (G i)
  G_support : ∀ i, HasCompactSupport (G i)
  G_lip : ∀ i, LipschitzWith (L i) (fderiv ℝ (G i))
  G_val : ∀ i, EqOn (G i) (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i)
  G_match : ∀ i, EqOn (fderiv ℝ (G i))
    (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i)
  G_actual : ∀ i, ∀ x ∈ K i,
    HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (fderiv ℝ (G i) x) x
  cover : (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) = chartInterior F u
  delta_pos : ∀ i, 0 < delta i
  B_compact : ∀ i, IsCompact (B i)
  reach : ∀ i, CalibratedPartners F u (old i) (delta i) (K i)
  U_open : ∀ i, IsOpen (U i)
  K_subset_U : ∀ i, K i ⊆ U i
  U_target : ∀ i, U i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target
  Gamma_init : ∀ i, ∀ x ∈ U i,
    Gamma i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x
  Gamma_EL : ∀ i, ∀ x ∈ U i, F.IsEulerLagrangeOn (Gamma i x) univ
  Gamma_contDiff : ∀ i, ∀ x ∈ U i, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Gamma i x)
  Gamma_momentum : ∀ i, ∀ x ∈ U i,
    F.chartMomentumFamily (old i) (Gamma i) (x, 0) = (x, fderiv ℝ (G i) x)

/-- **The pre-atlas rational chart construction exists.**  This is the countable
calibrated C1,1 family cover, repackaged with its component properties separated. -/
theorem exists_preAtlasC11Family
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    Nonempty (PreAtlasC11Family F u) := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, delta, B, Gamma,
    hdata, hcover, hreach, hfamily⟩ :=
    hF.exists_countable_calibrated_C11_family_cover hcomplete hu
  exact ⟨
    { ι := ι
      countable := hcount
      old := old
      K := K
      U := U
      G := G
      L := L
      delta := delta
      B := B
      Gamma := Gamma
      K_compact := fun i => (hdata i).1
      K_target := fun i => (hdata i).2.1
      G_contDiff := fun i => (hdata i).2.2.1
      G_support := fun i => (hdata i).2.2.2.1
      G_lip := fun i => (hdata i).2.2.2.2.1
      G_val := fun i => (hdata i).2.2.2.2.2.1
      G_match := fun i => (hdata i).2.2.2.2.2.2.1
      G_actual := fun i => (hdata i).2.2.2.2.2.2.2
      cover := hcover
      delta_pos := fun i => (hreach i).1
      B_compact := fun i => (hreach i).2.1
      reach := fun i x hx => by
        obtain ⟨a, -, b, -, h⟩ := (hreach i).2.2 x hx
        exact ⟨a, b, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      U_open := fun i => (hfamily i).1
      K_subset_U := fun i => (hfamily i).2.1
      U_target := fun i => (hfamily i).2.2.1
      Gamma_init := fun i x hx => ((hfamily i).2.2.2 x hx).1
      Gamma_EL := fun i x hx => ((hfamily i).2.2.2 x hx).2.1
      Gamma_contDiff := fun i x hx => ((hfamily i).2.2.2 x hx).2.2.1
      Gamma_momentum := fun i x hx => ((hfamily i).2.2.2 x hx).2.2.2 }⟩

/-! ## The per-window chart datum of the constructor -/

/-- The exact constructor datum supplied by one window of the pre-atlas
construction: chart potential on the compact core, ambient curves on the open
chart neighbourhood, calibration partners on the core, and a level section with
its label ball.  This is precisely the hypothesis package of
`exists_levelSeedPatch_of_coreSection_with_coordinates`. -/
structure PreAtlasChartDatum (F : ContinuousFinslerNorm E M) (u : M → ℝ) where
  old : M
  G : E → ℝ
  L : ℝ≥0
  U : Set E
  U_open : IsOpen U
  U_target : U ⊆ (extChartAt 𝓘(ℝ, E) old).target
  Gamma : E → ℝ → M
  delta : ℝ
  delta_pos : 0 < delta
  p : E →L[ℝ] ℝ
  V : Set p.ker
  V_open : IsOpen V
  sigma : p.ker → E
  K : Set E
  K_compact : IsCompact K
  K_subset : K ⊆ U
  K_center : sigma 0 ∈ K
  G_contDiff : ContDiff ℝ 1 G
  G_lip : LipschitzWith L (fderiv ℝ G)
  match_K : EqOn (fderiv ℝ G)
    (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K
  val_K : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K
  actual_K : ∀ y ∈ K,
    HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y
  EL_U : ∀ x ∈ U, F.IsEulerLagrangeOn (Gamma x) univ
  init_U : ∀ x ∈ U, Gamma x 0 = (extChartAt 𝓘(ℝ, E) old).symm x
  mom_U : ∀ x ∈ U,
    F.chartMomentumFamily old Gamma (x, 0) = (x, fderiv ℝ G x)
  partners_K : CalibratedPartners F u old delta K
  sigma_contDiff : ContDiffOn ℝ 1 sigma V
  sigma_mapsTo : MapsTo sigma V U
  sigma_inj : InjOn sigma V
  dim : Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E
  zero_V : (0 : p.ker) ∈ V
  covector_eq : p = fderiv ℝ G (sigma 0)
  sigma_deriv : HasFDerivAt sigma p.ker.subtypeL 0
  sigma_imm : ∀ w ∈ V, Function.Injective (fderiv ℝ sigma w)
  q : ℚ
  G_level : ∀ w ∈ V, G (sigma w) = (q : ℝ)

/-- **Every chart of the pre-atlas family supplies a per-window chart datum.**
Fixing a chart index, a rational level, a core point at that level, and the level
section with its label ball produced by the finite level-seed construction, the
constructor datum is assembled from the pre-atlas fields. -/
def preAtlasChartDatum_of_preAtlasFamily
    (X : PreAtlasC11Family F u) (i : X.ι) (q : ℚ)
    (x : E) (hxK : x ∈ X.K i) (hxG : X.G i x = (q : ℝ))
    (a : ℝ) (ha : 0 < a)
    (sigma : (fderiv ℝ (X.G i) x).ker → E)
    (hsigma0 : sigma 0 = x)
    (hsigma : ContDiffOn ℝ 1 sigma (ball 0 a))
    (hsigmaU : MapsTo sigma (ball 0 a) (X.U i))
    (hlevel : ∀ w ∈ ball 0 a, X.G i (sigma w) = (q : ℝ))
    (hsigmaD : HasFDerivAt sigma (fderiv ℝ (X.G i) x).ker.subtypeL 0)
    (hinj : InjOn sigma (ball 0 a))
    (hdim : Module.finrank ℝ (fderiv ℝ (X.G i) x).ker + 1 = Module.finrank ℝ E)
    (himm : ∀ w ∈ ball 0 a, Function.Injective (fderiv ℝ sigma w)) :
    PreAtlasChartDatum F u :=
  { old := X.old i
    G := X.G i
    L := X.L i
    U := X.U i
    U_open := X.U_open i
    U_target := X.U_target i
    Gamma := X.Gamma i
    delta := X.delta i
    delta_pos := X.delta_pos i
    p := fderiv ℝ (X.G i) x
    V := ball 0 a
    V_open := isOpen_ball
    sigma := sigma
    K := X.K i
    K_compact := X.K_compact i
    K_subset := X.K_subset_U i
    K_center := by rw [hsigma0]; exact hxK
    G_contDiff := X.G_contDiff i
    G_lip := X.G_lip i
    match_K := X.G_match i
    val_K := X.G_val i
    actual_K := X.G_actual i
    EL_U := X.Gamma_EL i
    init_U := X.Gamma_init i
    mom_U := X.Gamma_momentum i
    partners_K := X.reach i
    sigma_contDiff := hsigma
    sigma_mapsTo := hsigmaU
    sigma_inj := hinj
    dim := hdim
    zero_V := mem_ball_self ha
    covector_eq := by rw [hsigma0]
    sigma_deriv := hsigmaD
    sigma_imm := himm
    q := q
    G_level := hlevel }

/-! ## From the per-window datum to the chart datum of the refinement engine -/

/-- **The `CoreSectionChartData` of the refinement engine from the pre-atlas
per-window datum.**  The potential data and the calibration partners are extended
from the compact core to the open chart neighbourhood: these are the four
explicit extension inputs. -/
def coreSectionChartData_of_preAtlasChartDatum (D : PreAtlasChartDatum F u)
    (hmatchU : EqOn (fderiv ℝ D.G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) D.old).symm)) D.U)
    (hvalU : EqOn D.G (u ∘ (extChartAt 𝓘(ℝ, E) D.old).symm) D.U)
    (hactualU : ∀ y ∈ D.U,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) D.old).symm) (fderiv ℝ D.G y) y)
    (hpartnersU : CalibratedPartners F u D.old D.delta D.U) :
    CoreSectionChartData F u :=
  { old := D.old
    G := D.G
    L := D.L
    U := D.U
    U_open := D.U_open
    U_target := D.U_target
    Γ := D.Gamma
    δ := D.delta
    δ_pos := D.delta_pos
    p := D.p
    V := D.V
    V_open := D.V_open
    σ := D.sigma
    G_contDiff := D.G_contDiff
    G_lip := D.G_lip
    match_U := hmatchU
    val_U := hvalU
    actual_U := hactualU
    EL_U := D.EL_U
    init_U := D.init_U
    mom_U := D.mom_U
    partners_U := hpartnersU
    σ_contDiff := D.sigma_contDiff
    σ_mapsTo := D.sigma_mapsTo
    σ_inj := D.sigma_inj
    dim := D.dim
    zero_V := D.zero_V
    covector_eq := D.covector_eq
    σ_deriv := D.sigma_deriv
    σ_imm := D.sigma_imm
    q := D.q
    G_level := D.G_level }

/-- **Chart datum plus compact core yields a `WindowChartData`.**  The refinement
constructor produces the seed patch, and the patch is the seed of a constant
`ℕ`-indexed window family whose `WindowChartData` records the chart datum, the
compact core and the linear label identification. -/
theorem windowChartData_of_coreSectionChartData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (C : CoreSectionChartData F u) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ C.U) (hcenter : C.σ 0 ∈ K) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨A, e, h1, h2, h3, h4⟩ :=
    exists_levelSeedPatch_of_chartData hF hcomplete hu C hK hKU hcenter
  obtain ⟨Dpres⟩ := A.c11_presentation
  have hmem : ((0 : ℝ), (0 : A.covector.ker)) ∈ ⋃ q ∈ A.centers, ball q (A.radius q) := by
    rw [A.local_cover]
    exact mem_prod.mpr ⟨mem_univ _, Dpres.zero_mem⟩
  obtain ⟨center, hcenter', -⟩ := mem_iUnion₂.mp hmem
  let W : F.CalibratedSeedWindow u :=
    { seed := A
      left := -1
      right := 1
      left_neg := by norm_num
      right_pos := by norm_num
      center := center
      center_mem := hcenter' }
  refine ⟨fun _ => W, ⟨?_⟩⟩
  exact
    { chartData := fun _ => C
      parentCore := fun _ => K
      parentCore_compact := fun _ => hK
      parentCore_subset := fun _ => hKU
      parentCore_center := fun _ => hcenter
      parentEquiv := fun _ => e
      parent_labels := fun _ => h2
      parent_curves := fun _ => h3 }

/-- **The atlas-level field from the per-window datum.**  With the four extension
inputs, the pre-atlas per-window datum yields a `WindowChartData` for a constant
window family. -/
theorem exists_windowChartData_of_preAtlasChartDatum
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (D : PreAtlasChartDatum F u)
    (hmatchU : EqOn (fderiv ℝ D.G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) D.old).symm)) D.U)
    (hvalU : EqOn D.G (u ∘ (extChartAt 𝓘(ℝ, E) D.old).symm) D.U)
    (hactualU : ∀ y ∈ D.U,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) D.old).symm) (fderiv ℝ D.G y) y)
    (hpartnersU : CalibratedPartners F u D.old D.delta D.U) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) :=
  windowChartData_of_coreSectionChartData hF hcomplete hu
    (coreSectionChartData_of_preAtlasChartDatum D hmatchU hvalU hactualU hpartnersU)
    D.K_compact D.K_subset D.K_center

/-! ## The construction from the pre-atlas rational chart construction -/

/-- **`WindowChartData` from the pre-atlas rational chart construction.**  Every
chart index of the countable calibrated C1,1 family, together with a rational
level, a core point at that level, the level section with its label ball supplied
by the finite level-seed construction, and the four open-neighbourhood extension
inputs of the potential and its calibration partners, yields a constant
`ℕ`-indexed window family carrying the atlas-level `WindowChartData`. -/
theorem exists_windowChartData_of_preAtlasFamily
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (X : PreAtlasC11Family F u) (i : X.ι) (q : ℚ)
    (x : E) (hxK : x ∈ X.K i) (hxG : X.G i x = (q : ℝ))
    (a : ℝ) (ha : 0 < a)
    (sigma : (fderiv ℝ (X.G i) x).ker → E)
    (hsigma0 : sigma 0 = x)
    (hsigma : ContDiffOn ℝ 1 sigma (ball 0 a))
    (hsigmaU : MapsTo sigma (ball 0 a) (X.U i))
    (hlevel : ∀ w ∈ ball 0 a, X.G i (sigma w) = (q : ℝ))
    (hsigmaD : HasFDerivAt sigma (fderiv ℝ (X.G i) x).ker.subtypeL 0)
    (hinj : InjOn sigma (ball 0 a))
    (hdim : Module.finrank ℝ (fderiv ℝ (X.G i) x).ker + 1 = Module.finrank ℝ E)
    (himm : ∀ w ∈ ball 0 a, Function.Injective (fderiv ℝ sigma w))
    (hmatchU : EqOn (fderiv ℝ (X.G i))
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (X.old i)).symm)) (X.U i))
    (hvalU : EqOn (X.G i) (u ∘ (extChartAt 𝓘(ℝ, E) (X.old i)).symm) (X.U i))
    (hactualU : ∀ y ∈ X.U i,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) (X.old i)).symm) (fderiv ℝ (X.G i) y) y)
    (hpartnersU : CalibratedPartners F u (X.old i) (X.delta i) (X.U i)) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) :=
  exists_windowChartData_of_preAtlasChartDatum hF hcomplete hu
    (preAtlasChartDatum_of_preAtlasFamily X i q x hxK hxG a ha sigma hsigma0 hsigma
      hsigmaU hlevel hsigmaD hinj hdim himm)
    hmatchU hvalU hactualU hpartnersU


/-! ## The finite rational level-seed data -/

/-- **The pre-atlas family supplies the finite rational level-seed data.**  Running
the finite original level-seed construction on a chart of the pre-atlas family at a
rational level gives the finite section family with label balls and all section
properties. -/
theorem exists_preAtlas_finiteLevelSeeds
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (X : PreAtlasC11Family F u) (i : X.ι) (q : ℚ) :
    ∃ (J : Finset ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}))
      (a : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}) → ℝ)
      (Cg : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}) → ℝ≥0)
      (sigma : ∀ y : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}),
        (fderiv ℝ (X.G i) (y : E)).ker → E),
      (∀ y ∈ J, 0 < a y ∧ sigma y 0 = (y : E) ∧
        ContDiffOn ℝ 1 (sigma y) (ball 0 (a y)) ∧
        LipschitzOnWith (Cg y) (sigma y) (ball 0 (a y)) ∧
        MapsTo (sigma y) (ball 0 (a y)) (X.U i) ∧
        (∀ w ∈ ball 0 (a y), X.G i (sigma y w) = (q : ℝ)) ∧
        (∀ w ∈ ball 0 (a y), sigma y w ∈ X.K i →
          u ((extChartAt 𝓘(ℝ, E) (X.old i)).symm (sigma y w)) = (q : ℝ)) ∧
        HasFDerivAt (sigma y) (fderiv ℝ (X.G i) (y : E)).ker.subtypeL 0 ∧
        InjOn (sigma y) (ball 0 (a y)) ∧
        Module.finrank ℝ (fderiv ℝ (X.G i) (y : E)).ker + 1 = Module.finrank ℝ E ∧
        ∀ w ∈ ball 0 (a y), Function.Injective (fderiv ℝ (sigma y) w)) ∧
      X.K i ∩ {y | u ((extChartAt 𝓘(ℝ, E) (X.old i)).symm y) = (q : ℝ)} =
        ⋃ y ∈ J, sigma y '' (ball 0 (a y) ∩ (sigma y) ⁻¹' (X.K i)) := by
  exact hF.exists_finite_original_levelSeeds hcomplete (X.old i) (X.K_compact i)
    (X.U_open i) (X.K_subset_U i) (X.U_target i) hu (X.G_contDiff i) (X.G_val i)
    (X.G_match i) (X.delta_pos i) (X.reach i) (q : ℝ)

/-- **A section of the finite level-seed family supplies the section data.** -/
theorem sectionData_of_finiteLevelSeeds
    (X : PreAtlasC11Family F u) (i : X.ι) (q : ℚ)
    {J : Finset ↥(X.K i ∩ {y | X.G i y = (q : ℝ)})}
    {a : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}) → ℝ}
    {Cg : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}) → ℝ≥0}
    {sigma : ∀ y : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}),
      (fderiv ℝ (X.G i) (y : E)).ker → E}
    (hdata : ∀ y ∈ J, 0 < a y ∧ sigma y 0 = (y : E) ∧
      ContDiffOn ℝ 1 (sigma y) (ball 0 (a y)) ∧
      LipschitzOnWith (Cg y) (sigma y) (ball 0 (a y)) ∧
      MapsTo (sigma y) (ball 0 (a y)) (X.U i) ∧
      (∀ w ∈ ball 0 (a y), X.G i (sigma y w) = (q : ℝ)) ∧
      (∀ w ∈ ball 0 (a y), sigma y w ∈ X.K i →
        u ((extChartAt 𝓘(ℝ, E) (X.old i)).symm (sigma y w)) = (q : ℝ)) ∧
      HasFDerivAt (sigma y) (fderiv ℝ (X.G i) (y : E)).ker.subtypeL 0 ∧
      InjOn (sigma y) (ball 0 (a y)) ∧
      Module.finrank ℝ (fderiv ℝ (X.G i) (y : E)).ker + 1 = Module.finrank ℝ E ∧
      ∀ w ∈ ball 0 (a y), Function.Injective (fderiv ℝ (sigma y) w))
    (y : ↥(X.K i ∩ {z | X.G i z = (q : ℝ)})) (hyJ : y ∈ J) :
    ∃ (a' : ℝ) (sigma' : (fderiv ℝ (X.G i) (y : E)).ker → E),
      0 < a' ∧ sigma' 0 = (y : E) ∧ ContDiffOn ℝ 1 sigma' (ball 0 a') ∧
      MapsTo sigma' (ball 0 a') (X.U i) ∧
      (∀ w ∈ ball 0 a', X.G i (sigma' w) = (q : ℝ)) ∧
      HasFDerivAt sigma' (fderiv ℝ (X.G i) (y : E)).ker.subtypeL 0 ∧
      InjOn sigma' (ball 0 a') ∧
      Module.finrank ℝ (fderiv ℝ (X.G i) (y : E)).ker + 1 = Module.finrank ℝ E ∧
      ∀ w ∈ ball 0 a', Function.Injective (fderiv ℝ sigma' w) := by
  obtain ⟨ha, h0, hσ, -, hmap, hlev, -, hder, hinj, hdim, himm⟩ := hdata y hyJ
  exact ⟨a y, sigma y, ha, h0, hσ, hmap, hlev, hder, hinj, hdim, himm⟩

/-- **The atlas-level field from the finite rational level-seed data.**  Choosing a
section of the finite level-seed family at a rational level, together with the four
open-neighbourhood extensions, yields a constant window family carrying
`WindowChartData`. -/
theorem exists_windowChartData_of_finiteLevelSeeds
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (X : PreAtlasC11Family F u) (i : X.ι) (q : ℚ)
    {J : Finset ↥(X.K i ∩ {y | X.G i y = (q : ℝ)})}
    {a : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}) → ℝ}
    {Cg : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}) → ℝ≥0}
    {sigma : ∀ y : ↥(X.K i ∩ {y | X.G i y = (q : ℝ)}),
      (fderiv ℝ (X.G i) (y : E)).ker → E}
    (hdata : ∀ y ∈ J, 0 < a y ∧ sigma y 0 = (y : E) ∧
      ContDiffOn ℝ 1 (sigma y) (ball 0 (a y)) ∧
      LipschitzOnWith (Cg y) (sigma y) (ball 0 (a y)) ∧
      MapsTo (sigma y) (ball 0 (a y)) (X.U i) ∧
      (∀ w ∈ ball 0 (a y), X.G i (sigma y w) = (q : ℝ)) ∧
      (∀ w ∈ ball 0 (a y), sigma y w ∈ X.K i →
        u ((extChartAt 𝓘(ℝ, E) (X.old i)).symm (sigma y w)) = (q : ℝ)) ∧
      HasFDerivAt (sigma y) (fderiv ℝ (X.G i) (y : E)).ker.subtypeL 0 ∧
      InjOn (sigma y) (ball 0 (a y)) ∧
      Module.finrank ℝ (fderiv ℝ (X.G i) (y : E)).ker + 1 = Module.finrank ℝ E ∧
      ∀ w ∈ ball 0 (a y), Function.Injective (fderiv ℝ (sigma y) w))
    (y : ↥(X.K i ∩ {z | X.G i z = (q : ℝ)})) (hyJ : y ∈ J)
    (hmatchU : EqOn (fderiv ℝ (X.G i))
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (X.old i)).symm)) (X.U i))
    (hvalU : EqOn (X.G i) (u ∘ (extChartAt 𝓘(ℝ, E) (X.old i)).symm) (X.U i))
    (hactualU : ∀ z ∈ X.U i,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) (X.old i)).symm) (fderiv ℝ (X.G i) z) z)
    (hpartnersU : CalibratedPartners F u (X.old i) (X.delta i) (X.U i)) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨a', sigma', ha, h0, hσ, hmap, hlev, hder, hinj, hdim, himm⟩ :=
    sectionData_of_finiteLevelSeeds X i q hdata y hyJ
  exact exists_windowChartData_of_preAtlasFamily hF hcomplete hu X i q (y : E)
    y.property.1 y.property.2 a' ha sigma' h0 hσ hmap hlev hder hinj hdim himm
    hmatchU hvalU hactualU hpartnersU

end OTSelector.Reconstruction
