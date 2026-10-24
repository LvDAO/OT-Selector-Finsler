import OTSelector.Probability.FinslerAtlasCoordinateLaw
import OTSelector.Reconstruction.FinslerPopulationSeedIntensityLaw

/-!
# The three atlas coordinate law facts: product law, mark marginal, cube law

This module attacks the three remaining law facts of
`OTSelector.Probability.FinslerAtlasCoordinateLaw` and isolates, for each of them,
the exact atlas input and the precise missing analytic statement.

## Product law, mark marginal and independence

`three_reductions_of_map_prod_eq_prod` proves the general measure-theoretic
equivalence used below: for a finite measure `ρ`, measurable maps `f`, `g` and
probability measures `μ`, `ν`, a product law
`ρ.map (fun x ↦ (f x, g x)) = μ.prod ν` implies simultaneously

* `ρ.map f = μ` (the first marginal),
* `ρ.map g = ν` (the second marginal),
* `IndepFun f g ρ` (independence).

The proof of independence is the product-map characterization
`indepFun_iff_map_prod_eq_prod_map_map`; the marginals are the projections of the
product measure (`Measure.map_fst_prod`, `Measure.map_snd_prod`).

`atlas_three_reductions_of_product_law` instantiates this with the concrete atlas
maps `atlasSeedCoord S e a` and `atlasSeedMark mark` and the normalized tile law
`(lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})`.  It produces exactly the
three hypotheses `hcube`, `hmarkLaw`, `hindep` of
`map_normalized_label_atlasSeedMarkMap_eq_markedOnePointLaw`.  Consequently
`physical_normalized_tile_atlasSeedMarkMap_eq_markedOnePointLaw_of_product_law`
proves the physical identification from the single joint product law
`(cubeMeasure (Fin q) 1).prod α`.

Thus the joint product law is a *sufficient and essentially equivalent* form of
the three reductions.  The remaining geometric work is precisely to derive that
product law from the reconstruction atlas; see the gap map below.

## The exact atlas factorization

The reconstruction lane provides the following factorizations.

* `PopulationConditionalWindowLaw.window_law` / `joint_law` / `conditional_law`
  (`FinslerPopulationConditionalLaw`): the physical joint law of `(a x, u x)` is
  `(labelReference.prod volume).withDensity populationConditionalDensity`.  The
  base measure is a product of the label reference and Lebesgue measure, but the
  density `populationConditionalDensity` is a sum over windows of
  `rnDeriv * windowDensity` and does not factor into a function of the label
  times a function of the clock.  In particular these fields do not identify the
  law of the *mark*, which in the atlas model is read from the common label `z`.
* `original_seed_core_joint_eq_compProd`
  (`FinslerPopulationSeedIntensityLaw`): restricted to a label core `K`, the law
  of `(populationSeedRootLabelValue S a (a x), u x)` is
  `HaarDensity ⊗ₘ populationSeedCoordinateClockKernel`, a product of the seed
  coordinate law with a Markov kernel in the clock.  This is the closest exact
  product structure in the atlas.  `compProd_eq_prod_of_ae_eq_const` turns a
  constant kernel into a plain product, and
  `original_seed_core_joint_eq_prod_of_constant_kernel` records the resulting
  product identity for the atlas field.  It gives independence of the seed
  coordinate from the clock once the conditional clock kernel is constant in the
  seed label; it does not give independence of the seed coordinate from an
  arbitrary label mark `mark : Z → A`.

## Cube law

`normalized_seed_coordinate_law_eq_cubeMeasure` derives the cube law (i) from the
atlas intensity theorem `map_populationSeedCore_eq_withDensity` under exactly two
explicit hypotheses:

* `hconst`: the Haar density `populationSeedPieceHaarDensity` is constant
  `c ≠ 0, ∞` on the retained label image `populationSeedRootLabelValue S a '' K`;
* `hhaar`: the normalized Haar measure restricted to the retained labels, pushed
  through the basis coordinate `e`, is `cubeMeasure (Fin q) 1`.

The general scalar cancellation `ennreal_inv_mul_mul_eq_inv` shows that a
constant density disappears under normalization, so the normalized coordinate
law is exactly the normalized Haar pushforward.  `hhaar` is where the atlas
normalization `S.normalization` and the basis `e` enter: `S.normalization` and the
Haar measure `κ j` (supplied by `populationConditionalWindowLaw_of_atlas` as
`IsAddHaarMeasure`) determine the pushforward up to a constant, and the
normalization to the unit cube is the missing identification.

## Gap map

* (ii) mark marginal / (iii) independence: supplied by the single product law
  `hprod` of `atlas_three_reductions_of_product_law`.  The current atlas does not
  prove `hprod`: the only exact product factorizations are `label × clock`
  (`original_seed_core_joint_eq_compProd`, product with a kernel) and the product
  base `labelReference.prod volume` with a non-product density
  (`PopulationConditionalWindowLaw.joint_law`).  Note that
  `FinslerPopulationConditionalSeparation` supplies only compact support
  separation of the original conditional clock laws
  (`ConditionalClockSupportBounds`, `PopulationConditionalSeparationLaw`); it
  contains no coordinate/mark product factorization.  To close the gap one must
  either (a) take the model mark to be a function of the clock and assume the
  conditional clock kernel is constant in the seed label, or (b) add a product
  decomposition of the common label law `lambda` under which `atlasSeedCoord` and
  `atlasSeedMark` are coordinate projections.
* (i) cube law: reduced by `normalized_seed_coordinate_law_eq_cubeMeasure` to the
  constancy of `populationSeedPieceHaarDensity` on `r '' K` and the normalized
  Haar pushforward `hhaar`.  The atlas supplies the Haar measure `κ j` and the
  normalization `S.normalization`; the uniform density and the cube
  identification are the remaining analytic inputs.
-/

open MeasureTheory ProbabilityTheory Set Function Manifold OTSelector.Geometry
open OTSelector.Reconstruction
open scoped BigOperators NNReal ENNReal Topology ContDiff

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## General product-law reductions -/

section ProductLaw

variable {Ω X A : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace A]
  {ρ : Measure Ω} [IsFiniteMeasure ρ] {μ : Measure X} [IsProbabilityMeasure μ]
  {ν : Measure A} [IsProbabilityMeasure ν] {f : Ω → X} {g : Ω → A}

/-- The first marginal of a joint product law. -/
theorem map_fst_eq_of_map_prod_eq_prod (hf : Measurable f) (hg : Measurable g)
    (hprod : ρ.map (fun x ↦ (f x, g x)) = μ.prod ν) :
    ρ.map f = μ := by
  have hpair : Measurable (fun x ↦ (f x, g x)) := hf.prodMk hg
  calc
    ρ.map f = (ρ.map (fun x ↦ (f x, g x))).map Prod.fst := by
      rw [Measure.map_map measurable_fst hpair]
      rfl
    _ = (μ.prod ν).map Prod.fst := by rw [hprod]
    _ = (ν univ) • μ := Measure.map_fst_prod
    _ = μ := by rw [measure_univ, one_smul]

/-- The second marginal of a joint product law. -/
theorem map_snd_eq_of_map_prod_eq_prod (hf : Measurable f) (hg : Measurable g)
    (hprod : ρ.map (fun x ↦ (f x, g x)) = μ.prod ν) :
    ρ.map g = ν := by
  have hpair : Measurable (fun x ↦ (f x, g x)) := hf.prodMk hg
  calc
    ρ.map g = (ρ.map (fun x ↦ (f x, g x))).map Prod.snd := by
      rw [Measure.map_map measurable_snd hpair]
      rfl
    _ = (μ.prod ν).map Prod.snd := by rw [hprod]
    _ = (μ univ) • ν := Measure.map_snd_prod
    _ = ν := by rw [measure_univ, one_smul]

/-- Independence from a joint product law. -/
theorem indepFun_of_map_prod_eq_prod (hf : Measurable f) (hg : Measurable g)
    (hprod : ρ.map (fun x ↦ (f x, g x)) = μ.prod ν) :
    IndepFun f g ρ :=
  (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr <| by
    rw [hprod, map_fst_eq_of_map_prod_eq_prod hf hg hprod,
      map_snd_eq_of_map_prod_eq_prod hf hg hprod]

/-- A joint product law gives both marginals and independence. -/
theorem three_reductions_of_map_prod_eq_prod (hf : Measurable f) (hg : Measurable g)
    (hprod : ρ.map (fun x ↦ (f x, g x)) = μ.prod ν) :
    ρ.map f = μ ∧ ρ.map g = ν ∧ IndepFun f g ρ :=
  ⟨map_fst_eq_of_map_prod_eq_prod hf hg hprod,
    map_snd_eq_of_map_prod_eq_prod hf hg hprod,
    indepFun_of_map_prod_eq_prod hf hg hprod⟩

end ProductLaw

/-! ## Projection independence on a product label space -/

section ProductSpace

/-- On a product space, the two coordinate projections are independent. -/
theorem indepFun_fst_snd_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] :
    IndepFun (fun p : X × Y ↦ p.1) (fun p : X × Y ↦ p.2) (μ.prod ν) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- Any measurable functions of the two coordinate projections are independent
under the product law. -/
theorem indepFun_comp_fst_snd_prod {X Y X' A : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace A]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → X') (g : Y → A) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun p : X × Y ↦ f p.1) (fun p : X × Y ↦ g p.2) (μ.prod ν) :=
  (indepFun_fst_snd_prod μ ν).comp hf hg

end ProductSpace

/-! ## The atlas product law and its three reductions -/

section AtlasProductLaw

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- **The atlas product law gives the three reductions.**  If the normalized
label tile law pushes forward under the atlas mark map to the product of the
uniform cube law and `α`, then its coordinate marginal is the cube law, its mark
marginal is `α`, and the coordinate and the mark are independent. -/
theorem atlas_three_reductions_of_product_law {q : ℕ}
    (S : F.CalibratedLevelSeedPatch u) (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (a : M → Z) {A : Type*} [MeasurableSpace A] (mark : Z → A)
    (α : Measure A) [IsProbabilityMeasure α]
    (labZ : Z → ι) (c : ι) (lam : Measure Z) [IsProbabilityMeasure lam]
    (hρ : lam (labZ ⁻¹' {c}) ≠ 0)
    (hcoord : Measurable (atlasSeedCoord S e a)) (hmark : Measurable mark)
    (hprod : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMarkMap S e a mark) = (cubeMeasure (Fin q) 1).prod α) :
    ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedCoord S e a) = cubeMeasure (Fin q) 1 ∧
      ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMark mark) = α ∧
      IndepFun (atlasSeedCoord S e a) (atlasSeedMark mark)
        ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})) := by
  haveI := isProbabilityMeasure_inv_smul_restrict lam hρ
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure one_pos
  change ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
      (fun z ↦ (atlasSeedCoord S e a z, atlasSeedMark mark z)) =
        (cubeMeasure (Fin q) 1).prod α at hprod
  exact three_reductions_of_map_prod_eq_prod hcoord
    (measurable_atlasSeedMark mark hmark) hprod

/-- **The physical atlas identification from the joint product law.**  The
normalized physical tile law pushes forward under `atlasSeedMarkMap` to the marked
one-point law, assuming only the joint product law of the normalized label law. -/
theorem physical_normalized_tile_atlasSeedMarkMap_eq_markedOnePointLaw_of_product_law
    {q : ℕ} (S : F.CalibratedLevelSeedPatch u)
    (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) (a : M → Z)
    {A : Type*} [MeasurableSpace A] (mark : Z → A) (α : Measure A)
    [IsProbabilityMeasure α]
    (labZ : Z → ι) (hlabZ : Measurable labZ) (c : ι)
    (η : Measure M) [IsProbabilityMeasure η] (lam : Measure Z) [IsProbabilityMeasure lam]
    (ha : Measurable a) (hlaw : η.map a = lam)
    (hρ : lam (labZ ⁻¹' {c}) ≠ 0)
    (hmarkMap : Measurable (atlasSeedMarkMap S e a mark))
    (hcoord : Measurable (atlasSeedCoord S e a)) (hmark : Measurable mark)
    (hprod : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMarkMap S e a mark) = (cubeMeasure (Fin q) 1).prod α) :
    ((η (a ⁻¹' (labZ ⁻¹' {c})))⁻¹ • η.restrict (a ⁻¹' (labZ ⁻¹' {c}))).map
        (fun x ↦ atlasSeedMarkMap S e a mark (a x)) =
      markedOnePointLaw q A α := by
  obtain ⟨hcube, hmarkLaw, hindep⟩ :=
    atlas_three_reductions_of_product_law S e a mark α labZ c lam hρ hcoord hmark hprod
  exact physical_normalized_tile_atlasSeedMarkMap_eq_markedOnePointLaw S e a mark α
    labZ hlabZ c η lam ha hlaw hρ hmarkMap hcoord hmark hcube hmarkLaw hindep

/-- **Target atlas identification from the joint product law.**  The target
analogue with the target common-label map `b : M → Z`, the target mark space `B`
and the target mark law `β`. -/
theorem physical_normalized_target_tile_atlasSeedMarkMap_eq_markedOnePointLaw_of_product_law
    {q : ℕ} (S : F.CalibratedLevelSeedPatch u)
    (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) (b : M → Z)
    {B : Type*} [MeasurableSpace B] (mark : Z → B) (β : Measure B)
    [IsProbabilityMeasure β]
    (labZ : Z → ι) (hlabZ : Measurable labZ) (c : ι)
    (η : Measure M) [IsProbabilityMeasure η] (lam : Measure Z) [IsProbabilityMeasure lam]
    (hb : Measurable b) (hlaw : η.map b = lam)
    (hρ : lam (labZ ⁻¹' {c}) ≠ 0)
    (hmarkMap : Measurable (atlasSeedMarkMap S e b mark))
    (hcoord : Measurable (atlasSeedCoord S e b)) (hmark : Measurable mark)
    (hprod : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMarkMap S e b mark) = (cubeMeasure (Fin q) 1).prod β) :
    ((η (b ⁻¹' (labZ ⁻¹' {c})))⁻¹ • η.restrict (b ⁻¹' (labZ ⁻¹' {c}))).map
        (fun y ↦ atlasSeedMarkMap S e b mark (b y)) =
      markedOnePointLaw q B β := by
  obtain ⟨hcube, hmarkLaw, hindep⟩ :=
    atlas_three_reductions_of_product_law S e b mark β labZ c lam hρ hcoord hmark hprod
  exact physical_normalized_target_tile_atlasSeedMarkMap_eq_markedOnePointLaw S e b mark β
    labZ hlabZ c η lam hb hlaw hρ hmarkMap hcoord hmark hcube hmarkLaw hindep

end AtlasProductLaw

/-! ## The exact atlas factorization: a constant clock kernel gives a product -/

section CompProdLaw

/-- A composition product with an almost everywhere constant kernel is the
product of the base measure and the constant measure. -/
theorem compProd_eq_prod_of_ae_eq_const {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (ρ : Measure Ω) [SFinite ρ] (k : Kernel Ω Ω')
    [IsSFiniteKernel k] (ν : Measure Ω') [SFinite ν]
    (h : k =ᵐ[ρ] Kernel.const Ω ν) :
    ρ ⊗ₘ k = ρ.prod ν := by
  rw [← Measure.compProd_const (α := Ω), Measure.compProd_congr h]

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  [IsFiniteMeasure lambda]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFactsClockMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **Constant-clock-kernel product identity.**  If the retained conditional clock
kernel is almost everywhere constant in the seed label, then the physical joint
law of the seed coordinate and the clock is a plain product.  This is the exact
product structure supplied by the atlas field
`original_seed_core_joint_eq_compProd`. -/
theorem original_seed_core_joint_eq_prod_of_constant_kernel
    (η : Measure M) [IsFiniteMeasure η] (j : ℕ) [SigmaFinite (κ j)] {K : Set Z}
    (hK : MeasurableSet K) (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (hlabel : η.map a = lambda) (ν : Measure ℝ) [SFinite ν]
    (hconst : populationSeedCoordinateClockKernel (P j).seed a ha (condDistrib u a η)
      =ᵐ[(((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).withDensity
          (populationSeedPieceHaarDensity P a κ lambda j))]
        Kernel.const (P j).seed.covector.ker ν) :
    (η.restrict (a ⁻¹' K)).map
        (fun x ↦ (populationSeedRootLabelValue (P j).seed a (a x), u x)) =
      (((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).withDensity
        (populationSeedPieceHaarDensity P a κ lambda j)).prod ν := by
  rw [original_seed_core_joint_eq_compProd P a κ lambda hF hcomplete hu ha hinj η hlabel
    j hK hsub]
  exact compProd_eq_prod_of_ae_eq_const _ _ _ hconst

end CompProdLaw

/-! ## The cube law from a constant Haar density -/

section CubeLaw

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFactsCubeMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

omit hF hcomplete hu ha hinj in
/-- In `ℝ≥0∞`, a nonzero finite constant cancels under normalization:
`(c * m)⁻¹ * c = m⁻¹`. -/
theorem ennreal_inv_mul_mul_eq_inv {c m : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    (c * m)⁻¹ * c = m⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_assoc,
    mul_comm m⁻¹ c, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]

/-- **Cube law from the atlas intensity.**  If the Haar density of a retained
label core is constant `c ≠ 0, ∞` and the normalized Haar pushforward under the
basis coordinate `e` is the uniform cube law, then the normalized coordinate law
of the core is the uniform cube law.

The atlas input is `map_populationSeedCore_eq_withDensity`; the density
`populationSeedPieceHaarDensity` cancels under normalization.  The two remaining
hypotheses are stated explicitly: `hconst` is the uniformity of the Haar density,
`hhaar` is the normalized Haar pushforward (where `S.normalization` and `e`
enter). -/
theorem normalized_seed_coordinate_law_eq_cubeMeasure {q : ℕ} (j : ℕ)
    [SigmaFinite lambda] [SigmaFinite (κ j)]
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    {c : ℝ≥0∞}
    (hconst : populationSeedPieceHaarDensity P a κ lambda j
      =ᵐ[((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K))]
        (fun _ ↦ c))
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hhaar : (κ j (populationSeedRootLabelValue (P j).seed a '' K))⁻¹ •
        (((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).map e) =
          cubeMeasure (Fin q) 1) :
    (lambda K)⁻¹ • (lambda.restrict K).map
        (atlasSeedCoord (P j).seed e a) = cubeMeasure (Fin q) 1 := by
  let S := (P j).seed
  let r := populationSeedRootLabelValue S a
  let μ := (κ j).restrict (r '' K)
  let d := populationSeedPieceHaarDensity P a κ lambda j
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hlaw : (lambda.restrict K).map r = μ.withDensity d :=
    map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj j hK hsub
  have hdens : μ.withDensity d = c • μ := by
    rw [← withDensity_const c]
    exact withDensity_congr_ae hconst
  have hmap : (lambda.restrict K).map (atlasSeedCoord S e a) = c • μ.map e := by
    calc
      (lambda.restrict K).map (atlasSeedCoord S e a)
          = ((lambda.restrict K).map r).map e := by
            rw [Measure.map_map e.continuous.measurable hr]
            rfl
      _ = (μ.withDensity d).map e := by rw [hlaw]
      _ = (c • μ).map e := by rw [hdens]
      _ = c • μ.map e := Measure.map_smul c μ e
  have hmass0 : ((lambda.restrict K).map r) univ = lambda K := by
    rw [Measure.map_apply hr MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  have hmass : lambda K = c * μ univ := by
    calc
      lambda K = ((lambda.restrict K).map r) univ := hmass0.symm
      _ = (μ.withDensity d) univ := by rw [hlaw]
      _ = (c • μ) univ := by rw [hdens]
      _ = c * μ univ := by rw [Measure.smul_apply, smul_eq_mul]
  calc
    (lambda K)⁻¹ • (lambda.restrict K).map (atlasSeedCoord S e a)
        = (lambda K)⁻¹ • (c • μ.map e) := by rw [hmap]
    _ = ((lambda K)⁻¹ * c) • μ.map e := by rw [smul_smul]
    _ = (μ univ)⁻¹ • μ.map e := by
          rw [hmass, ennreal_inv_mul_mul_eq_inv hc0 hctop]
    _ = cubeMeasure (Fin q) 1 := by
          have hμuniv : μ univ = κ j (r '' K) := by
            change (κ j).restrict (r '' K) univ = κ j (r '' K)
            exact Measure.restrict_apply_univ (r '' K)
          rw [hμuniv]
          exact hhaar

end CubeLaw

end OTSelector.Probability
