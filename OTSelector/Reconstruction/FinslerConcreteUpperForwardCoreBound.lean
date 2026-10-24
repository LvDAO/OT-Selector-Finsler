import OTSelector.Reconstruction.FinslerConcreteUpperClassForwardGeometry
import OTSelector.Reconstruction.MarkedStationaryValueLegalClassValue

/-! Original forward type cores bound the frozen legal optimum. The leading
energy coefficient depends on the relative Taylor error; fine-class complexity
is confined to the genuine cardinality deficit correction. -/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {J : Type*} [Fintype J]

/-- A genuine legal core converts physical energy into a model upper bound.
Only the maximum-cardinality deficit pays the finite class augmentation cost. -/
theorem legalMaximumValue_le_inverse_relative_core
    (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (physical frozen probe : Fin m → Fin n → ℝ)
    {ρ G edgeBound : ℝ} (hρ : ρ < 1) (_hG : 0 ≤ G) (hB : 0 ≤ edgeBound)
    (hrelative : ∀ e ∈ σ.edges,
      |physical e.1 e.2 - frozen e.1 e.2| ≤ ρ * frozen e.1 e.2)
    (hprobe : ∀ i j, |probe i j| ≤ G) (tilt : ℝ)
    (hedge : ∀ i j, |frozen i j + tilt * probe i j| ≤ edgeBound) :
    legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * probe i j) ≤
      σ.cost physical / (1 - ρ) + (σ.card : ℝ) * (|tilt| * G) +
      ((legalMaximumCard allowed - σ.card : ℕ) : ℝ) *
        ((2 * (Fintype.card J : ℝ) - 1) * edgeBound) := by
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  have hcore : σ.cost (fun i j ↦ frozen i j + tilt * probe i j) ≤
      σ.cost physical / (1 - ρ) + (σ.card : ℝ) * (|tilt| * G) := by
    have hpoint (e) (he : e ∈ σ.edges) :
        frozen e.1 e.2 + tilt * probe e.1 e.2 ≤
          physical e.1 e.2 / (1 - ρ) + |tilt| * G := by
      have hr := (abs_le.mp (hrelative e he)).1
      have hf : frozen e.1 e.2 ≤ physical e.1 e.2 / (1 - ρ) :=
        (le_div_iff₀ hden).mpr (by nlinarith only [hr])
      have hp : tilt * probe e.1 e.2 ≤ |tilt| * G := by
        calc _ ≤ |tilt * probe e.1 e.2| := le_abs_self _
          _ = |tilt| * |probe e.1 e.2| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hprobe _ _) (abs_nonneg _)
      exact add_le_add hf hp
    have hs := Finset.sum_le_sum hpoint
    simpa only [OTSelector.PartialMatching.cost, Finset.sum_add_distrib,
      Finset.sum_div, Finset.sum_const, nsmul_eq_mul, OTSelector.PartialMatching.card] using hs
  exact (legalMaximumValue_le_cost_add_class_deficit σ hσ sourceClass sourceAllows
    hallowed _ hB hedge).trans (add_le_add hcore (le_refl _))

end OTSelector.Reconstruction.PartialMatching

namespace OTSelector.Reconstruction.PopulationLocalPressureCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Actual stored compact seed labels bound every unscaled frozen edge. This
constant is fixed before finite clouds and their empirical scale are chosen. -/
theorem exists_original_clockClass_pair_bound
    (i : Fin D.haar.continuous.count) {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width)
    (ref : (D.haar.continuous.coefficient i).roots) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let bW := Module.finBasis ℝ S.covector.ker
    ∃ edgeBound ≥ 0, ∀ j k, ∀ z ∈ C.roots, ∀ z' ∈ C.roots,
      |C.clockClassKinetic Q ref.val j k (bW.equivFun (R z' - R z))| ≤ edgeBound := by
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let bW := Module.finBasis ℝ S.covector.ker
  let q := Module.finrank ℝ S.covector.ker
  have hcompact : IsCompact (bW.equivFunL '' (R '' C.roots)) := by
    have h := (D.haar.intensity i).compact_labels.image bW.equivFunL.continuous
    simpa only [D.haar.intensity_roots i] using h
  obtain ⟨B, hB, hnorm⟩ := hcompact.isBounded.exists_pos_norm_lt
  obtain ⟨K, hK, hkernel⟩ := C.exists_clockClassKinetic_bound Q ref.val ref.property
  refine ⟨K * ((q : ℝ) * (2 * B) ^ 2), by positivity, ?_⟩
  intro j k z hz z' hz'
  have hn (z) (hz : z ∈ C.roots) : ‖bW.equivFun (R z)‖ < B :=
    hnorm _ (mem_image_of_mem bW.equivFunL (mem_image_of_mem R hz))
  have hv : ‖bW.equivFun (R z' - R z)‖ ≤ 2 * B := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (by linarith [hn z hz, hn z' hz'])
  have hsum : (∑ l, (bW.equivFun (R z' - R z) l) ^ 2) ≤ (q : ℝ) * (2 * B) ^ 2 := by
    calc _ ≤ ∑ _l : Fin q, (2 * B) ^ 2 := by
          apply Finset.sum_le_sum
          intro l _
          have ha : |bW.equivFun (R z' - R z) l| ≤ 2 * B :=
            (show |bW.equivFun (R z' - R z) l| ≤ ‖bW.equivFun (R z' - R z)‖ from
              by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (bW.equivFun (R z' - R z)) l).trans hv
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (bW.equivFun (R z' - R z) l))
            (by positivity : 0 ≤ 2 * B)).mpr ha
      _ = _ := by simp
  exact (hkernel j k _).trans (mul_le_mul_of_nonneg_left hsum hK)

/-- Actual geometry turns every forward original type core on active classes
into a legal frozen core and a quantitative maximum-cardinality upper bound.
All class-edge constants are fixed before the finite sample or its scale. -/
theorem exists_original_forward_clockClass_core_bounds
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε probeError : ℝ} (hε : 0 < ε) (hprobeError : 0 < probeError)
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1) :
    let C := D.haar.continuous.coefficient i
    ∃ (Q : C.roots → FiniteScalarBins I globalGap) (U : C.roots → Set (ℚ → M)),
      (∀ ref, IsOpen (U ref) ∧ ref.val ∈ U ref) ∧
      ∀ ref, ∃ edgeBound ≥ 0,
      ∀ (m n : ℕ) (zs : Fin m → (ℚ → M)) (zt : Fin n → (ℚ → M))
      (cs : Fin m → Fin (Q ref).count) (ct : Fin n → Fin (Q ref).count)
      (ts : Fin m → ℝ) (tt : Fin n → ℝ),
      (∀ j, zs j ∈ C.roots ∩ U ref) → (∀ k, zt k ∈ C.roots ∩ U ref) →
      (∀ j, ts j ∈ (Q ref).cell (cs j)) → (∀ k, tt k ∈ (Q ref).cell (ct k)) →
      (∀ j, ∃ k, C.clockClassAllowed (Q ref) (cs j) k) →
      (∀ k, ∃ j, C.clockClassAllowed (Q ref) j (ct k)) →
      (∀ j, D.corePoint i (zs j, ts j) ∈ A) →
      (∀ k, D.corePoint i (zt k, tt k) ∈ B) →
      ∀ σ : OTSelector.PartialMatching m n,
      (∀ e ∈ σ.edges, ts e.1 < tt e.2) → ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let d := fun j k ↦ (Module.finBasis ℝ S.covector.ker).equivFun (R (zt k) - R (zs j))
      let allowed := Finset.univ.filter (fun e : Fin m × Fin n ↦
        C.clockClassAllowed (Q ref) (cs e.1) (ct e.2))
      let frozen := fun j k ↦ scale * C.clockClassKinetic (Q ref) ref.val (cs j) (ct k) (d j k)
      let probe := fun j k ↦ C.clockClassProbe (Q ref) ref.val ref.property f (cs j) (ct k)
      PartialMatching.IsLegal allowed σ ∧
      PartialMatching.legalMaximumValue allowed (fun j k ↦ frozen j k + tilt * probe j k) ≤
        σ.cost (fun j k ↦ scale * populationSeedPairDeficit S (ts j, tt k) (R (zs j), R (zt k))) /
          (1 - (3 * ε + 2 * ε ^ 2)) + (σ.card : ℝ) * (|tilt| * ‖f‖) +
        ((PartialMatching.legalMaximumCard allowed - σ.card : ℕ) : ℝ) *
          ((2 * ((Q ref).count : ℝ) - 1) * (scale * edgeBound + |tilt| * ‖f‖)) := by
  classical
  obtain ⟨Q, U, hU, houter, hregion, hgeometry⟩ :=
    D.exists_full_original_clockClass_geometry_with_forward_region hF hcomplete hu ha hinj
      i f f.continuous hgap hsep hscreen hI hglobalGap hε hprobeError
  refine ⟨Q, U, hU, fun ref ↦ ?_⟩
  obtain ⟨edgeBound, hEdge0, hEdge⟩ := D.exists_original_clockClass_pair_bound i (Q ref) ref
  refine ⟨edgeBound, hEdge0, ?_⟩
  intro m n zs zt cs ct ts tt hzs hzt hts htt hactiveS hactiveT hAs hBt σ hforward scale hscale tilt
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let d := fun j k ↦ (Module.finBasis ℝ S.covector.ker).equivFun (R (zt k) - R (zs j))
  let allowed := Finset.univ.filter (fun e : Fin m × Fin n ↦
    C.clockClassAllowed (Q ref) (cs e.1) (ct e.2))
  let frozen := fun j k ↦ scale * C.clockClassKinetic (Q ref) ref.val (cs j) (ct k) (d j k)
  let probe := fun j k ↦ C.clockClassProbe (Q ref) ref.val ref.property f (cs j) (ct k)
  have hSouter (j) : ts j ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    obtain ⟨k, hk⟩ := hactiveS j
    have hp := C.clockClassReference_mem (Q ref) hk
    exact (houter ref (cs j) k hk (ts j) (hts j) _ hp.2.2).1
  have hTouter (k) : tt k ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    obtain ⟨j, hj⟩ := hactiveT k
    have hp := C.clockClassReference_mem (Q ref) hj
    exact (houter ref j (ct k) hj _ hp.2.1 (tt k) (htt k)).2
  have hlegal : PartialMatching.IsLegal allowed σ := by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨(ts e.1, tt e.2), hregion ref (zs e.1) (hzs e.1) (zt e.2) (hzt e.2)
      (ts e.1) (hSouter e.1) (tt e.2) (hTouter e.2) (hforward e he) (hAs e.1) (hBt e.2),
      hts e.1, htt e.2⟩
  refine ⟨hlegal, ?_⟩
  have hbound := PartialMatching.legalMaximumValue_le_inverse_relative_core allowed σ hlegal cs
    (fun j k ↦ C.clockClassAllowed (Q ref) j (ct k))
    (fun j k ↦ by simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and])
    (fun j k ↦ scale * populationSeedPairDeficit S (ts j, tt k) (R (zs j), R (zt k)))
    frozen probe hsmall (norm_nonneg f) (by positivity : 0 ≤ scale * edgeBound + |tilt| * ‖f‖)
    ?_ (fun j k ↦ C.clockClassProbe_abs_le (Q ref) ref.val ref.property f (cs j) (ct k)) tilt ?_
  · simpa only [Fintype.card_fin] using hbound
  · intro e he
    have hallowed := (Finset.mem_filter.mp (hlegal he)).2
    have hcost := (hgeometry ref (zs e.1) (hzs e.1) (zt e.2) (hzt e.2)
      (cs e.1) (ct e.2) hallowed (ts e.1) (hts e.1) (tt e.2) (htt e.2) (hAs e.1) (hBt e.2)).2.1
    dsimp only [frozen, d, R, S]
    rw [← mul_sub, abs_mul, abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left hcost hscale).trans_eq (by ring)
  · intro j k
    have hk := hEdge (cs j) (ct k) (zs j) (hzs j).1 (zt k) (hzt k).1
    calc |frozen j k + tilt * probe j k| ≤ |frozen j k| + |tilt * probe j k| := abs_add_le _ _
      _ ≤ scale * edgeBound + |tilt| * ‖f‖ := by
        apply add_le_add
        · simpa only [frozen, abs_mul, abs_of_nonneg hscale] using
            mul_le_mul_of_nonneg_left hk hscale
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (C.clockClassProbe_abs_le (Q ref) ref.val ref.property f (cs j) (ct k)) (abs_nonneg _)

end OTSelector.Reconstruction.PopulationLocalPressureCore
