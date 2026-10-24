import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalClassActivity
import OTSelector.Reconstruction.FinslerRelativeLawOriginalClockClassMembership
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalEndpointAllowed

/-! Literal original conditional class splits discharge all retained endpoint
properties and compatibility needed by the canonical expected upper bound. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Original physical recovery, full original clock support, and the exact
within-bin retained kernel imply all endpoint conditions and same-old-type
class legality. No active-class, selected-edge or residual-iid premise is used. -/
theorem PopulationLocalPressureCore.original_retained_clockClass_endpoint_properties
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (i : Fin D.haar.continuous.count) (hI : MeasurableSet I) {globalGap : ℝ}
    (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I globalGap)
    (U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    {A B : Set M} (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (houter : ∀ ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k →
      ∀ s ∈ (Q ref).cell j, ∀ t ∈ (Q ref).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1)
    (hregion : ∀ ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient i).window.region)
    {C T : Type*} [Fintype C] [Fintype T]
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν) {q : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    {forwardGap : ℝ} (hgap : 0 < forwardGap)
    (hforward : ∀ t x y, Cst.sourceGood t x → Cst.targetGood t y →
      forwardGap ≤ u y - u x)
    (reference : C → (D.haar.continuous.coefficient i).roots)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient i).roots ∩ U (reference c))
    (classify : ∀ c, ℝ → Fin (Q (reference c)).count)
    (hmclass : ∀ c, Measurable (classify c))
    (hclass : ∀ c j s, s ∈ (Q (reference c)).cell j → classify c s = j)
    (Kcell : C → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (Kcell c)]
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell Kcell z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z))
    (hχ : χ = (((lambda ⊗ₘ finiteCellPairKernel cell hcell Kcell).map
      sameLabelPopulationPair).map (Prod.map b b)))
    (fallbackS fallbackT : ∀ c, Fin (Q (reference c)).count → ℝ)
    (P₀ : ∀ c, Fin (Q (reference c)).count → Fin (Q (reference c)).count → ℝ)
    (hP₀ : ∀ c j k, 0 ≤ P₀ c j k)
    (density : C → (ℚ → M) → ℝ)
    (residual Pf : ∀ c, (ℚ → M) → Fin (Q (reference c)).count → Fin (Q (reference c)).count → ℝ)
    (hmPf : ∀ c j k, Measurable (fun z ↦ Pf c z j k))
    (hPf : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, Pf c z j k = P₀ c j k / density c z)
    (hdensity : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), 0 < density c z)
    (hresidual : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, 0 ≤ residual c z j k)
    (hrow : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j,
      ∑ k, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a μ z).real ((Q (reference c)).cell j))
    (hcol : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ k,
      ∑ j, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a ν z).real ((Q (reference c)).cell k))
    (hKcell : ∀ c, Kcell c = finiteClassPopulationKernel (Pf c)
      (fun j ↦ normalizedActualBinKernel (condDistrib u a μ) ((Q (reference c)).cell j)
        ((Q (reference c)).measurable_cell j) (fallbackS c j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a ν) ((Q (reference c)).cell k)
        ((Q (reference c)).measurable_cell k) (fallbackT c k)))
    (hzero : ∀ c j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed
      (Q (reference c)) j k → P₀ c j k = 0) :
    let C₀ := D.haar.continuous.coefficient i
    let Ps := fun x ↦ x ∈ A ∧ ∀ c, a x ∈ cell c →
      D.corePoint i (a x, u x) = x ∧ u x ∈ (Q (reference c)).cell (classify c (u x)) ∧
        ∃ k, C₀.clockClassAllowed (Q (reference c)) (classify c (u x)) k
    let Pt := fun y ↦ y ∈ B ∧ ∀ c, a y ∈ cell c →
      D.corePoint i (a y, u y) = y ∧ u y ∈ (Q (reference c)).cell (classify c (u y)) ∧
        ∃ j, C₀.clockClassAllowed (Q (reference c)) j (classify c (u y))
    (∀ᵐ x ∂χ.map Prod.fst, Ps x) ∧ (∀ᵐ y ∂χ.map Prod.snd, Pt y) ∧
    ∀ c t x y, Cst.sourceGood t x → Cst.targetGood t y → Ps x → Pt y →
      a x ∈ cell c → a y ∈ cell c →
        C₀.clockClassAllowed (Q (reference c)) (classify c (u x)) (classify c (u y)) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  have humeas : Measurable u := hu.continuous.measurable
  have hroot : (⋃ c, cell c) ⊆ (D.haar.continuous.coefficient i).roots := by
    intro z hz
    obtain ⟨c, hc⟩ := mem_iUnion.mp hz
    exact (hsub c hc).1
  have hrestore := D.original_cell_corePoint_ae hF hcomplete hu ha hinj horder hb hμreg hνreg
    hμinv hνinv hlabel0 hlabel1 i (MeasurableSet.iUnion hcell) hroot
  have hrange := D.original_clock_range_on_core_ae γ originalGap I hI hcomplete ha humeas
    hlabel0 hlabel1 i
  have hactive :
      (∀ᵐ x ∂χ.map Prod.fst, ∀ c, a x ∈ cell c → ∃ k,
        (D.haar.continuous.coefficient i).clockClassAllowed (Q (reference c)) (classify c (u x)) k) ∧
      (∀ᵐ y ∂χ.map Prod.snd, ∀ c, a y ∈ cell c → ∃ j,
        (D.haar.continuous.coefficient i).clockClassAllowed (Q (reference c)) j (classify c (u y))) := by
    rw [hχ]
    exact original_physical_retained_class_activity μ ν lambda a u ha humeas b hb
      hμinv hνinv hlabel0 hlabel1 cell hcell hdisj Kcell Qglobal hwhole
      (fun c ↦ (Q (reference c)).cell) (fun c ↦ (Q (reference c)).cell)
      (fun c ↦ (Q (reference c)).measurable_cell) (fun c ↦ (Q (reference c)).measurable_cell)
      fallbackS fallbackT classify classify hmclass hmclass hclass hclass
      P₀ hP₀ density residual Pf hmPf hPf hdensity hresidual hrow hcol hKcell
      (fun c ↦ (D.haar.continuous.coefficient i).clockClassAllowed (Q (reference c))) hzero
  have hsle : χ.map Prod.fst ≤ μ :=
    (Measure.map_mono (Measure.le_add_right le_rfl) measurable_fst).trans_eq hπ.1
  have htle : χ.map Prod.snd ≤ ν :=
    (Measure.map_mono (Measure.le_add_right le_rfl) measurable_snd).trans_eq hπ.2
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ae_mono hsle hμA, ae_mono hsle hrestore.1,
      ae_mono hsle hrange.1, hactive.1] with x hx hrest hrange hact
    refine ⟨hx, ?_⟩
    intro c hc
    exact ⟨hrest (mem_iUnion_of_mem c hc),
      (Q (reference c)).mem_classified_cell (classify c) (hclass c) (hrange (hsub c hc).1), hact c hc⟩
  · filter_upwards [ae_mono htle hνB, ae_mono htle hrestore.2,
      ae_mono htle hrange.2, hactive.2] with y hy hrest hrange hact
    refine ⟨hy, ?_⟩
    intro c hc
    exact ⟨hrest (mem_iUnion_of_mem c hc),
      (Q (reference c)).mem_classified_cell (classify c) (hclass c) (hrange (hsub c hc).1), hact c hc⟩
  · intro c t x y hx hy hPs hPt hxc hyc
    obtain ⟨hxs, hxb, hxa⟩ := hPs.2 c hxc
    obtain ⟨hys, hyb, hya⟩ := hPt.2 c hyc
    apply D.original_endpoint_clockClass_allowed_of_geometry i Q U houter hregion
      (reference c) x y (classify c (u x)) (classify c (u y))
      (hsub c hxc) (hsub c hyc) hxb hyb hxa hya hxs hys hPs.1 hPt.1
    linarith [hforward t x y hx hy]

end OTSelector.Reconstruction
