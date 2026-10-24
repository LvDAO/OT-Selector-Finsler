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

/-- A dependent finite family of original coefficient cells supplies endpoint
properties and class legality on ONE original retained physical population.
No residual, original atlas or compact approximation is allocated per coefficient. -/
theorem PopulationLocalPressureCore.original_dependent_clockClass_endpoint_properties
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
    {C T : Type*} [Fintype C] [Fintype T]
    (hI : MeasurableSet I) {globalGap : ℝ}
    (coreIndex : C → Fin D.haar.continuous.count)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (Q : C → FiniteScalarBins I globalGap) (U : C → Set (ℚ → M))
    {A B : Set M} (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (houter : ∀ c j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1)
    (hregion : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      s < t → D.corePoint (coreIndex c) (z, s) ∈ A → D.corePoint (coreIndex c) (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient (coreIndex c)).window.region)
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν) {q : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    {forwardGap : ℝ} (hgap : 0 < forwardGap)
    (hforward : ∀ t x y, Cst.sourceGood t x → Cst.targetGood t y →
      forwardGap ≤ u y - u x)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c)
    (classify : ∀ c, ℝ → Fin (Q c).count)
    (hmclass : ∀ c, Measurable (classify c))
    (hclass : ∀ c j s, s ∈ (Q c).cell j → classify c s = j)
    (Kcell : C → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (Kcell c)]
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell Kcell z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z))
    (hχ : χ = (((lambda ⊗ₘ finiteCellPairKernel cell hcell Kcell).map
      sameLabelPopulationPair).map (Prod.map b b)))
    (fallbackS fallbackT : ∀ c, Fin (Q c).count → ℝ)
    (P₀ : ∀ c, Fin (Q c).count → Fin (Q c).count → ℝ)
    (hP₀ : ∀ c j k, 0 ≤ P₀ c j k)
    (density : C → (ℚ → M) → ℝ)
    (residual Pf : ∀ c, (ℚ → M) → Fin (Q c).count → Fin (Q c).count → ℝ)
    (hmPf : ∀ c j k, Measurable (fun z ↦ Pf c z j k))
    (hPf : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, Pf c z j k = P₀ c j k / density c z)
    (hdensity : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), 0 < density c z)
    (hresidual : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, 0 ≤ residual c z j k)
    (hrow : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j,
      ∑ k, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a μ z).real ((Q c).cell j))
    (hcol : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ k,
      ∑ j, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a ν z).real ((Q c).cell k))
    (hKcell : ∀ c, Kcell c = finiteClassPopulationKernel (Pf c)
      (fun j ↦ normalizedActualBinKernel (condDistrib u a μ) ((Q c).cell j)
        ((Q c).measurable_cell j) (fallbackS c j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a ν) ((Q c).cell k)
        ((Q c).measurable_cell k) (fallbackT c k)))
    (hzero : ∀ c j k, ¬(D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed
      (Q c) j k → P₀ c j k = 0) :
    let Ps := fun x ↦ x ∈ A ∧ ∀ c, a x ∈ cell c →
      D.corePoint (coreIndex c) (a x, u x) = x ∧ u x ∈ (Q c).cell (classify c (u x)) ∧
        ∃ k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) (classify c (u x)) k
    let Pt := fun y ↦ y ∈ B ∧ ∀ c, a y ∈ cell c →
      D.corePoint (coreIndex c) (a y, u y) = y ∧ u y ∈ (Q c).cell (classify c (u y)) ∧
        ∃ j, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j (classify c (u y))
    (∀ᵐ x ∂χ.map Prod.fst, Ps x) ∧ (∀ᵐ y ∂χ.map Prod.snd, Pt y) ∧
    ∀ c t x y, Cst.sourceGood t x → Cst.targetGood t y → Ps x → Pt y →
      a x ∈ cell c → a y ∈ cell c →
        (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) (classify c (u x)) (classify c (u y)) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  have hum : Measurable u := hu.continuous.measurable
  have hrestore c := D.original_cell_corePoint_ae hF hcomplete hu ha hinj horder hb hμreg hνreg
    hμinv hνinv hlabel0 hlabel1 (coreIndex c) (hcell c) (fun _ hz ↦ (hsub c hz).1)
  have hrange c := D.original_clock_range_on_core_ae γ originalGap I hI hcomplete ha hum
    hlabel0 hlabel1 (coreIndex c)
  have hrestoreS : ∀ᵐ x ∂μ, ∀ c, a x ∈ cell c → D.corePoint (coreIndex c) (a x,u x) = x :=
    ae_all_iff.mpr fun c ↦ (hrestore c).1
  have hrestoreT : ∀ᵐ y ∂ν, ∀ c, a y ∈ cell c → D.corePoint (coreIndex c) (a y,u y) = y :=
    ae_all_iff.mpr fun c ↦ (hrestore c).2
  have hrangeS : ∀ᵐ x ∂μ, ∀ c, a x ∈ cell c → u x ∈ I :=
    ae_all_iff.mpr fun c ↦ ((hrange c).1.mono fun x hx hc ↦ hx (hsub c hc).1)
  have hrangeT : ∀ᵐ y ∂ν, ∀ c, a y ∈ cell c → u y ∈ I :=
    ae_all_iff.mpr fun c ↦ ((hrange c).2.mono fun y hy hc ↦ hy (hsub c hc).1)
  have hactive :
      (∀ᵐ x ∂χ.map Prod.fst, ∀ c, a x ∈ cell c → ∃ k,
        (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) (classify c (u x)) k) ∧
      (∀ᵐ y ∂χ.map Prod.snd, ∀ c, a y ∈ cell c → ∃ j,
        (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j (classify c (u y))) := by
    rw [hχ]
    exact original_physical_retained_class_activity μ ν lambda a u ha hum b hb
      hμinv hνinv hlabel0 hlabel1 cell hcell hdisj Kcell Qglobal hwhole
      (fun c ↦ (Q c).cell) (fun c ↦ (Q c).cell)
      (fun c ↦ (Q c).measurable_cell) (fun c ↦ (Q c).measurable_cell)
      fallbackS fallbackT classify classify hmclass hmclass hclass hclass
      P₀ hP₀ density residual Pf hmPf hPf hdensity hresidual hrow hcol hKcell
      (fun c ↦ (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c)) hzero
  have hsle : χ.map Prod.fst ≤ μ :=
    (Measure.map_mono (Measure.le_add_right le_rfl) measurable_fst).trans_eq hπ.1
  have htle : χ.map Prod.snd ≤ ν :=
    (Measure.map_mono (Measure.le_add_right le_rfl) measurable_snd).trans_eq hπ.2
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ae_mono hsle hμA, ae_mono hsle hrestoreS,
      ae_mono hsle hrangeS, hactive.1] with x hx hrest hrange hact
    refine ⟨hx, ?_⟩
    intro c hc
    exact ⟨hrest c hc, (Q c).mem_classified_cell (classify c) (hclass c) (hrange c hc), hact c hc⟩
  · filter_upwards [ae_mono htle hνB, ae_mono htle hrestoreT,
      ae_mono htle hrangeT, hactive.2] with y hy hrest hrange hact
    refine ⟨hy, ?_⟩
    intro c hc
    exact ⟨hrest c hc, (Q c).mem_classified_cell (classify c) (hclass c) (hrange c hc), hact c hc⟩
  · intro c t x y hx hy hPs hPt hxc hyc
    obtain ⟨hxs, hxb, hxa⟩ := hPs.2 c hxc
    obtain ⟨hys, hyb, hya⟩ := hPt.2 c hyc
    apply D.original_endpoint_clockClass_allowed_of_geometry (coreIndex c)
      (fun _ ↦ Q c) (fun _ ↦ U c) (fun _ ↦ houter c) (fun _ ↦ hregion c)
      (reference c) x y (classify c (u x)) (classify c (u y))
      (hsub c hxc) (hsub c hyc) hxb hyb hxa hya hxs hys hPs.1 hPt.1
    linarith [hforward t x y hx hy]

end OTSelector.Reconstruction
