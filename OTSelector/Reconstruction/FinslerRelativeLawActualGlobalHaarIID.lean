import OTSelector.Reconstruction.FinslerRelativeLawActualGlobalHaarCell

/-!
The retained original physical pair population equals its literal fixed
pair-class population on the original Haar cell under the actual seed physical
map. Both original endpoint recovery and original density normalization are
discharged from the unchanged original population and pressure-core data.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- One actual Haar cell is selected INSIDE the same original global
retained/residual marked experiment. Other retained cells remain retained;
the global residual ξ and its uniform repair estimate are unchanged. -/
theorem PopulationLocalPressureCore.actual_global_retained_cell_iid_coordinates_eq_haar
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hb : Measurable b)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x)
    (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {I J : Type*} [Fintype I] [Fintype J]
    (Sbin : I → Set ℝ) (Tbin : J → Set ℝ)
    (hSbin : ∀ j, MeasurableSet (Sbin j)) (hTbin : ∀ k, MeasurableSet (Tbin k))
    (fallbackS : I → ℝ) (fallbackT : J → ℝ)
    (P₀ : I → J → ℝ) (Pf : (ℚ → M) → I → J → ℝ)
    (hmPf : ∀ j k, Measurable (fun z ↦ Pf z j k))
    (hPf : ∀ z ∈ L, ∀ j k, Pf z j k = P₀ j k / D.rootIntensity i z)
    {Cells : Type*} [Fintype Cells]
    (cell : Cells → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (c : Cells) (hc : cell c = L)
    (hKc : K c = finiteClassPopulationKernel Pf
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Sbin j) (hSbin j) (fallbackS j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Tbin k) (hTbin k) (fallbackT k)))
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (πWhole ξ : Measure (M × M)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {T : Type*} [Fintype T] {q : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T q cost)
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {NS NT : Type*} [Fintype NS] [Fintype NT] :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue Seed a
    let read := fun x ↦ (R (a x), u x)
    let αc := fun j ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₀)) (Sbin j) (hSbin j) (fallbackS j)
    let βc := fun k ↦ normalizedActualBinKernel
      (populationSeedCoordinateClockKernel Seed a ha (condDistrib u a η₁)) (Tbin k) (hTbin k) (fallbackT k)
    let H := ((κ C.seedIndex).restrict (R '' L) ⊗ₘ
      finiteClassPopulationKernel (fun _ j k ↦ P₀ j k) αc βc).map sameLabelPopulationPair
    let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
    let Refined := Cst.refineSubplan ξ hξ
    let Law := (Measure.pi (fun _ : NS ↦ Refined.types.sourceMarkedLaw η₀)).prod
      (Measure.pi (fun _ : NT ↦ Refined.types.targetMarkedLaw η₁))
    Law.map (Prod.map (fun x i ↦ (x i).1) (fun y j ↦ (y j).1)) =
      (Measure.pi (fun _ : NS ↦ η₀)).prod (Measure.pi (fun _ : NT ↦ η₁)) ∧
    (Law.restrict
      ((univ.pi (fun _ ↦ {p | subplanRetentionFlag p.2 = false ∧ a p.1 ∈ L})) ×ˢ
        (univ.pi (fun _ ↦ {p | subplanRetentionFlag p.2 = false ∧ a p.1 ∈ L})))).map
          (Prod.map (fun x i ↦ read (x i).1) (fun y j ↦ read (y j).1)) =
      (Measure.pi (fun _ : NS ↦ H.map Prod.fst)).prod (Measure.pi (fun _ : NT ↦ H.map Prod.snd)) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let read := fun x ↦ (R (a x), u x)
  have hR : Measurable R := measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj
  have hread : Measurable read := (hR.comp ha).prodMk hu.continuous.measurable
  have hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
  let _instξ : IsFiniteMeasure ξ := isFiniteMeasure_of_le πWhole hξ
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
    sameLabelPopulationPair).map (Prod.map b b))
  have hcancel : πWhole - ξ = χ := by rw [hsplit, Measure.add_sub_cancel]
  have hsPair := D.actual_global_retained_cell_pair_coordinates_eq_haar hF hcomplete hu ha hinj
    hb hη₀inv hη₁inv hlabel0 hlabel1 i hL hsub Sbin Tbin hSbin hTbin fallbackS fallbackT
    P₀ Pf hmPf hPf cell hcell hdisj K c hc hKc Qglobal hwhole false
  have htPair := D.actual_global_retained_cell_pair_coordinates_eq_haar hF hcomplete hu ha hinj
    hb hη₀inv hη₁inv hlabel0 hlabel1 i hL hsub Sbin Tbin hSbin hTbin fallbackS fallbackT
    P₀ Pf hmPf hPf cell hcell hdisj K c hc hKc Qglobal hwhole true
  dsimp only at hsPair htPair ⊢
  constructor
  · exact (Cst.refineSubplan ξ hξ).types.iid_physical_law hπWhole
  · have hsample := Cst.refineSubplan_retained_cell_iid_observation_laws (I := NS) (J := NT)
      ξ hξ (ha hL) (ha hL) read read hread hread
    have hs : (((χ.map Prod.fst).restrict (a ⁻¹' L)).map read) =
        ((χ.restrict {p | a p.1 ∈ L}).map (Prod.map read read)).map Prod.fst := by
      rw [Measure.restrict_map measurable_fst (ha hL), Measure.map_map hread measurable_fst,
        Measure.map_map measurable_fst (hread.prodMap hread)]
      rfl
    have ht : (((χ.map Prod.snd).restrict (a ⁻¹' L)).map read) =
        ((χ.restrict {p | a p.2 ∈ L}).map (Prod.map read read)).map Prod.snd := by
      rw [Measure.restrict_map measurable_snd (ha hL), Measure.map_map hread measurable_snd,
        Measure.map_map measurable_snd (hread.prodMap hread)]
      rfl
    have hsHaar := hs.trans (congrArg (Measure.map Prod.fst) hsPair)
    have htHaar := ht.trans (congrArg (Measure.map Prod.snd) htPair)
    rw [← hcancel] at hsHaar htHaar
    dsimp only at hsample
    simp_rw [hsHaar, htHaar] at hsample
    exact hsample

end OTSelector.Reconstruction
