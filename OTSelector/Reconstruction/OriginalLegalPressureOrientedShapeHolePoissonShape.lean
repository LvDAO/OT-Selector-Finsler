import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonSpatial
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonSigned
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape

/-! Actual original spatial holes have a sublinear kinetic pressure cost. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- A real spatial hole of mass h has original Poisson count mean r*h, while
its physical kinetic scale stays r^(2/q). The actual shape optimum is integrable
and obeys the explicit sublinear-hole estimate, with no Poisson-cost callback.
Closed-cube arbitrary-space costs use the true unclamped displacement; equality
with the literal original block cost is proved only on the actual uniform
shape's full-measure open-cube carrier. -/
theorem originalShapeHolePoisson_shape_mean_le
    {q : ℕ} (hq : 4 < q) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (π : Measure (ℝ × ℝ)) (hπ : Vlasov.IsCoupling π α β)
    {I : Set ℝ} {gap diameter : ℝ} (bins : FiniteScalarBins I gap) (hIm : MeasurableSet I) (hgap : 0 < gap)
    (hsep : ConditionalClockSupportBounds α β gap diameter)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v) {C : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C*∑ i, v i^2)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) {G : ℝ} (hG : 0 ≤ G)
    (hgb : ∀ a b, |g a b| ≤ G) (r : ℝ≥0) (H : Set (Fin q → ℝ)) (hH : MeasurableSet H) (t : ℝ) :
    let h := (cubeMeasure (Fin q) 1).real H
    let K := ((bins.count+1 : ℕ) : ℝ)
    let A := C*(q : ℝ)*dyadicMatchingConstant q*K^(2/(q : ℝ))
    let B := C*(q : ℝ)*((1+2*K)*Real.sqrt K+2*K)
    Integrable (shapeLegalMarkedTilted q id id H r kin g t) (twoMarkedCloudLaw q ℝ ℝ α β r) ∧
      (∫ ω, shapeLegalMarkedTilted q id id H r kin g t ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) ≤
        A*(r : ℝ)^(2/(q : ℝ))*((r : ℝ)*h)^(1-2/(q : ℝ))+
        B*(r : ℝ)^(2/(q : ℝ))*Real.sqrt (2*(r : ℝ)*h)+|t| * G*((r : ℝ)*h) := by
  have : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  let h := (cubeMeasure (Fin q) 1).real H
  let K := ((bins.count+1 : ℕ) : ℝ)
  let space := originalShapeHolePoissonSpatialLaw q H
  let a := r*restrictionWeight (cubeMeasure (Fin q) 1) H
  let scaledC := (r : ℝ)^(2/(q : ℝ))*(C*(q : ℝ))
  let cost := fun x y : DyadicUnitCube q × ℝ ↦
    (r : ℝ)^(2/(q : ℝ))*kin x.2 y.2 (dyadicCubePoint y.1-dyadicCubePoint x.1)
  let probe := fun x y : DyadicUnitCube q × ℝ ↦ g x.2 y.2
  have hp : Measurable (dyadicCubePoint (q := q)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  have hc : Measurable (uncurry cost) := by
    apply Measurable.const_mul
    exact hk.comp (show Measurable (fun xy : (DyadicUnitCube q × ℝ) × (DyadicUnitCube q × ℝ) ↦
      ((xy.1.2,xy.2.2),dyadicCubePoint xy.2.1-dyadicCubePoint xy.1.1)) by fun_prop)
  have hprobe : Measurable (uncurry probe) := hg.comp
    (show Measurable (fun xy : (DyadicUnitCube q × ℝ) × (DyadicUnitCube q × ℝ) ↦ (xy.1.2,xy.2.2)) by fun_prop)
  have hscaledC : 0 ≤ scaledC := by dsimp [scaledC]; positivity
  have hcostn (x y) : 0 ≤ cost x y := mul_nonneg (Real.rpow_nonneg r.coe_nonneg _) (hkn _ _ _)
  have hquad (x y : DyadicUnitCube q × ℝ) : cost x y ≤ scaledC*‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2 := by
    have hsum : (∑ i, (dyadicCubePoint y.1-dyadicCubePoint x.1) i^2) ≤
        (q : ℝ)*‖dyadicCubePoint y.1-dyadicCubePoint x.1‖^2 := by
      calc
        _ ≤ ∑ _i : Fin q, ‖dyadicCubePoint y.1-dyadicCubePoint x.1‖^2 := by
          apply Finset.sum_le_sum
          intro i _
          have hb := pow_le_pow_left₀ (norm_nonneg ((dyadicCubePoint y.1-dyadicCubePoint x.1) i))
            (norm_le_pi_norm (dyadicCubePoint y.1-dyadicCubePoint x.1) i) 2
          simpa only [Real.norm_eq_abs,sq_abs] using hb
        _ = _ := by simp
    have hb := (le_abs_self (kin x.2 y.2 (dyadicCubePoint y.1-dyadicCubePoint x.1))).trans (hkb _ _ _)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hsum hC)
    rw [norm_sub_rev] at hb'
    exact (mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg r.coe_nonneg _)).trans_eq (by dsimp [cost,scaledC]; ring)
  have hsign := originalShapeHolePoisson_signed_integral_le hq space α β π hπ bins hIm hgap hsep hI horder
    cost probe hc hprobe hscaledC hG t hcostn hquad (fun _ _ ↦ hgb _ _) a
  let P := originalShapeHolePoissonLaw space α β a
  let Fval := fun d : BlockData ((Fin q → ℝ) × ℝ) × BlockData ((Fin q → ℝ) × ℝ) ↦
    blockLegalTilted q id id (r : ℝ) kin g t d.1 d.2
  have hF : Measurable Fval := measurable_blockLegalTilted q measurable_id measurable_id (r : ℝ) hk hg t
  have hraw := originalShapeHolePoisson_raw_blocks_law q α β r H
  have heq : (fun z ↦ Fval (originalShapeHolePoissonRawBlocks z)) =ᵐ[P]
      originalShapeHolePoissonValue (fun x y ↦ cost x y+t*probe x y) := by
    filter_upwards [hraw.quasiMeasurePreserving.ae (ae_shapeBlockLaw_unitCube_two q α β r hH)] with z hz
    rw [show Fval (originalShapeHolePoissonRawBlocks z) = unclampedBlockLegalTilted q id id (r : ℝ) kin g t
      (originalShapeHolePoissonRawBlocks z).1 (originalShapeHolePoissonRawBlocks z).2 from
      (unclampedBlockLegalTilted_eq_block q id id (r : ℝ) kin g t _ _ hz.1 hz.2).symm]
    rfl
  have hcompI := hsign.1.congr heq.symm
  have hFI : Integrable Fval ((shapeBlockLaw q α r H).prod (shapeBlockLaw q β r H)) := by
    rw [← hraw.map_eq]
    exact (integrable_map_measure hF.aestronglyMeasurable hraw.measurable.aemeasurable).mpr hcompI
  have hshape : MeasurePreserving (Prod.map (shapeCloud H) (shapeCloud H))
      (twoMarkedCloudLaw q ℝ ℝ α β r) ((shapeBlockLaw q α r H).prod (shapeBlockLaw q β r H)) :=
    ⟨(measurable_shapeCloud hH).prodMap (measurable_shapeCloud hH),map_shapeCloud_twoMarkedCloudLaw q α β r hH⟩
  have hactual : (∫ ω, shapeLegalMarkedTilted q id id H r kin g t ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) =
      ∫ z, originalShapeHolePoissonValue (fun x y ↦ cost x y+t*probe x y) z ∂P := by
    calc
      _ = ∫ d, Fval d ∂(shapeBlockLaw q α r H).prod (shapeBlockLaw q β r H) :=
        hshape.hasLaw.integral_comp hFI.aestronglyMeasurable
      _ = ∫ z, Fval (originalShapeHolePoissonRawBlocks z) ∂P :=
        (hraw.hasLaw.integral_comp hFI.aestronglyMeasurable).symm
      _ = _ := integral_congr_ae heq
  refine ⟨hshape.integrable_comp_of_integrable hFI,?_⟩
  rw [hactual]
  have ha : (a : ℝ) = (r : ℝ)*h := by
    simp only [a,NNReal.coe_mul,restrictionWeight,ENNReal.coe_toNNReal_eq_toReal,h,measureReal_def]
  have he : scaledC*dyadicMatchingConstant q*K^(2/(q : ℝ))*(a : ℝ)^(1-2/(q : ℝ))+
      (scaledC+2*((bins.count : ℝ)+1)*scaledC)*Real.sqrt (2*(a : ℝ)*(bins.count+1))+
      Real.sqrt (2*(a : ℝ))*(2*((bins.count : ℝ)+1)*scaledC)+(a : ℝ)*(|t| * G) =
      (C*(q : ℝ)*dyadicMatchingConstant q*K^(2/(q : ℝ)))*(r : ℝ)^(2/(q : ℝ))*((r : ℝ)*h)^(1-2/(q : ℝ))+
      (C*(q : ℝ)*((1+2*K)*Real.sqrt K+2*K))*(r : ℝ)^(2/(q : ℝ))*Real.sqrt (2*(r : ℝ)*h)+|t| * G*((r : ℝ)*h) := by
    have hsqrt : Real.sqrt (2*(a : ℝ)*(bins.count+1)) = Real.sqrt (2*(a : ℝ))*Real.sqrt K := by
      simpa only [K,Nat.cast_add,Nat.cast_one] using
        Real.sqrt_mul (show (0 : ℝ) ≤ 2*(a : ℝ) by positivity) ((bins.count : ℝ)+1)
    rw [hsqrt,ha]
    dsimp only [scaledC,K]
    push_cast
    ring
  exact hsign.2.trans_eq he

end OTSelector.Reconstruction
