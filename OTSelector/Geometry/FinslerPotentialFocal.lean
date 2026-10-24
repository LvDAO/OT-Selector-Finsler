import OTSelector.Geometry.Finsler.PotentialLevelGraph
import OTSelector.Geometry.FinslerGraphFocal
import OTSelector.Geometry.GraphVariationPole

/-!
# Focal expansions of the constructed potential-level Finsler family

The same normalized conormal flow, genuine level chart and graph inverse now yield
regular crossings, sharp determinant/inverse rates and an exact inverse simple pole.
Time smoothness is derived from the original field. No crossing, position inverse,
parameter dimension or extra smoothness of the graph family is assumed.
The auxiliary smooth potential and its actual initial momentum match remain inputs.
-/

open Set Filter Metric Manifold Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- The actual level construction retains its original normalized flow and supplies
focal expansions for its true square graph variation at every central point in Q. -/
theorem exists_potentialLevel_focalFamily (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {f : (ℝ × V) → ℝ} {Ω : Set (ℝ × V)} {y₀ v₀ : ℝ × V}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hy₀ : y₀ ∈ Ω)
    (hz : (y₀, v₀) ∈ chartEnergyDomain x₀)
    (hmatch : fderiv ℝ f y₀ = fiberLegendre (F.chartEnergy x₀) (y₀, v₀))
    (hpositive : 0 < v₀.1) (t₀ : ℝ) :
    ∃ (σ : V → ℝ × V) (B₀ : Set V) (U : Set (ℝ × V)),
      IsOpen B₀ ∧ (0 : V) ∈ B₀ ∧ IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ σ B₀ ∧ σ 0 = y₀ ∧ MapsTo σ B₀ Ω ∧
      (∀ w ∈ B₀, f (σ w) = f y₀) ∧ Function.Injective (fderiv ℝ σ 0) ∧
      InjOn σ B₀ ∧ σ '' B₀ = U ∩ {x | f x = f y₀} ∧
      let L₀ := F.chartEnergy x₀
      let z₀ := (σ (0 : V), v₀)
      let p₀ := parametricLegendre L₀ z₀
      ∃ (ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
          ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)))
        (B : Set V) (v : V → ℝ × V) (a : V → ℝ) (r : ℝ≥0) (T : ℝ)
        (Φ : ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) × ℝ →
          (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)),
        let seed := potentialConormalState f σ a
        let Ψ := fun q : V × ℝ ↦ Φ (seed q.1, q.2)
        let γ := fun q ↦ (Ψ q).1
        let Z₀ := fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) (0 : V)
        let q₀ := curveGraphCoordinateMap γ ((0 : V), t₀)
        let L := F.chartGraphLagrangian x₀
        (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
          parametricLegendre L₀ ∧
        z₀ ∈ ℓ.source ∧ ℓ.source ⊆ chartEnergyDomain x₀ ∧
        ContDiffOn ℝ ∞ ℓ.symm ℓ.target ∧ IsOpen B ∧ (0 : V) ∈ B ∧ B ⊆ B₀ ∧
        ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧ v (0 : V) = v₀ ∧ a (0 : V) = 1 ∧
        ContDiffOn ℝ ∞ seed B ∧ seed (0 : V) = p₀ ∧
        (∀ w ∈ B, (σ w, v w) ∈ ℓ.source ∧ 0 < a w ∧
          L₀ (σ w, v w) = L₀ z₀ ∧
          fiberLegendre L₀ (σ w, v w) = a w • fderiv ℝ f (σ w) ∧
          ℓ.symm (seed w) = (σ w, v w) ∧ seed w ∈ closedBall p₀ r) ∧
        0 < r ∧ 0 < T ∧
        LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L₀ ℓ)
          t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
        MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) ℓ.target ∧
        ContDiffOn ℝ 2 Ψ (B ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
        Z₀ t₀ = fderiv ℝ seed (0 : V) ∧
        (∀ t ∈ Icc (t₀ - T) (t₀ + T),
          DifferentiableAt ℝ (fun w ↦ Ψ (w, t)) (0 : V) ∧ Function.Injective (Z₀ t) ∧
          (∀ u w : V, canonicalPhasePairing (Z₀ t u) (Z₀ t w) = 0) ∧
          (∀ u : V, HasDerivWithinAt (fun s ↦ Z₀ s u)
            (fderiv ℝ (localHamiltonianVectorField L₀ ℓ) (Φ (p₀, t)) (Z₀ t u))
            (Icc (t₀ - T) (t₀ + T)) t) ∧
          ∀ u : V, (Z₀ t u).1 ∈ (fiberLegendre L₀ (ℓ.symm (Φ (p₀, t)))).ker) ∧
        ∃ (e : OpenPartialHomeomorph (V × ℝ) (V × ℝ))
          (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
          (D : Set (V × ℝ)),
          (e : V × ℝ → V × ℝ) = curveGraphCoordinateMap γ ∧
          ((0 : V), t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ Ioo (t₀ - T) (t₀ + T) ∧
          (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
          g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ ∧
          ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
          ContDiffOn ℝ 2 (F.chartGraphPhase x₀ γ e) D ∧
          (∀ q ∈ D,
            let P := F.chartGraphPhase x₀ γ e
            let A := GraphHamiltonian.blockA L g q.2 (P q)
            let B' := GraphHamiltonian.blockB L g q.2 (P q)
            let C := GraphHamiltonian.blockC L g q.2 (P q)
            graphVelocityPhase (fun p ↦ (curveGraphPosition γ e p).2) q ∈ g.source ∧
            HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2 ∧
            (∀ ξ : V,
              let Z := fun s ↦ fderiv ℝ (fun w ↦ P (w, s)) q.1 ξ
              HasDerivAt (fun s ↦ (Z s).1) (B' (Z q.2).1 + C (Z q.2).2) q.2 ∧
              HasDerivAt (fun s ↦ (Z s).2) (-A (Z q.2).1 - (Z q.2).2.comp B') q.2) ∧
            (∀ u v, A u v = A v u) ∧
            (∀ p r : V →L[ℝ] ℝ, r (C p) = p (C r)) ∧
            C = ContinuousLinearMap.inverse
              (GraphLegendre.verticalHessian L (g.symm ((q.2, (P q).1), (P q).2))) ∧
            ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (C p) ) ∧
          ∃ Q : Set (V × ℝ), IsOpen Q ∧ q₀ ∈ Q ∧ Q ⊆ D ∧
            ∀ q ∈ Q, q.1 = (0 : V) →
              let P := F.chartGraphPhase x₀ γ e
              let Z := fun s ↦ fderiv ℝ (fun w ↦ P (w, s)) q.1
              let b := Module.finBasis ℝ V
              let J := fun s ↦ vectorFamilyMatrix b (fun j ↦ (Z s (b j)).1)
              ContDiffOn ℝ ∞ Z {s | (q.1, s) ∈ D} ∧
              Function.Bijective (focalCrossingMap (J q.2) (deriv J q.2)) ∧
              (0 < Module.finrank ℝ (LinearMap.ker (J q.2).mulVecLin) →
                ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ∃ cdet Cdet cinv Cinv : ℝ,
                  0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
                  ∀ᶠ s in 𝓝[>] (0 : ℝ),
                    cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J q.2).mulVecLin) ≤
                        |(J (q.2 + ε * s)).det| ∧
                      |(J (q.2 + ε * s)).det| ≤
                        Cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J q.2).mulVecLin) ∧
                      cinv / |s| ≤ ‖(J (q.2 + ε * s))⁻¹‖ ∧
                      ‖(J (q.2 + ε * s))⁻¹‖ ≤ Cinv / |s|) ∧
              ∃ (U : Set ℝ) (R : Matrix (Fin (Module.finrank ℝ V))
                  (Fin (Module.finrank ℝ V)) ℝ)
                (H : ℝ → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ),
                IsOpen U ∧ 0 ∈ U ∧ U ⊆ {s | (q.1, q.2 + s) ∈ D} ∧
                ContDiffOn ℝ ∞ H U ∧
                (∀ s ∈ U, s ≠ 0 → (J (q.2 + s)).det ≠ 0 ∧
                  (J (q.2 + s))⁻¹ = s⁻¹ • R + H s) ∧
                R.rank = Module.finrank ℝ (LinearMap.ker (J q.2).mulVecLin) ∧
                (0 < Module.finrank ℝ (LinearMap.ker (J q.2).mulVecLin) → R ≠ 0) := by
  obtain ⟨σ, B₀, U, hB₀, h0, hU, hyU, hUΩ, hσ, hσ0, hσΩ, hlevel,
    himm, hinj, himage, ℓ, B, v, a, r, T, Φ, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    hΨ, hinit, hvar, e, g, D, he, hzes, hesub, hg, hgsub, hgi,
    hD, hqD, hDsub, hPC2, hgraph, Q, hQ, hqQ, hQD, hstructure⟩ :=
    hF.exists_potentialLevel_graphStructure x₀ hΩ hf hy₀ hz hmatch hpositive t₀
  refine ⟨σ, B₀, U, hB₀, h0, hU, hyU, hUΩ, hσ, hσ0, hσΩ, hlevel,
    himm, hinj, himage, ℓ, B, v, a, r, T, Φ, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    hΨ, hinit, hvar, e, g, D, he, hzes, hesub, hg, hgsub, hgi,
    hD, hqD, hDsub, hPC2, hgraph, Q, hQ, hqQ, hQD, ?_⟩
  intro q hq hlabel
  have hs := hstructure q hq hlabel
  have hpt (z) (hz : z ∈ D) := g.map_source (hgraph z hz).1
  simp only [hg] at hpt
  have hODE := fun z hz ↦ (hgraph z hz).2.1
  have hsm := hF.chartGraph_family_contDiffOn_slice x₀ hgsub hgi hD hPC2 hODE q.1
    (fun t ht ↦ hpt (q.1, t) ht)
  have hfc := hF.chartGraph_regular_focal_bounds x₀ (Module.finBasis ℝ V)
    (Module.finBasis ℝ V) hg hgsub hgi hD hPC2 hODE (hQD hq)
    (hpt q (hQD hq)) hs.1 hs.2.1
  refine ⟨hsm.2, hfc.1, hfc.2, ?_⟩
  exact hF.chartGraph_exists_smooth_inverse_pole x₀ (Module.finBasis ℝ V)
    (Module.finBasis ℝ V) hg hgsub hgi hD hPC2 hODE (hQD hq)
    (fun t ht ↦ hpt (q.1, t) ht) hs.1 hs.2.1

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
