import OTSelector.Geometry.FinslerSeedEndpointGraphData
import OTSelector.Analysis.ODE.GraphHamiltonianCoefficientContinuity
import OTSelector.Reconstruction.ClosedJacobiConditionalMoments
import OTSelector.Analysis.Calculus.GraphClockClosedInverse

/-!
# The closed Jacobi system of the selected actual endpoint graph

The endpoint record retains its original graph and Legendre inverses. Reading its
actual phase in fixed bases produces the closed system without selecting another
chart, and the positive clock transfers closed physical intervals to that system.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData

open OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E W V M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {A : E ≃L[ℝ] (ℝ × V)}
  {Γ : W → ℝ → M} {B : Set W} {w : W} {old : M} {t₀ : ℝ}

omit [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] in
/-- The selected endpoint graph itself supplies the actual closed system; no new
choice of graph inverse, Legendre branch, phase or endpoint data is made. -/
theorem closedJacobiSystem
    (G : EndpointGraphData F A Γ B w old t₀) (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) {a b : ℝ}
    (hI : ∀ s ∈ Icc a b, (w, s) ∈ G.D) :
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
    let L := F.adaptedGraphLagrangian old A
    let Ψ := F.adaptedGraphPhase old A γ G.e
    let Z := fun s ↦ fderiv ℝ (fun z ↦ Ψ (z, s)) w
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    let P := fun s ↦ covectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).2)
    let Aₛ := fun s ↦ hamiltonianMatrixA bV (GraphHamiltonian.blockA L G.g s (Ψ (w, s)))
    let Bₛ := fun s ↦ hamiltonianMatrixB bV (GraphHamiltonian.blockB L G.g s (Ψ (w, s)))
    let Cₛ := fun s ↦ hamiltonianMatrixC bV (GraphHamiltonian.blockC L G.g s (Ψ (w, s)))
    ClosedHamiltonianJacobiSystem J P Aₛ Bₛ Cₛ a b := by
  obtain ⟨he, hs, hB, hg, hsub, hG, hD, hcenter, htarget, hΨ, hJacobi, hphase⟩ := G.raw
  let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
  let Ψ := F.adaptedGraphPhase old A γ G.e
  have hODE (q : W × ℝ) (hq : q ∈ G.D) : HasDerivAt (fun s ↦ Ψ (q.1, s))
      (GraphHamiltonian.field (F.adaptedGraphLagrangian old A) G.g q.2 (Ψ q)) q.2 :=
    (hJacobi q hq).2.1
  have hp (s : ℝ) (hs : (w, s) ∈ G.D) :
      ((s, (Ψ (w, s)).1), (Ψ (w, s)).2) ∈ G.g.target := by
    have h := G.g.map_source (hJacobi (w, s) hs).1
    rw [hg] at h
    exact h
  have hmat (s : ℝ) (hs : (w, s) ∈ G.D) :=
    hF.adaptedGraph_parameter_matrices old A bW bV hg hsub hG hD hΨ hODE hs (hp s hs)
      (hphase (w, s) hs rfl).1 (hphase (w, s) hs rfl).2
  have hpath : ContinuousOn (fun s ↦ Ψ (w, s)) (Icc a b) :=
    hΨ.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hI
  obtain ⟨hA, hBb, hC⟩ := continuousOn_graphHamiltonian_matrix_coefficients bV
    ((hF.contDiffOn_adaptedGraphLagrangian old A).mono hsub) hG hpath
    (fun s hs ↦ hp s (hI s hs))
  exact {
    position_derivative := fun s hs ↦ (hmat s (hI s hs)).1
    momentum_derivative := fun s hs ↦ (hmat s (hI s hs)).2.1
    continuous_A := hA
    continuous_B := hBb
    continuous_C := hC
    symmetric_A := fun s hs ↦ (hmat s (hI s hs)).2.2.1
    symmetric_C := fun s hs ↦ (hmat s (hI s hs)).2.2.2.1
    positive_C := fun s hs ↦ (hmat s (hI s hs)).2.2.2.2.1
    wronskian := fun s hs ↦ (hmat s (hI s hs)).2.2.2.2.2.1
    phase_rank := fun s hs ↦ (hmat s (hI s hs)).2.2.2.2.2.2.1 }

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] in
/-- The exact graph image of a closed physical endpoint interval lies in the same
phase domain. This discharges the closed-system interval inclusion from actual data. -/
theorem closedGraphInterval_subset_phase
    (G : EndpointGraphData F A Γ B w old t₀) {a b : ℝ} (hab : a ≤ b)
    (hI : ∀ t ∈ Icc a b, (w, t) ∈ G.U) :
    let s := fun t ↦ (A (extChartAt 𝓘(ℝ, E) old (Γ w t))).1
    ∀ r ∈ Icc (s a) (s b), (w, r) ∈ G.D := by
  let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))
  have hγ (t : ℝ) (ht : t ∈ Icc a b) : DifferentiableAt ℝ γ (w, t) :=
    (G.position_C2.contDiffAt (G.open_U.mem_nhds (hI t ht))).differentiableAt (by norm_num)
  have himage := (curveGraphClock_closedInverse_data G.raw.1 hab
    (fun t ht ↦ G.source_U (hI t ht)) hγ
    (fun t ht ↦ (G.regular (w, t) (hI t (Ioo_subset_Icc_self ht))).1)).1
  dsimp only
  intro r hr
  rw [← himage] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  have h := G.mapsTo_phase (hI t ht)
  simpa only [G.raw.1, curveGraphCoordinateMap] using h

end OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
