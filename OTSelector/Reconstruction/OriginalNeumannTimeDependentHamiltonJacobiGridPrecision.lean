import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The actual quadratic grid errors are removed by choosing shifted time first
and then a genuine positive mesh, retaining the original mass multiplier. -/
namespace OTSelector.Reconstruction

/-- Every positive tolerance admits genuine positive time and grid parameters
for the full original finite-mass quadratic grid and lifting error. -/
theorem exists_neumannQuadratic_grid_precision (mass D M diam : ℝ)
    {ε : ℝ} (hε : 0<ε) :
    ∃δ:ℝ,0<δ ∧ ∃h:ℝ,0<h ∧
      mass*(D*h/(1+δ)+D*h/δ+M*δ+2*diam*h)<ε := by
  obtain ⟨δ,hδ,hδerror⟩:=exists_pos_mul_lt (half_pos hε) (mass*M)
  obtain ⟨h,hh,hherror⟩:=exists_pos_mul_lt (half_pos hε)
    (mass*(D/(1+δ)+D/δ+2*diam))
  refine ⟨δ,hδ,h,hh,?_⟩
  have heq : mass*(D*h/(1+δ)+D*h/δ+M*δ+2*diam*h)=
      mass*M*δ+mass*(D/(1+δ)+D/δ+2*diam)*h := by ring
  rw [heq]
  linarith only [hδerror,hherror]

end OTSelector.Reconstruction
