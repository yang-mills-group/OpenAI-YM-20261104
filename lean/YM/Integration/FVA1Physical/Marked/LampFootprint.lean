import YM.Integration.FVA1Physical.Marked.QuayLampSpatial
import YM.Corona.Fill

/-! For an actually local family at arbitrary relative placements, charge just
one native block for the whole support, and remove the inverse square-root
from the failed-mask invoice using its independently purchased allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Source Labels
open Next.Foundations Push.Local Push.AbsoluteSums Animals LocalLTE
open Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I] {d:ℕ} {n:Side}

theorem lamp_one_ball (a:I → CoverLabel G d) (v:I → Site n) (r b:ℕ)
    (placed:∀ j,separation (v j) 0 ≤ r) (fit:r+Vault.terr G d ≤ b) :
    coverNumber b (lampSupport a v) ≤ 1 := by
  have inside:lampSupport a v⊆halo b {0} := by
    intro x hx
    apply halo_spec.mpr
    refine ⟨0,mem_singleton_self _,?_⟩
    rcases mem_insert.mp hx with eq|hx
    · subst x;simp
    obtain ⟨j,_,hj⟩:=mem_biUnion.mp hx
    have local':=Vault.placeV G (show (a j).1.val ≤ d from Nat.le_of_lt_succ (a j).1.isLt) (v j) hj
    have reach:separation (v j) x ≤ Vault.terr G d := (neighbors_mem ..).mp local'
    have near:separation 0 (v j) ≤ r:=separation_comm (v j) 0 ▸ placed j
    exact (separation_triangle 0 (v j) x).trans ((Nat.add_le_add near reach).trans fit)
  have c:covers b (lampSupport a v) {0}:=⟨inside,Corona.ship_halo _ (fun x hx y hy=>by
    rw [mem_singleton.mp hx,mem_singleton.mp hy])⟩
  simpa using Corona.list_cost b c

theorem birth_one_ball (B:BudgetPoint) (T:Support n) {w u e:ℝ} (positive:0 < w)
    (permit:hitWidth B*Real.sqrt w ≤ 1) (upper:coverNumber B.B T ≤ 1) (u0:0 ≤ u) (e0:0 ≤ e) :
    birthCost B T w u e ≤ Real.exp (B.supportExponent+2)*(u+e) := by
  have small:(coverNumber B.B T:ℝ) ≤ 1:=by exact_mod_cast upper
  have first:=mul_le_mul_of_nonneg_left small B.exponent_pos.le
  have second:=mul_le_mul_of_nonneg_left small (show 0 ≤ B.supportExponent+2 by linarith only [B.exponent_pos])
  have costReg:B.mass T u ≤ Real.exp (B.supportExponent+2)*u:=
    mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith only [first])) u0
  have costK:reservedMass B T e ≤ Real.exp (B.supportExponent+2)*e :=
    mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith only [second])) e0
  have price : hitWidth B*w*reservedMass B T e/Real.sqrt w ≤ reservedMass B T e := by
    have E:0 ≤ reservedMass B T e:=mul_nonneg (Real.exp_pos _).le e0
    have factor : hitWidth B*w ≤ Real.sqrt w := by
      have := mul_le_mul_of_nonneg_right permit (Real.sqrt_nonneg w)
      rwa [mul_assoc,Real.mul_self_sqrt positive.le,one_mul] at this
    exact (div_le_iff₀ (Real.sqrt_pos.mpr positive)).mpr
      ((mul_le_mul_of_nonneg_right factor E).trans_eq (mul_comm ..))
  exact (add_le_add costReg (price.trans costK)).trans_eq (mul_add ..).symm
end YM.Integration.FVA1Physical.Marked
