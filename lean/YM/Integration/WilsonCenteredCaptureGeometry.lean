import YM.Integration.WilsonCenteredLampCapture
import YM.Integration.WilsonReportRetainedRadius
import YM.Corona.Halo

/-! The price for independent children in the capture cell is funded by the
original reporting-radius forecast. A complete physical B-halo is enough. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureGeometry
open Finset Lattice RG Wilson Push.Local
open scoped Classical BigOperators
variable {n : Side} {G : Gauge}

theorem motion (p : BudgetPoint) {rad : ℕ} (near : rad≤p.B)
    {J : Type} (s : Finset J) (two : s.card≤2) :
    WilsonCenteredLampCapture.stage p rad s≤WilsonReportRetainedAnchor.reprice p p.B := by
  have seats : ((s.card+1:ℕ):ℝ)≤3 := by exact_mod_cast (show s.card+1≤3 by omega)
  have pp : 1≤p.power := Nat.le_trans (by decide : 1≤2) p.power_ge
  have three : (3:ℝ) ≤ 3^p.power := by
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤3 by norm_num) pp
  have base : 3*(1+(rad:ℝ))≤1+((p.B*(4*p.B+2)+2*p.B:ℕ):ℝ) := by
    have hj : (rad:ℝ)≤p.B := by exact_mod_cast near
    have B : (1:ℝ)≤p.B := by exact_mod_cast p.B_pos
    push_cast
    nlinarith only [hj,B,sq_nonneg ((p.B:ℝ)-1)]
  apply pow_le_pow_left₀ (by positivity)
  calc
    _ ≤ 3^p.power*(1+(rad:ℝ))^p.power := mul_le_mul_of_nonneg_right (seats.trans three) (by positivity)
    _ = (3*(1+(rad:ℝ)))^p.power := (mul_pow ..).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) base _

theorem housing (p : BudgetPoint) (Z : Support n) (y : Site n) (near : Z⊆halo p.B {y}) :
    coverNumber p.B Z≤81 := by
  have one:=Corona.tile y 1 p.B p.B_pos
  exact (Corona.cover_mono near p.B).trans (by simpa using one)

theorem cover (p : BudgetPoint) (Z : Support n) (y : Site n) (near : Z⊆halo p.B {y}) {α : ℝ}
    (width : p.supportExponent≤α) :
    Real.exp ((p.supportExponent+2)*coverNumber p.B Z) ≤ Real.exp ((α+2)*81) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul (by linarith only [width]) (by exact_mod_cast housing p Z y near) (Nat.cast_nonneg _)
    (by have :=p.exponent_pos;linarith)

end YM.Integration.WilsonCenteredCaptureGeometry
