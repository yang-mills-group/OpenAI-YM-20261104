import YM.Integration.WilsonPhysicalHistoryRetainedSpringGrowth
import YM.Integration.WilsonPhysicalHistoryKioskHeatOrder

/-! Physical heat absorbs a period-independent polynomial in the genuine
stage temperature before the upper cutoff and any marked positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice RG Wilson OPE.Therm
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pert.Asymptotics
open scoped Classical Topology
open private rent from YM.Integration.WilsonPhysicalHistoryKioskHeatOrder
variable {G : Gauge}

theorem spring_mask_clock (R : Run G) (simple : G.Simple) (d q : ℕ) {C ε : ℝ} (cn : 0≤C) (ep : 0<ε) :
    ∀ᶠ i : ℕ in atTop,∀N,i≤N→∀ per,
      let V:=R.family.path.levels
      let g:=regulatorRun R.family N per i
      C*(1+V.clock.hatBeta i)^d*((625*(Fintype.card PlaqAxes:ℝ))*V.clock.forcedAllowance i)≤ε*g^q := by
  let V:=R.family.path.levels
  have C0 : 0≤C*4^d:=by positivity
  filter_upwards [rent R simple (2*d) q C0 ep] with i bank N live per A g
  let β:=R.family.path.β N per i
  have x1:=V.fits.delayed i
  have band:V.clock.hatBeta i/2≤β:=(R.makes.wilson.represents N per i live).band.1
  have b0:0<β:=by linarith
  have z0:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr b0)
  have g2:g^2=β⁻¹:=by change (Real.sqrt β)⁻¹^2=β⁻¹; rw [inv_pow,Real.sq_sqrt b0.le]
  have stage : 1+V.clock.hatBeta i≤4*β:=by linarith
  have fee : 0≤(625*(Fintype.card PlaqAxes:ℝ))*V.clock.forcedAllowance i:=
    mul_nonneg (by positivity) (Real.exp_pos _).le
  have price : C*(1+V.clock.hatBeta i)^d≤(C*4^d)/g^(2*d):= by
    calc
      _ ≤ C*(4*β)^d:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) stage _) cn
      _ = (C*4^d)/g^(2*d):=by rw [pow_mul,g2,inv_pow,div_inv_eq_mul,mul_pow];ring
  exact (mul_le_mul_of_nonneg_right price fee).trans (by simpa only [mul_assoc] using bank N live per)

theorem spring_cover_bound (V : Levels G) (i : ℕ) :
    (((2*(V.budget i).B+1)^4:ℕ):ℝ) ≤625*(1+V.clock.hatBeta i)^8 := by
  let x:=V.clock.hatBeta i
  have x1:1<x:=V.fits.delayed i
  have lo:0≤Real.log x:=(Real.log_pos x1).le
  have hi:Real.log x≤x:=(Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have n : (((V.budget i).B:ℕ):ℝ)≤x^2+1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log x))).le.trans (by gcongr)
  have ball : 2*(((V.budget i).B:ℕ):ℝ)+1≤5*(1+x)^2:=by nlinarith [sq_nonneg x]
  push_cast
  calc
    _ ≤ (5*(1+x)^2)^4:=pow_le_pow_left₀ (by positivity) ball _
    _ = 625*(1+V.clock.hatBeta i)^8:=by dsimp only [x];ring

end YM.Integration.OriginalMarkedRunAction
