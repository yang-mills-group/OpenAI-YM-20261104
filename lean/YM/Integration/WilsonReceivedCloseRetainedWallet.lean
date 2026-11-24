import YM.Integration.WilsonReceivedCloseRetainedRent
import YM.Integration.WilsonReceivedCloseFaceBudget

/-! All slot fees are restored once at the actual receiving coupling. The
constant in the physical birth sale costs one extra power per entire face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseRetainedWallet
open Finset Filter Marker Lattice WilsonLimitConstruction OPE OPE.Log Trace.Pilot PhysicalNext.Repeat.Legato Bandage
open scoped BigOperators
def fee (u:ℝ) (d a:ℕ) : ℝ := u^a*3^(d*a+1)
theorem nonneg (u:ℝ) (u₁:1≤u) (d a:ℕ) : 0 ≤ fee u d a := by
  unfold fee
  exact mul_nonneg (pow_nonneg (zero_le_one.trans u₁) _) (by positivity)
theorem face {V:Type} [DecidableEq V] [Fintype V] (R:Census V)
    (s:R.Mode) {d a:ℕ} (load:s.val.card≤a) {u x t:ℝ} (u₁:1≤u) (xp:0<x) (tp:0<t)
    (band:t≤3*x) {w:V→ℝ} (wp:∀v,0<w v) (sold:∀v,(w v)⁻¹≤u*(x⁻¹)^d)
    (late:fee u d a*x≤1) :
    t^(d*s.val.card+1) ≤ Poly.toll w s := by
  let r:=s.val.card
  have rp:r≤a:=load
  have whole:=WilsonReceivedCloseFaceBudget.product wp (active:=Finset.univ) s (Finset.subset_univ _) (fun v _=>sold v)
  have eqn : (3*x)^(d*r+1)*(u*(x⁻¹)^d)^r=(u^r*3^(d*r+1))*x := by
    rw [mul_pow 3 x,mul_pow u,← pow_mul,inv_pow,pow_succ x]
    field_simp [xp.ne']
  have raised: d*r+1≤d*a+1 := by gcongr
  have booked:u^r*3^(d*r+1)≤fee u d a := mul_le_mul (pow_le_pow_right₀ u₁ rp)
    (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤3) raised) (by positivity) (pow_nonneg (zero_le_one.trans u₁) _)
  have tollPos : 0 < Poly.toll w s := Finset.prod_pos (fun v _=>wp v)
  rw [← div_le_one tollPos,div_eq_mul_inv]
  calc
    _ ≤ (3*x)^(d*r+1)*(u*(x⁻¹)^d)^r := mul_le_mul (pow_le_pow_left₀ tp.le band _) whole
      (inv_nonneg.mpr tollPos.le) (by positivity)
    _ = _ := eqn
    _ ≤ fee u d a*x := mul_le_mul_of_nonneg_right booked xp.le
    _ ≤ _ := late

variable {G:Gauge} (R:Run G) (simple:G.Simple)
def Ready (p q d a:ℕ) (u ε:ℝ) (u₁:1≤u) (ep:0<ε) (b:ℕ) : Prop :=
  (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (WilsonReceivedCloseRetainedRent.nonneg p q) ep)).choose ≤ b ∧
  (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (nonneg u u₁ d a) (zero_lt_one:(0:ℝ)<1))).choose ≤ b

theorem original (p q d a:ℕ) (u ε:ℝ) (u₁:1≤u) (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop, ∀ b, m≤b → Ready R simple p q d a u ε u₁ ep b := by
  let day₁:=(eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (WilsonReceivedCloseRetainedRent.nonneg p q) ep)).choose
  let day₂:=(eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (nonneg u u₁ d a) (zero_lt_one:(0:ℝ)<1))).choose
  filter_upwards [eventually_ge_atTop day₁,eventually_ge_atTop day₂] with m rent wallet
  exact fun b mb=>⟨rent.trans mb,wallet.trans mb⟩
end YM.Integration.WilsonReceivedCloseRetainedWallet
