import YM.Integration.WilsonEmittedOriginalCalendar
/-! Transfer the stated quotes of the original figure at its actual strip into the complete source wallets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedPostedFigure
open Lattice Wilson RG QuadraticLocal QuadraticLocal.Earn
open WilsonEmittedSignedTariff

theorem school {H C:ℝ} (hp:0<H) (cap p t u:ℕ) (hc:(2:ℝ)^cap≤C) (bought:C≤Real.log H)
    (hr:p≤cap) (ht:t≤cap) (hu:u≤cap) :
    (p:ℝ)≤Real.log H ∧ (t:ℝ)≤Real.log H ∧ (2:ℝ)^p≤H ∧ (2:ℝ)^u≤H := by
  have grows (n:ℕ):(n:ℝ)≤(2:ℝ)^n:=by
    induction n with
    | zero=>norm_num
    | succ n ih=>
      rw [Nat.cast_succ,pow_succ];linarith [show (1:ℝ)≤2^n from one_le_pow₀ (by norm_num) (n:=n)]
  have levels (n:ℕ) (h:n≤cap):(2:ℝ)^n≤Real.log H:=
    (pow_le_pow_right₀ (by norm_num:1≤(2:ℝ)) h).trans (hc.trans bought)
  have physical:Real.log H≤H:=by linarith [Real.log_le_sub_one_of_pos hp]
  exact ⟨(grows p).trans (levels _ hr),(grows t).trans (levels _ ht),
    (levels _ hr).trans physical,(levels _ hu).trans physical⟩

theorem paid (G:Gauge) (B:BudgetPoint) (p d t u T:ℕ) {g H K σ ω:ℝ}
    (hp:0<H) (w0:0≤ω) (clock:ω≤H) (wide:(2:ℝ)^u≤H) (cap:B.supportExponent+2≤102)
    (size:B.B=Nat.ceil ((Real.log H)^2)) (late:(256*((T:ℝ)+1))^2≤Real.log H)
    (sealed:Real.exp ((σ⁻¹)^2)≤H)
    (scope:Invoice.Supports B K (B.supportExponent+2) g σ (σ/4))
    (global:Real.exp ((σ/4)/2)≤16*(2^u*ω))
    (rent:Invoice.price B K (p+d+1) t (B.supportExponent+2) (σ/4) G≤256*(2^u*ω)^3) :
    Real.exp (σ/4)≤ stageCost*H^4 ∧
    Invoice.price B K (p+d+1) t (B.supportExponent+2) (σ/4) G≤ stageCost*H^6 ∧
    Real.exp (-(σ/4))^(B.B/32)≤(H^T)⁻¹ :=by
  have bound:2^u*ω≤H^2:=(mul_le_mul wide clock w0 hp.le).trans_eq (by ring)
  have material:=global.trans (mul_le_mul_of_nonneg_left bound (by norm_num))
  have paid:=rent.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by positivity) w0) bound 3) (by norm_num))
  have stage:(256:ℝ)≤ stageCost:=by unfold stageCost;linarith [Real.add_one_le_exp (1:ℝ)]
  have wage:Real.exp (σ/4)=(Real.exp ((σ/4)/2))^2:=by
    rw [←Real.exp_nat_mul];congr 1;ring
  have chosen:WilsonEmittedLengthWindow.strip (σ/4) σ=σ/4:=
    max_eq_left (min_le_right ..)
  refine ⟨?_,?_,?_⟩
  · rw [wage]
    exact ((pow_le_pow_left₀ (Real.exp_pos _).le material 2).trans_eq
      (show ((16:ℝ)*H^2)^2=256*H^4 by ring)).trans (mul_le_mul_of_nonneg_right stage (pow_nonneg hp.le _))
  · rw [←pow_mul] at paid
    exact paid.trans (mul_le_mul_of_nonneg_right stage (pow_nonneg hp.le _))
  · simpa only [chosen] using (WilsonEmittedLengthWindow.decays scope size sealed cap T late).2

end YM.Integration.WilsonEmittedPostedFigure
end
