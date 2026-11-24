import YM.Integration.WilsonEmittedGrossTariff
/-! The full signed long-row sum on its actual root cash, with distinct regular and unrestricted charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedLongFunds
open Lattice Marker Wilson RG QuadraticLocal QuadraticLocal.Earn Push Push.AbsoluteSums Push.AbsoluteSums.Animals
open WilsonEmittedGroupWallet WilsonEmittedJoinedFares WilsonEmittedLongInvoice
open WilsonEmittedGrossTariff

variable {G:Gauge} {A V:Type} [Fintype A] [DecidableEq V] {Γ:Census V} (s:Γ.Mode)
variable (w:A→V→ℝ) (c:A→ℝ) (ν p pieces depth:A→ℕ) (b K θ:A→ℝ)
variable (B:BudgetPoint)

omit [Fintype A] in
private theorem scalar_norm {g:ℝ} (hp:0<g) (h1:g≤1) (u:A) :
    ‖scalar c ν g u‖≤|c u|:=by
  unfold scalar
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hp.le _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hp.le h1)

theorem soft {g F τ:ℝ} (m:ℕ) (hp:0<g) (h1:g≤1) (toll:∀a,0<Poly.toll (w a) s)
    (hb:∀a,0≤b a) (F0:0≤F) (t0:0≤τ)
    (price:∀a,Invoice.price B (K a) (p a+depth a+1) (pieces a) (B.supportExponent+2) (θ a) G≤F)
    (small:∀a,Real.exp (-θ a)^m≤τ) :
    budget (G:=G) w c ν B s m g p pieces depth K b θ ≤ cash s w c b*F*τ := by
  unfold budget cash
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum;intro a _
  let t:=(Poly.toll (w a) s)⁻¹
  have tp:0≤t:=inv_nonneg.mpr (toll a).le
  have ba:=hb a
  have nom:=mul_le_mul_of_nonneg_right (price a) (hb a)
  have pay:=mul_le_mul nom (small a) (pow_nonneg (Real.exp_pos _).le _) (mul_nonneg F0 (hb a))
  have moved:=mul_le_mul_of_nonneg_left pay tp
  calc
    _ ≤ ‖scalar c ν g a‖*(t*(F*b a*τ)):=mul_le_mul_of_nonneg_left moved (norm_nonneg _)
    _ ≤ |c a| *(t*(F*b a*τ)):=mul_le_mul_of_nonneg_right (scalar_norm c ν hp h1 a) (by positivity)
    _ = _:=by ring

theorem unrestricted {H β g Ω:ℝ} (d m:ℕ) (hp:0<g) (h1:g≤1) (Ω0:0≤Ω)
    (H1:1<H) (logH:1≤Real.log H) (_bb:0<β) (upper:β≤2*H) (coin:g=(Real.sqrt β)⁻¹)
    (sized:B.B=Nat.ceil ((Real.log H)^2)) (tax:B.supportExponent+2≤102)
    (toll:∀a,0<Poly.toll (w a) s) (σ:A→ℝ)
    (school:∀a, (p a+depth a+1:ℕ)≤Real.log H ∧ (pieces a:ℝ)≤Real.log H ∧
        (2:ℝ)^(p a+depth a+1)≤H ∧ depth a≤d)
    (paid:∀a,0≤b a ∧ 0<σ a ∧ Real.exp (((σ a)⁻¹)^2)≤H ∧
        WilsonEmittedCompactTariff.strip (σ a)≤θ a ∧ Real.exp (θ a)≤Ω) :
    gross w c ν B s m g p pieces depth b θ ≤
      cash s w c b * ((2:ℝ)^(d+1)*WilsonEmittedGrossTariff.fixedCost)*H^(d+2+217)*Ω := by
  have gr:1≤g⁻¹:=(one_le_inv₀ hp).mpr h1
  have gcap:g⁻¹≤2*H:=by
    rw [coin,inv_inv]
    exact (Real.sqrt_le_iff).mpr ⟨by linarith,by nlinarith [sq_nonneg (H-1)]⟩
  have fixed0:0≤WilsonEmittedGrossTariff.fixedCost:=by unfold WilsonEmittedGrossTariff.fixedCost;positivity
  have H0:0≤H:=zero_le_one.trans H1.le
  unfold gross cash
  rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum;intro a _
  have A0:=paid a
  have ba:=A0.1
  have sA:=school a
  let t:=(Poly.toll (w a) s)⁻¹
  have f0:0≤t:=inv_nonneg.mpr (toll a).le
  have sf:=WilsonEmittedGrossTariff.original B (p a+depth a+1) (pieces a) m H1 logH sized
    sA.1 sA.2.1 A0.2.1 A0.2.2.1 A0.2.2.2.1 tax A0.1
  have bill:=sf.trans (mul_le_mul_of_nonneg_left A0.2.2.2.2 (by positivity))
  have p1: (g^(depth a+1))⁻¹≤(2:ℝ)^(d+1)*H^(d+1):=by
    rw [←inv_pow,←mul_pow]
    exact (pow_le_pow_right₀ gr (Nat.succ_le_succ sA.2.2.2)).trans (pow_le_pow_left₀ (inv_nonneg.mpr hp.le) gcap _)
  have roof:ceiling g (p a) (depth a) ≤ 2^(d+1)*H^(d+2):=by
    exact (mul_le_mul p1 sA.2.2.1 (by positivity) (by positivity)).trans_eq (by rw [show d+2=(d+1)+1 by omega,pow_succ];ring)
  have ceil0:0≤ceiling g (p a) (depth a):=by unfold ceiling;positivity
  have rent0:0≤t*(b a*fixedCost*H^217*Ω):=by positivity
  calc
    _ ≤ ‖scalar c ν g a‖ * (ceiling g (p a) (depth a)*(t*(b a*fixedCost*H^217*Ω))):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bill f0) ceil0) (norm_nonneg _)
    _ ≤ |c a| * (2^(d+1)*H^(d+2)*(t*(b a*fixedCost*H^217*Ω))):=
      mul_le_mul (scalar_norm c ν hp h1 a) (mul_le_mul_of_nonneg_right roof rent0)
        (mul_nonneg ceil0 rent0) (abs_nonneg _)
    _ = _:=by rw [pow_add H (d+2) 217];ring

end YM.Integration.WilsonEmittedLongFunds
end
