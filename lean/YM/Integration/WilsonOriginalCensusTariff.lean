import YM.Integration.WilsonOriginalCensusPhysicalLoad
import YM.Integration.WilsonEmittedLongFunds

/-! The two actual printed group rows use the finite source shelf when their
unmasked terms are summed. Increasing Taylor precision changes the lower time
threshold and the fixed constants in the short-jet salary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusTariff
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonEmittedWordJointFare WilsonEmittedFiledCatalogue WilsonEmittedJoinedFares
open WilsonOriginalCensusPhysicalLoad Filter
open scoped BigOperators

def debit (source physical:ℕ):ℕ:=source+2*(physical+219)

theorem measured {g H β:ℝ}(_gp:0<g)(H₀:0<H)(bb:0<β)(lower:H/2 ≤ β)
    (clock:g=(Real.sqrt β)⁻¹)(n:ℕ):H^n ≤ 2^n*(g^(2*n))⁻¹:=by
  have eq₂:g^2=β⁻¹:=by rw [clock,inv_pow,Real.sq_sqrt bb.le]
  have h:H ≤ 2*(g^2)⁻¹:=by rw [eq₂,inv_inv];linarith
  simpa [mul_pow,inv_pow,pow_mul] using pow_le_pow_left₀ H₀.le h n

theorem logarithm (C:ℝ)(k:ℕ):∀ᶠH:ℝ in atTop,C*(1+Real.log H)^k  ≤  H:=by
  let A:=(max 1 |C|)*2^k
  have ap:0<A:=mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left ..)) (by positivity)
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    (Real.isLittleO_pow_log_id_atTop (n:=k)).bound (inv_pos.mpr ap)] with H high h
  have hp:0<H:=(Real.exp_pos _).trans_le high
  have lg:1 ≤ Real.log H:=(Real.le_log_iff_exp_le hp).mpr high
  have small:(Real.log H)^k ≤ A⁻¹*H:=by
    simpa [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (zero_le_one.trans lg) k),abs_of_pos hp,
      abs_of_nonneg (zero_le_one.trans lg)] using h
  calc
    _  ≤  (max 1 |C|)*(2*Real.log H)^k:=mul_le_mul ((le_abs_self _).trans (le_max_right ..))
      (pow_le_pow_left₀ (by linarith) (by linarith) k) (by positivity)
      (zero_le_one.trans (le_max_left ..))
    _ = A*(Real.log H)^k:=by rw [mul_pow];ring
    _  ≤  A*(A⁻¹*H):=mul_le_mul_of_nonneg_left small ap.le
    _ = H:=by rw [←mul_assoc,mul_inv_cancel₀ ap.ne',one_mul]

variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]{C:Census V}
variable (tube:LinkTube G)(B:BudgetPoint)(s:C.Mode)(w:Bool→V→ℝ)(c:Bool→ℝ)
  (d:Bool→V→ℕ)(ℓ p:Bool→ℕ)(b σ:Bool→ℝ)
local notation "D" => rank d
local notation "seats₀" => (fun _:Bool=>Fintype.card V)
local notation "shelves" => (fun _:Bool=>rank d)
local notation "ζ" => (fun a=>WilsonEmittedCompactTariff.strip (σ a))
local notation "k₀" => (max (p false) (p true)+D+1)
local notation "income" => cash s w c b
local notation "word" g:max => WilsonEmittedLongInvoice.gross w c (fun _=>0) B s 0 g p seats₀ shelves b ζ
local notation "jet" J:max => rent (G:=G) w c ℓ B (p:=p) (pieces:=seats₀) (depth:=shelves)
    (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=ζ) s J 0
local notation "F" => ((2:ℝ)^(D+1)*WilsonEmittedGrossTariff.fixedCost)
local notation "posted" A:max => A*(2+(F)*2^(D+219)*Real.exp 1)

theorem original {H β g A L:ℝ}(source J:ℕ)(hi:1<H)(early:1 ≤ Real.log H)
    (positive:0<g)(small:g ≤ 1)(bb:0<β)(lower:H/2 ≤ β)(upper:β ≤ 2*H)(clock:g=(Real.sqrt β)⁻¹)
    (square:B.B=Nat.ceil ((Real.log H)^2))(tax:B.supportExponent+2 ≤ 102)
    (toll:∀a,0<Poly.toll (w a) s)(salary:∀a,0 ≤ b a)(width:∀a,0<σ a)
    (reserve:∀a,Real.exp (((σ a)⁻¹)^2) ≤ H)
    (begun:∀a,(p a+D+1:ℕ) ≤ Real.log H ∧ (Fintype.card V:ℝ) ≤ Real.log H ∧ (2:ℝ)^(p a+D+1) ≤ H)
    (fixedFee:∀a,|WilsonEmittedTransitionJet.fee J (ℓ a)
      (WilsonEmittedCompactTariff.fixed G J (p a+D+1) (Fintype.card V))| ≤ L)
    (stage:groupPrice tube 0*L*(1+Real.log H)^(13+J*(k₀)) ≤ H)
    (Ap:0 ≤ A)(paid:(income) ≤ A*(g^source)⁻¹):
    0 ≤ posted A ∧ groupPrice tube 0*(jet J) ≤ (posted A)*(g^(debit source D))⁻¹ ∧
      (word g) ≤ (posted A)*(g^(debit source D))⁻¹:=by
  have Hpos:=zero_lt_one.trans hi
  have Fpos:0  ≤  WilsonEmittedGrossTariff.fixedCost:=by unfold WilsonEmittedGrossTariff.fixedCost;positivity
  have nonneg:0  ≤  F:=mul_nonneg (by positivity) Fpos
  have wage:0 ≤ income:=sum_nonneg fun a _=>mul_nonneg (abs_nonneg _)
    (mul_nonneg (inv_nonneg.mpr (toll a).le) (salary a))
  have stock:0 ≤ posted A:=by positivity
  have low:∀a,p a + D+1  ≤  k₀:=by
    intro a
    have bill:p a ≤ max (p false) (p true):=by cases a <;> simp
    omega
  have short:=WilsonEmittedJoinedFares.original G B s w c ℓ p seats₀ shelves b
    (fun _=>B.supportExponent+2) σ (J:=J) (k:=k₀) (m:=0) (by linarith:1 ≤ 1+Real.log H)
    zero_le_one square fixedFee low toll (fun a=>⟨salary a,tax,width a,reserve a⟩) (by simp)
  rw [mul_one] at short
  have jets:groupPrice tube 0*(jet J) ≤ income*H:=calc
    _  ≤  groupPrice tube 0*((income)*L*(1+Real.log H)^(13+J*(k₀))):=
      mul_le_mul_of_nonneg_left short (price_nonneg tube 0)
    _ = (income)*(groupPrice tube 0*L*(1+Real.log H)^(13+J*(k₀))):=by ring
    _  ≤  _:=mul_le_mul_of_nonneg_left stage wage
  have long:=WilsonEmittedLongFunds.unrestricted s w c (fun _=>0) p seats₀ shelves b ζ B D 0
    positive small (Real.exp_pos 1).le hi early bb upper clock square tax toll σ
    (fun a=>⟨(begun a).1,(begun a).2.1,(begun a).2.2,le_rfl⟩)
    (fun a=>⟨salary a,width a,reserve a,le_rfl,Real.exp_le_exp.mpr (min_le_left ..)⟩)
  have Hh:=measured positive Hpos bb lower clock (D+219)
  have unif:(income)*H^(D+219)  ≤  A*2^(D+219)*(g^(debit source D))⁻¹:=calc
    _  ≤  (A*(g^source)⁻¹)*(2^(D+219)*(g^(2*(D+219)))⁻¹):=mul_le_mul paid Hh (pow_nonneg Hpos.le _) (by positivity)
    _ = _:=by rw [debit,pow_add g source,mul_inv];ring
  have shortPrice:groupPrice tube 0*(jet J)  ≤  A*2*(g^(debit source D))⁻¹:=by
    have first:=measured positive Hpos bb lower clock 1
    simp only [pow_one,Nat.mul_one] at first
    have push:(g^2)⁻¹ ≤ (g^(2*(D+219)))⁻¹:=by
      apply inv_anti₀ (pow_pos positive _)
      apply pow_le_pow_of_le_one positive.le small
      omega
    apply jets.trans
    calc _  ≤  (A*(g^source)⁻¹)*(2*(g^(2*(D+219)))⁻¹):=
           mul_le_mul paid (first.trans (mul_le_mul_of_nonneg_left push (by norm_num))) Hpos.le (by positivity)
         _ = _:=by rw [debit,pow_add g source,mul_inv];ring
  refine ⟨stock,shortPrice.trans (mul_le_mul_of_nonneg_right ?_ (by positivity)),long.trans ?_⟩
  · apply mul_le_mul_of_nonneg_left _ Ap
    exact le_add_of_nonneg_right (by positivity)
  · change (income)*(F)*H^(D+2+217)*Real.exp 1  ≤  _
    calc _ = ((income)*H^(D+219))*(F*Real.exp 1):=by rw [show D+2+217=D+219 by omega];ring
         _  ≤  (A*2^(D+219)*(g^(debit source D))⁻¹)*(F*Real.exp 1):=mul_le_mul_of_nonneg_right unif (by positivity)
         _  ≤  _:=by
           have add:0  ≤  2*A*(g^(debit source D))⁻¹:=by positivity
           linarith only [add]

end YM.Integration.WilsonOriginalCensusTariff
end
