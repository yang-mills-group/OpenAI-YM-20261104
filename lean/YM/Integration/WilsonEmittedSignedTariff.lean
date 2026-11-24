import YM.Integration.WilsonEmittedLongFunds
/-! The full signed, rooted short and long original field invoice at fixed physical source dimension. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedSignedTariff
open Comparison.Density.Mirrors Lattice Marker Wilson RG QuadraticLocal QuadraticLocal.Earn Push Push.Local
open WilsonEmittedGroupWallet WilsonEmittedJoinedFares WilsonEmittedLongInvoice
open WilsonEmittedOutputPower WilsonEmittedGrossTariff
open scoped BigOperators
def boxCost:ℝ := Real.exp (102*5^4)
def stageCost:ℝ := 256*Real.exp 1
def softCost (T q:ℕ):ℝ := boxCost*(constant T*34*2^4)+34*stageCost*2^(q+3)
def hardCost (d:ℕ):ℝ := (boxCost+1)*(34*(2^(d+1)*fixedCost)*stageCost)

theorem onGroup {G:Gauge} {n:Side} (B:BudgetPoint) (y:Site n)
    {V A:Type} [Fintype A] [DecidableEq V] {Γ:Census V} (s:Γ.Mode)
    (w:A→V→ℝ) (c:A→ℝ) (ν p pieces depth:A→ℕ) (b K θ σ:A→ℝ)
    {H β g M:ℝ} (d pole q T:ℕ) (pole1:1≤pole) (chosen:T=2*4+pole+1+(q+3))
    (H1:1<H) (bb:0<β) (lower:H/2≤β) (upper:β≤2*H) (coin:g=(Real.sqrt β)⁻¹) (g1:g≤1)
    (logH:1≤Real.log H) (sized:B.B=Nat.ceil ((Real.log H)^2))
    (tax:B.supportExponent+2≤102) (M0:0≤M) (toll:∀a,0<Poly.toll (w a) s)
    (salary:cash s w c b≤34*H^4*M)
    (school:∀a, (p a+depth a+1:ℕ)≤Real.log H ∧ (pieces a:ℝ)≤Real.log H ∧
        (2:ℝ)^(p a+depth a+1)≤H ∧ depth a≤d)
    (bills:∀a,0≤b a ∧ 0<σ a ∧ Real.exp (((σ a)⁻¹)^2)≤H ∧
        WilsonEmittedCompactTariff.strip (σ a)≤θ a ∧ Real.exp (θ a)≤ stageCost*H^4)
    (prices:∀a,Invoice.price B (K a) (p a+depth a+1) (pieces a) (B.supportExponent+2) (θ a) G ≤ stageCost*H^6)
    (decay:∀a,Real.exp (-(θ a))^(B.B/32)≤(H^T)⁻¹) :
    let cube:=neighborhood (B.B+1) y
    reservedMass B cube (‖(↑((g^pole)⁻¹):ℂ)‖*(constant T*(cash s w c b*g⁻¹)*g^T))+
      budget (G:=G) w c ν B s (B.B/32) g p pieces depth K b θ ≤ softCost T q*M*g^(q+3) ∧
    reservedMass B cube (gross w c ν B s 0 g p pieces depth b θ)+
      gross w c ν B s (B.B/32) g p pieces depth b θ ≤ hardCost d * H^(d+227)*M :=by
  have H0:0<H:=zero_lt_one.trans H1
  have g0:0<g:=coin.symm ▸ inv_pos.mpr (Real.sqrt_pos.mpr bb)
  have stage0:0≤ stageCost:=by unfold stageCost;positivity
  have const0:0≤constant T:=by unfold constant;positivity
  have fixed0:0≤fixedCost:=by unfold fixedCost;positivity
  have box0:0≤boxCost:=(Real.exp_pos _).le
  have z:=WilsonEmittedShortTariff.tax B y tax
  have short:=WilsonEmittedOutputPower.paid bb lower H0 coin (by norm_num : (0:ℝ)≤34) M0 salary T chosen
  have live:‖(↑((g^pole)⁻¹):ℂ)‖=(g^pole)⁻¹:=by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg g0.le _))]
  have shortBox:reservedMass B (neighborhood (B.B+1) y)
       (‖(↑((g^pole)⁻¹):ℂ)‖*(constant T*(cash s w c b*g⁻¹)*g^T)) ≤
       boxCost*((constant T*34*2^4)*M*g^(q+3)):=by
    rw [live];unfold reservedMass
    exact (mul_le_mul_of_nonneg_left short (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right z (by positivity))
  have base:=WilsonEmittedLongFunds.soft (G:=G) s w c ν p pieces depth b K θ B (B.B/32) g0 g1 toll
    (fun a=>(bills a).1) (mul_nonneg stage0 (pow_nonneg H0.le 6)) (inv_nonneg.mpr (pow_nonneg H0.le T)) prices decay
  have far:T=10+(T-10):=by omega
  have found:(H^10)*(H^T)⁻¹=(H^(T-10))⁻¹:=by
    conv_lhs =>arg 2;arg 1;rw [far,pow_add]
    field_simp
  have power:(H^(T-10))⁻¹≤2^(q+3)*g^(q+3):=
    (inv_anti₀ (pow_pos H0 _) (pow_le_pow_right₀ H1.le (show q+3≤T-10 by omega))).trans
      (WilsonEmittedOutputPower.tail H0 bb upper g coin g1 (q+3))
  have long:=base.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right salary
    (mul_nonneg stage0 (pow_nonneg H0.le _))) (inv_nonneg.mpr (pow_nonneg H0.le _)))
  have long':budget (G:=G) w c ν B s (B.B/32) g p pieces depth K b θ ≤ 34*stageCost*M*(2^(q+3)*g^(q+3)):=by
    refine long.trans ?_
    rw [show 34*H^4*M*(stageCost*H^6)*(H^T)⁻¹ = (34*stageCost*M)*(H^10*(H^T)⁻¹) by ring,found]
    exact mul_le_mul_of_nonneg_left power (by positivity)
  dsimp only
  refine ⟨(add_le_add shortBox long').trans_eq (by unfold softCost;ring),?_⟩
  let raw:=34*((2:ℝ)^(d+1)*fixedCost)*stageCost*H^(d+227)*M
  have raw0:0≤raw:=by unfold raw;positivity
  have both (j:ℕ):gross w c ν B s j g p pieces depth b θ ≤ raw:=by
    have gross:=WilsonEmittedLongFunds.unrestricted s w c ν p pieces depth b θ B d j g0 g1
      (mul_nonneg stage0 (pow_nonneg H0.le 4)) H1 logH bb upper coin sized tax toll σ school bills
    refine gross.trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right salary
      (mul_nonneg (pow_nonneg (by norm_num) _) fixed0)) (pow_nonneg H0.le _)) (mul_nonneg stage0 (pow_nonneg H0.le 4))).trans_eq ?_
    unfold raw
    rw [show d+2+217=d+219 by omega,pow_add H d 219,pow_add H d 227]
    ring
  unfold reservedMass
  exact (add_le_add ((mul_le_mul_of_nonneg_left (both 0) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right z raw0)) (both _)).trans_eq (by unfold raw hardCost boxCost;ring)

end YM.Integration.WilsonEmittedSignedTariff
end
