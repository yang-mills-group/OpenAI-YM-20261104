import YM.Integration.WilsonMeasuredPrimaryTariff

/-! The original projection only sees the fixed section footprint at its
actual output origin. Its expense grows with the section reader and the
purchased derivative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPrimaryWindow
open Wilson Lattice RG Labels Source Push.Local

def bound {G:Gauge} {d:ℕ} {F:Frame G d} (A:Hol G) (S:SectionData F) : ℝ :=
  let K:=Real.exp (102*(atomTiles S:ℝ))*(1+readPrice A F)
  16*(1+K+Real.exp (100*(atomTiles S:ℝ))*K)

theorem budget {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} (p:BudgetPoint) (A:Hol G)
    (S:SectionData F) (o:Site n) (w:ℝ) (hw:0≤w) (fixed:p.supportExponent=100) :
    let y:=(1+w)^2*(p.order.factorial:ℝ)
    WilsonMeasuredPrimaryTariff.allowance p A S o w ≤ bound A S*y ∧
      WilsonMeasuredPrimaryTariff.cost p A S o w ≤ bound A S*y := by
  intro y
  let t:=1+w
  let f:ℝ:=p.order.factorial
  let z:=factor A S p.supportExponent w*f
  let k:=Real.exp (102*(atomTiles S:ℝ))*(1+readPrice A F)
  let e:=Real.exp (100*(atomTiles S:ℝ))
  have rp:0≤readPrice A F:=(by norm_num : (0:ℝ)≤1).trans (readPrice_pos A F)
  have f1:1≤f:=by
    change (1:ℝ)≤(p.order.factorial:ℝ)
    exact_mod_cast (show 1≤p.order.factorial from Nat.factorial_pos _)
  have f0:0≤f:=zero_le_one.trans f1
  have t1:1≤t:=by dsimp [t];linarith
  have tpos:0≤t:=zero_le_one.trans t1
  have ts:t≤t^2:=by nlinarith [mul_nonneg tpos (sub_nonneg.mpr t1)]
  have fy:f≤y:=by
    change f≤t^2*f
    exact (show f=1*f by ring).le.trans (mul_le_mul_of_nonneg_right (t1.trans ts) f0)
  have k0:0≤k:=by dsimp [k];positivity
  have exp0:0≤e:=(Real.exp_pos _).le
  have z0:0≤z:=by
    dsimp [z,factor,atomPrice]
    positivity
  have pre:z≤k*t*f:=by
    apply mul_le_mul_of_nonneg_right _ f0
    rw [fixed]
    change Real.exp ((100+2)*(atomTiles S:ℝ))*(1+(1+w)*readPrice A F)≤k*t
    dsimp [k,t]
    rw [show (100+2:ℝ)=102 by norm_num,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith
  have zy:z≤k*y:=by
    refine pre.trans ?_
    change k*t*f≤k*(t^2*f)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ts f0) k0
  have wz:w*z ≤ k*y:=by
    calc w*z ≤ t*(k*t*f) := mul_le_mul (by dsimp [t];linarith) pre z0 tpos
      _ = k*y := by change _=k*(t^2*f);ring
  have shell:Real.exp (p.supportExponent*(coverNumber p.B (S.footprint o):ℝ)) ≤ e:=by
    rw [fixed]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact_mod_cast atomTiles_price S p o
  have outer:p.mass (S.footprint o) (w*z)≤e*(k*y):=
    mul_le_mul shell wz (mul_nonneg hw z0) exp0
  let u:=(1+k+e*k)*y
  have u0:0≤u:=by dsimp [u,y];positivity
  have ek:0≤e*(k*y):=mul_nonneg exp0 (mul_nonneg k0 (f0.trans fy))
  have one:f+z+p.mass (S.footprint o) (w*z)≤u:=by dsimp [u];linarith only [fy,zy,outer]
  have two:2*(1+z)≤2*u:=by dsimp [u];linarith only [f1.trans fy,zy,ek]
  change 4*(f+z+p.mass (S.footprint o) (w*z))≤16*(1+k+e*k)*y ∧
    8*max (f+z+p.mass (S.footprint o) (w*z)) (2*(1+z))≤16*(1+k+e*k)*y
  have all:max (f+z+p.mass (S.footprint o) (w*z)) (2*(1+z))≤2*u:=
    max_le (one.trans (by linarith)) two
  constructor
  · nlinarith only [one,u0]
  · nlinarith only [all]

end YM.Integration.WilsonMeasuredPrimaryWindow
end
