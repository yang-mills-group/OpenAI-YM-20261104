import YangMills.WilsonProof.NativeSupport.JointCashAdmission
import YangMills.WilsonProof.NativeSupport.JointInletBootstrap

/-! Polynomial purchases for an entire growing inlet, with the width,
canonical stencil and original global tariff fixed before perturbative
order is picked. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open scoped BigOperators
def priceDegree (W s:ℕ):ℕ:=16*W+s+64
def radiusDegree (W s ν:ℕ):ℕ:=2*priceDegree W s+W*ν+4

theorem calendar_capacity (W s₀:ℕ) {x μ s z c:ℝ} (heat:256 ≤ x)
    (m0:0 ≤ μ) (s0:0 ≤ s) (z0:0 ≤ z) (box0:0 ≤ c)
    (load:μ ≤ x^(4*W+2)) (sites:s ≤ x^13) (primitive:z ≤ x^(s₀+1)) (box:c ≤ x^13) :
    64*μ*c*x^2*(1+μ*s*(1+z)) ≤ x^(priceDegree W s₀) := by
  have x1:1 ≤ x := by linarith
  have x0:=zero_le_one.trans x1
  let a:=4*W+2
  let b:=s₀+1
  have fit:1+μ*s*(1+z) ≤ 3*x^(a+13+b) := by
    have za:1+z ≤ 2*x^b:=by linarith only [primitive,one_le_pow₀ (n:=b) x1]
    have cheap:μ*s*(1+z) ≤ x^a*x^13*(2*x^b) := by gcongr
    rw [pow_add,pow_add]
    have ample:1 ≤ x^a*x^13*x^b := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ x1) (one_le_pow₀ x1)) (one_le_pow₀ x1)
    linarith only [cheap,ample]
  calc
    _ ≤ 64*x^a*x^13*x^2*(3*x^(a+13+b)) := by gcongr
    _ = 192*x^(a+13+2+(a+13+b)) := by rw [pow_add,pow_add,pow_add];ring
    _ ≤ x*x^(a+13+2+(a+13+b)) := by gcongr;linarith
    _ = x^(a+13+2+(a+13+b)+1) := by rw [pow_succ];ring
    _ ≤ x^(priceDegree W s₀) := by
      apply pow_le_pow_right₀ x1
      dsimp only [a,b,priceDegree]
      omega

theorem calendar_bootstrap_fee (W s ν:ℕ) {x days block:ℝ} (x1:1 ≤ x) (width:2*(W:ℝ) ≤ x)
    (bd:0 ≤ block) (duration:days ≤ (W:ℝ)*x) (range_:block ≤ x^W) :
    2*days*block^ν*x^(2*priceDegree W s+1)*(x^(radiusDegree W s ν))⁻¹ ≤ 1 := by
  let b:=priceDegree W s
  have heat:=zero_le_one.trans x1
  have ample:2*days ≤ x^2 := by
    calc
      2*days ≤ 2*((W:ℝ)*x) := by gcongr
      _ = 2*(W:ℝ)*x := by ring
      _ ≤ x*x := mul_le_mul_of_nonneg_right width heat
      _ = x^2 := by ring
  have fit:block^ν ≤ x^(W*ν) := by rw [pow_mul];exact pow_le_pow_left₀ bd range_ _
  have p:0 < x^(radiusDegree W s ν) := pow_pos (zero_lt_one.trans_le x1) _
  rw [←div_eq_mul_inv,div_le_one p]
  calc
    _ ≤ x^2*x^(W*ν)*x^(2*b+1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg heat _)
      exact mul_le_mul ample fit (pow_nonneg bd _) (sq_nonneg x)
    _ = x^(2+W*ν+(2*b+1)) := by rw [pow_add x (2+W*ν) (2*b+1),pow_add x 2 (W*ν)]
    _ ≤ x^(radiusDegree W s ν) := by
      apply pow_le_pow_right₀ x1
      dsimp only [radiusDegree,b]
      omega

theorem calendar_radii (W s ν:ℕ) {x u:ℝ} (heat:2 ≤ x) (prev:u ≤ (x^(radiusDegree W s ν))⁻¹) :
    let k:=x^(priceDegree W s)
    let r:=(x^(radiusDegree W s ν))⁻¹
    let h:=r^2
    0 < h ∧ h ≤ 1 ∧ 1 ≤ oldRadius k u h ∧ 1 ≤ bornRadius k h ∧
      oldRadius k u h*u ≤ 1/k ∧ bornRadius k h*h=1/k ∧
      2/min (bornRadius k h) (oldRadius k u h^2) ≤ x^(2*priceDegree W s+1)*(u^2+h) := by
  intro k r h
  have x1:1 ≤ x:=by linarith
  have xp:=zero_lt_one.trans_le x1
  have r0:0 < r:=inv_pos.mpr (pow_pos xp _)
  have r1:r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ x1)
  have h0:0 < h:=sq_pos_of_pos r0
  have hr:h ≤ r := by dsimp only [h];nlinarith only [mul_nonneg r0.le (sub_nonneg.mpr r1)]
  have kk:1 ≤ k:=one_le_pow₀ x1
  have disk:k*max u h ≤ 1 := by
    apply (mul_le_mul_of_nonneg_left (max_le prev hr) (zero_le_one.trans kk)).trans
    change x^priceDegree W s*(x^radiusDegree W s ν)⁻¹ ≤ 1
    rw [←div_eq_mul_inv,div_le_one (pow_pos xp _)]
    apply pow_le_pow_right₀ x1
    dsimp only [radiusDegree]
    omega
  obtain ⟨oa,da,ou,dh,err⟩:=radius_price kk h0 (hr.trans r1) disk
  refine ⟨h0,hr.trans r1,oa,da,ou,dh,err.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (add_nonneg (sq_nonneg _) h0.le)
  dsimp only [k]
  rw [pow_succ x (2*priceDegree W s),Nat.mul_comm 2 (priceDegree W s),pow_mul x (priceDegree W s) 2]
  nlinarith only [mul_nonneg (sub_nonneg.mpr heat) (sq_nonneg (x^priceDegree W s))]

end YM.Integration.InletSusceptibility.Packet
