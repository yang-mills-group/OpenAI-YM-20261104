import YM.Integration.WilsonReflectedOriginalPrefixMesh

/-! Summing a first true connected support across the entire finer Wilson clock. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOriginalPrefixTariff
open Finset Lattice Wilson RG WilsonReflectedOriginalPrefixMesh
open scoped BigOperators
variable {G:Gauge}(C:Calendar G)

def width (k:ℕ):ℝ:=1+|G.slopeConstant|+Real.log (C.hatBeta k)
def blockBill (i:ℕ):ℝ:=8*(4*(⌈(Real.log (C.hatBeta i))^2⌉₊:ℝ)+2)
def reserve (K a b q m:ℕ)(A:ℝ):ℝ:=
  A*(width C K)^(m+1)*(((m:ℝ)+1)^(m+1))*((a:ℝ)+b+q+1)

private theorem polynomial (m:ℕ)(v:ℝ)(hv:0≤v):
    (1+v)^(m+1) ≤ ((m:ℝ)+1)^(m+1)*Real.exp v:=by
  let l:ℝ:=m+1
  have lp:0<l:=by dsimp [l];positivity
  have lb:1≤l:=by dsimp [l];linarith only [Nat.cast_nonneg (α:=ℝ) m]
  have ordinary:1+v≤l*Real.exp (v/l):=by
    have h:=mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v/l)) lp.le
    have clean:v/l*l=v:=div_mul_cancel₀ v lp.ne'
    nlinarith only [h,clean,lb]
  have powered:=pow_le_pow_left₀ (by positivity:0≤1+v) ordinary (m+1)
  rw [mul_pow,←Real.exp_nat_mul,Nat.cast_add_one] at powered
  have same:((m:ℝ)+1)*(v/l)=v:=by change l*(v/l)=v;rw [mul_comm,div_mul_cancel₀ _ lp.ne']
  rwa [same] at powered

private theorem logHeight (K t:ℕ)(beg:1≤C.hatBeta K)(endp:1≤C.hatBeta (K+t)):
    let v:=Real.log ((C.schedule.steps K t).val:ℝ)
    let l:=width C K
    1≤l ∧ 0≤v ∧ Real.log (C.hatBeta K)≤l ∧ Real.log (C.hatBeta (K+t))≤l*(1+v):=by
  intro v l
  have source:0≤Real.log (C.hatBeta K):=Real.log_nonneg beg
  have vpos:0≤v:=Real.log_nonneg (by exact_mod_cast (C.schedule.steps K t).property)
  have lpos:1≤l:=by dsimp [l,width];linarith only [source,abs_nonneg G.slopeConstant]
  have lbase:Real.log (C.hatBeta K)≤l:=by dsimp [l,width];linarith only [abs_nonneg G.slopeConstant]
  have lrate:|G.slopeConstant|≤l:=by dsimp [l,width];linarith only [source]
  refine ⟨lpos,vpos,lbase,?_⟩
  have before:=WilsonReflectedOriginalPrefixMesh.height C K t
  have form:C.hatBeta (K+t)≤C.hatBeta K*Real.exp (|G.slopeConstant| *v):=by
    rw [before]
    have relax:G.slopeConstant*v≤|G.slopeConstant| *v:=mul_le_mul_of_nonneg_right (le_abs_self _) vpos
    have cost:=mul_le_mul_of_nonneg_left (Real.add_one_le_exp (|G.slopeConstant| *v)) (zero_le_one.trans beg)
    have wz:0≤|G.slopeConstant| *v:=mul_nonneg (abs_nonneg _) vpos
    nlinarith only [relax,cost,mul_le_mul_of_nonneg_right beg wz]
  have lg:=Real.log_le_log (zero_lt_one.trans_le endp) form
  rw [Real.log_mul (zero_lt_one.trans_le beg).ne' (Real.exp_pos _).ne',Real.log_exp] at lg
  nlinarith only [lg,lbase,mul_le_mul_of_nonneg_right lrate vpos]

theorem block (K t:ℕ)(beg:1≤C.hatBeta K)(endp:1≤C.hatBeta (K+t)):
    blockBill C (K+t) ≤ 80*(width C K)^2*(1+Real.log ((C.schedule.steps K t).val:ℝ))^2:=by
  obtain ⟨lo,vz,_,hi⟩:=logHeight C K t beg endp
  have squared:=pow_le_pow_left₀ (Real.log_nonneg endp) hi 2
  have young:=Nat.ceil_lt_add_one (sq_nonneg (Real.log (C.hatBeta (K+t))))
  have one:1≤(width C K)*(1+Real.log ((C.schedule.steps K t).val:ℝ)):=by
    simpa only [one_mul] using mul_le_mul lo (by linarith only [vz]:1≤1+Real.log ((C.schedule.steps K t).val:ℝ)) zero_le_one (zero_le_one.trans lo)
  have unit:=pow_le_pow_left₀ (by norm_num:0≤(1:ℝ)) one 2
  dsimp only [blockBill]
  nlinarith only [squared,young,unit]

theorem salary {K t a b q m:ℕ}{A D strip:ℝ}(Ap:0<A)(sp:0<strip)
    (beg:1≤C.hatBeta K)(endp:1≤C.hatBeta (K+t))
    (room:strip≤A*(width C K)^m*(1+Real.log ((C.schedule.steps K t).val:ℝ))^m)
    (span:reserve C K a b q m A*((C.schedule.steps K t).val:ℝ) ≤ D):
    Real.exp (-(D/strip))*(C.hatBeta (K+t))^a*((C.schedule.steps K t).val:ℝ)^b ≤
      (C.hatBeta K)^(-(q:ℤ))*((1/2:ℝ)^t):=by
  let l:=width C K
  let T:ℝ:=(C.schedule.steps K t).val
  let v:=Real.log T
  let c:ℝ:=a+b+q+1
  obtain ⟨hl,hv,hk,hi⟩:=logHeight C K t beg endp
  have lp:0<l:=zero_lt_one.trans_le hl
  have Tp:0<T:=by dsimp only [T];exact_mod_cast (C.schedule.steps K t).property
  have cc:0≤c:=by dsimp [c];positivity
  have vplus:0≤1+v:=by linarith only [hv]
  have lin:l*(1+v) ≥ v:=by nlinarith only [hl,mul_le_mul_of_nonneg_right hl vplus]
  have key:c*l*(1+v) ≤ D/strip:=by
    apply (le_div_iff₀ sp).mpr
    have first:=mul_le_mul_of_nonneg_left room (mul_nonneg (mul_nonneg cc lp.le) vplus)
    apply first.trans
    have pol:=polynomial m v hv
    rw [Real.exp_log Tp] at pol
    have mult:=mul_le_mul_of_nonneg_left pol (mul_nonneg (mul_nonneg Ap.le (pow_nonneg lp.le (m+1))) cc)
    change _≤D
    apply le_trans _ span
    dsimp only [reserve]
    change c*l*(1+v)*(A*l^m*(1+v)^m) ≤ A*l^(m+1)*((m:ℝ)+1)^(m+1)*c*T
    calc _ = A*l^(m+1)*c*(1+v)^(m+1) := by ring
         _ ≤ _ := by nlinarith only [mult]
  have peak:Real.log (C.hatBeta K) ≤ l*(1+v):=by nlinarith only [hk,mul_nonneg lp.le hv]
  have logs:(a:ℝ)*Real.log (C.hatBeta (K+t))+((b:ℝ)+1)*v+(q:ℝ)*Real.log (C.hatBeta K) ≤ D/strip:=by
    dsimp only [c] at key
    nlinarith only [key,mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α:=ℝ) a),
      mul_le_mul_of_nonneg_left lin (by positivity:0≤(b:ℝ)+1),
      mul_le_mul_of_nonneg_left peak (Nat.cast_nonneg (α:=ℝ) q)]
  have net:=Real.exp_le_exp.mpr (by linarith only [logs]:
      -(D/strip)+(a:ℝ)*Real.log (C.hatBeta (K+t))+(b:ℝ)*v ≤ -((q:ℝ)*Real.log (C.hatBeta K))-v)
  simp only [Real.exp_add,Real.exp_sub,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le endp),
    Real.exp_log (zero_lt_one.trans_le beg),v,Real.exp_log Tp] at net
  have dy:(2:ℝ)^t ≤ T:=by dsimp only [T];exact_mod_cast WilsonReflectedOriginalPrefixMesh.dyadic C.schedule K t
  have dier:1/T≤(1/2:ℝ)^t:=by
    rw [one_div,one_div,inv_pow];exact inv_anti₀ (by positivity) dy
  rw [zpow_neg,zpow_natCast]
  rw [Real.exp_neg]
  apply net.trans
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left dier (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans beg) _))

end YM.Integration.WilsonReflectedOriginalPrefixTariff
