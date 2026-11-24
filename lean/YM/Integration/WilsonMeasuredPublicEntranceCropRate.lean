import YM.Integration.WilsonMeasuredPublicEntrancePeerWindow
import YM.Integration.WilsonMeasuredPublicEntranceCheapOrder
/-! Uniform restoration of the discarded regular tails when the occupied
trial and its true finite collection of spectators share their pre-test cap. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCropRate
open Filter Pert.Asymptotics WilsonMeasuredPublicEntranceCheapOrder WilsonThermometerMixedCollarSubpower
open scoped Classical BigOperators
variable {V:Type*}

private theorem prod_cap (a:V→ℝ){S:ℝ}(pos:∀v,0≤a v)(cap:∀v,a v≤S)(vs:List V):
    0≤(vs.map a).prod ∧ (vs.map a).prod≤S^vs.length:=by
  induction vs with
  | nil=>simp
  | cons v vs ih=>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ']
    exact ⟨mul_nonneg (pos v) ih.1,mul_le_mul (cap v) ih.2 ih.1 ((pos v).trans (cap v))⟩

theorem route_cap (a b δ:V→ℝ){S E:ℝ}(sp:1≤S)(ep:0≤E)
    (ap:∀v,0≤a v)(bp:∀v,0≤b v)(dp:∀v,0≤δ v)(ac:∀v,a v≤S)(bc:∀v,b v≤S)(dc:∀v,δ v≤E)
    (vs:List V):0≤route a b δ vs ∧ route a b δ vs≤(vs.length:ℝ)*S^vs.length*E:=by
  induction vs with
  | nil=>simp [route]
  | cons v vs ih=>
    have products:=prod_cap a ap ac vs
    have term:=mul_le_mul (dc v) products.2 products.1 ep
    have next:=mul_le_mul (bc v) ih.2 ih.1 (zero_le_one.trans sp)
    have piece:=le_mul_of_one_le_left (mul_nonneg (pow_nonneg (zero_le_one.trans sp) vs.length) ep) sp
    refine ⟨add_nonneg (mul_nonneg (dp v) products.1) (mul_nonneg (bp v) ih.1),?_⟩
    simp only [route,List.length_cons,Nat.cast_add,Nat.cast_one,pow_succ']
    exact (add_le_add term next).trans (by nlinarith only [piece])

def depth (n p:ℕ)(H U:ℝ):ℕ:=Nat.ceil ((n:ℝ)*2^n+((n:ℝ)+2)*U+p*Real.log H)

theorem original (n p:ℕ)(H U:ℝ)(hH:1≤H)(up:0≤U)(D:ℕ)
    (enough:depth n p H U≤D) (a δ:V→ℝ)(M:ℝ)(ap:∀v,0≤a v)(dp:∀v,0≤δ v)(ac:∀v,a v≤Real.exp U)
    (dc:∀v,δ v≤Real.exp (-(D:ℝ))*Real.exp U)(mc:M≤Real.exp U)(vs:List V)(size:vs.length≤n):
    M*route a (fun v=>a v+δ v) δ vs≤(H^p)⁻¹:=by
  let K:ℝ:=(n:ℝ)*2^n
  let S:=Real.exp U
  let E:=Real.exp (-(D:ℝ))*S
  have width:1≤S:=Real.one_le_exp_iff.mpr up
  have e0:0≤E:=mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have inner:E≤S:=mul_le_of_le_one_left (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (by simp))
  have numeric:=route_cap a (fun v=>a v+δ v) δ (S:=2*S) (E:=E) (by linarith) e0
    ap (fun v=>add_nonneg (ap v) (dp v)) dp (fun v=>(ac v).trans (by linarith))
    (fun v=>by linarith only [ac v,(dc v).trans inner]) dc vs
  have collect :M*route a (fun v=>a v+δ v) δ vs≤S*((n:ℝ)*(2*S)^n*E):=by
    apply (mul_le_mul mc numeric.2 numeric.1 (Real.exp_nonneg _)).trans
    gcongr
    exact one_le_mul_of_one_le_of_one_le (by norm_num) width
  have paid:K+((n:ℝ)+2)*U+p*Real.log H ≤(D:ℝ):=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr enough)
  calc
    _≤S*((n:ℝ)*(2*S)^n*E):=collect
    _=K*Real.exp (((n:ℝ)+2)*U-(D:ℝ)):=by
      dsimp only [K,S,E];rw [mul_pow,←Real.exp_nat_mul]
      have eq:((n:ℝ)+2)*U-(D:ℝ)=U+(n:ℝ)*U+(-(D:ℝ)+U):=by ring
      rw [eq,Real.exp_add,Real.exp_add,Real.exp_add];ring
    _≤Real.exp K*Real.exp (((n:ℝ)+2)*U-(D:ℝ)):=mul_le_mul_of_nonneg_right ((by linarith : K≤K+1).trans (Real.add_one_le_exp K)) (Real.exp_nonneg _)
    _=Real.exp (K+((n:ℝ)+2)*U-(D:ℝ)):=by rw [←Real.exp_add];congr 1;ring
    _≤Real.exp (-((p:ℝ)*Real.log H)):=Real.exp_le_exp.mpr (by linarith only [paid])
    _=(H^p)⁻¹:=by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le hH)]

theorem calendar (n p:ℕ)(H C:ℝ)(hH:1≤H)(cp:0≤C):
    let V:ℝ:=(1+Real.log H)*(scale H)^3
    (depth n p H (C*V):ℝ)≤((n:ℝ)*2^n+((n:ℝ)+2)*C+p+1)*V:=by
  intro V
  have logp:=Real.log_nonneg hH
  have room:1 ≤ scale H:=by dsimp [scale];linarith only [le_max_left 0 (Real.log (Real.log H))]
  have span:1+Real.log H≤V:=le_mul_of_one_le_right (by linarith) (one_le_pow₀ room)
  have one:1≤V:=by linarith
  have large:=mul_le_mul_of_nonneg_left one (show 0≤(n:ℝ)*2^n by positivity)
  have limit:=mul_le_mul_of_nonneg_left ((by linarith only [logp]:Real.log H≤1+Real.log H).trans span)
    (Nat.cast_nonneg p : 0≤(p:ℝ))
  have vpos:=zero_le_one.trans one
  dsimp only [depth]
  have upper:=Nat.ceil_lt_add_one (show 0≤(n:ℝ)*2^n+((n:ℝ)+2)*(C*V)+p*Real.log H by positivity)
  nlinarith only [upper,limit,large,one]

end YM.Integration.WilsonMeasuredPublicEntranceCropRate
end
