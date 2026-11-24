import YM.Integration.WilsonMeasuredPublicEntranceCropRate
/-! A single before-cutoff allowance for the rooted crop and the time
spent at all of the actual trial opportunities. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCropClock
open WilsonThermometerMixedCollarSubpower WilsonMeasuredPublicEntranceCropRate
def span (H:ℝ):ℝ:=(1+Real.log H)*(scale H)^3
def limit (n p:ℕ)(C:ℝ):ℝ:=(n:ℝ)*2^n+((n:ℝ)+2)*C+p+1
def fee (n p t:ℕ)(C H:ℝ):ℝ:=n+1+C*span H+3*(depth n p H (C*span H):ℝ)+t*Real.log H
def capital (n p t:ℕ)(C:ℝ):ℝ:=n+1+C+3*limit n p C+t

theorem original (n p t:ℕ)(C H:ℝ)(cp:0 ≤ C)(one:1 ≤ H)(level:1 ≤ Real.log H):
    let size:=span H
    let D:=depth n p H (C*size)
    let V:=fee n p t C H
    1 ≤ V ∧ C*size ≤ V ∧
    (n:ℝ)*Real.exp (3*(D:ℝ))*H^t ≤ Real.exp V ∧
    ∀(f b:ℕ)(gap:ℝ),((f-b:ℕ):ℝ) ≤ gap*(1+Real.log H)^4 →
      ((f-b+Nat.ceil (2*V):ℕ):ℝ) ≤ (gap+2*capital n p t C+1)*(1+Real.log H)^4:=by
  intro size D V
  have logp:0<Real.log H:=by linarith
  have pos:=zero_lt_one.trans_le one
  have on:1 ≤ 1+Real.log H:=by linarith
  have room:1 ≤  scale H:=by unfold scale;linarith only [le_max_left 0 (Real.log (Real.log H))]
  have sc: scale H ≤ 1+Real.log H:=by
    unfold scale
    exact add_le_add_right (max_le logp.le (Real.log_le_self logp.le)) _
  have size₀:0 ≤ size:=mul_nonneg (zero_le_one.trans on) (pow_nonneg (zero_le_one.trans room) _)
  have size₁:size ≤ (1+Real.log H)^4:=by
    change (1+Real.log H)*(scale H)^3 ≤ _
    rw [pow_succ' (1+Real.log H) 3]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans room) sc _) (zero_le_one.trans on)
  have cc:=mul_nonneg cp size₀
  have tt:=mul_nonneg (Nat.cast_nonneg t:0 ≤ (t:ℝ)) logp.le
  have floor:1 ≤ (1+Real.log H)^4:=one_le_pow₀ on
  have log_fit:Real.log H ≤ (1+Real.log H)^4:=by
    have z:1+Real.log H ≤ (1+Real.log H)^4:= by
      simpa only [pow_one] using pow_le_pow_right₀ on (by decide : 1 ≤ 4)
    linarith only [z]
  have stamped:(D:ℝ) ≤ limit n p C*size:=calendar n p H C one cp
  have lim:0 ≤ limit n p C:=by unfold limit;positivity
  have upper:=stamped.trans (mul_le_mul_of_nonneg_left size₁ lim)
  have first:=le_mul_of_one_le_right (show 0 ≤ (n:ℝ)+1 by positivity) floor
  have second:=mul_le_mul_of_nonneg_left size₁ cp
  have last:=mul_le_mul_of_nonneg_left log_fit (Nat.cast_nonneg t:0 ≤ (t:ℝ))
  have total:V ≤ capital n p t C*(1+Real.log H)^4:=by
    change (n:ℝ)+1+C*size+3*(D:ℝ)+(t:ℝ)*Real.log H ≤ _
    unfold capital
    linarith only [first,second,upper,last]
  have expensive:1 ≤ V:=by
    change 1 ≤ (n:ℝ)+1+C*size+3*(D:ℝ)+(t:ℝ)*Real.log H
    linarith only [cc,tt,(Nat.cast_nonneg D:0 ≤ (D:ℝ)),(Nat.cast_nonneg n:0 ≤ (n:ℝ))]
  have covers:C*size ≤ V:=by
    change C*size ≤ (n:ℝ)+1+C*size+3*(D:ℝ)+(t:ℝ)*Real.log H
    linarith only [tt,(Nat.cast_nonneg D:0 ≤ (D:ℝ)),(Nat.cast_nonneg n:0 ≤ (n:ℝ))]
  refine ⟨expensive,covers,?_,?_⟩
  · have people:(n:ℝ) ≤ Real.exp ((n:ℝ)+1+C*size):=by
      have base:=(Real.add_one_le_exp ((n:ℝ)+1+C*size))
      linarith
    calc (n:ℝ)*Real.exp (3*(D:ℝ))*H^t  ≤ 
        Real.exp ((n:ℝ)+1+C*size)*Real.exp (3*(D:ℝ))*H^t:=by gcongr
         _ = Real.exp V:=by
           change _=Real.exp ((n:ℝ)+1+C*size+3*(D:ℝ)+t*Real.log H)
           rw [Real.exp_add ((n:ℝ)+1+C*size+3*(D:ℝ)) ((t:ℝ)*Real.log H),Real.exp_nat_mul,Real.exp_log pos,
             Real.exp_add ((n:ℝ)+1+C*size) (3*(D:ℝ))]
  · intro f b gap bought
    have ceil:=(Nat.ceil_lt_add_one (show 0 ≤ 2*V by linarith)).le
    push_cast
    linarith only [bought,total,ceil,floor]

end YM.Integration.WilsonMeasuredPublicEntranceCropClock
end
