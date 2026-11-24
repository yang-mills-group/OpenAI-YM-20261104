import YM.Integration.WilsonOriginalObservedRoseVaneCaliber
import YM.Integration.WilsonMaxwellThermometerNominatedSecant

/-! Cofactors of the complete connected Rose share the fourteen engineering powers among their disjoint factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseSevenScale
open Finset WilsonPositionThermometerConnected WilsonMaxwellThermometerNominatedSecant
open WilsonOriginalObservedRoseMeshHeight (height)
open WilsonOriginalObservedRoseVanePurse (ages)
open scoped Classical BigOperators
local notation "Faces" => Finset (Fin 3)

def plant (u:ℝ)(p:Faces→ℂ)(s:Faces):ℂ:=(u:ℂ)^(height ages s)*p s

private theorem graded (u:ℝ)(p:Faces→ℂ):value (plant u p)=(u:ℂ)^14*value p:=by
  have all:height ages (univ:Faces)=14:=by decide
  have ab:height ages ({0,1}:Faces)=10:=by decide
  have ac:height ages ({0,2}:Faces)=10:=by decide
  have bc:height ages ({1,2}:Faces)=8:=by decide
  have a:height ages ({0}:Faces)=6:=by decide
  have b:height ages ({1}:Faces)=4:=by decide
  have c:height ages ({2}:Faces)=4:=by decide
  simp only [value,plant,all,ab,ac,bc,a,b,c]
  ring

private theorem blank (p q:Faces→ℂ):bill p q ∅=0:=by
  unfold bill
  apply sum_eq_zero
  intro i _
  rw [if_neg (show ∅≠faceKey i from by fin_cases i <;> decide)]

private theorem seven (p q:Faces→ℂ){M τ:ℝ}(one:1≤M)(positive:0≤τ)
    (high:∀s:Faces,s.Nonempty → ‖p s‖≤M)(low:∀s:Faces,s.Nonempty → ‖q s‖≤M)
    (gap:∀s:Faces,s.Nonempty → ‖p s-q s‖≤M*τ):
    ‖value p-value q‖≤21*M^3*τ:=by
  have mp:0≤M:=zero_le_one.trans one
  have done:∑s:Faces,‖bill p q s‖≤7*(M+2*M^2):=by
    simpa only [max_self,max_eq_right one] using budget p q M M (fun s occupied _=>high s occupied)
      (fun i=>low {i} (singleton_nonempty _))
  calc ‖value p-value q‖=‖∑s:Faces,bill p q s*(p s-q s)‖:=congrArg norm (signed p q)
       _≤∑s:Faces,‖bill p q s‖*(M*τ):=by
         apply (norm_sum_le _ _).trans
         apply sum_le_sum
         intro s _
         by_cases occupied:s.Nonempty
         · rw [norm_mul];exact mul_le_mul_of_nonneg_left (gap s occupied) (norm_nonneg _)
         · have h:s=∅:=not_nonempty_iff_eq_empty.mp occupied
           simp only [h,blank,zero_mul,norm_zero]
           exact le_rfl
       _=(∑s:Faces,‖bill p q s‖)*(M*τ):=(sum_mul ..).symm
       _≤(7*(M+2*M^2))*(M*τ):=mul_le_mul_of_nonneg_right done (mul_nonneg mp positive)
       _≤21*M^3*τ:=by
         have h:M≤M^2:=by rw [pow_two];exact le_mul_of_one_le_right mp one
         calc (7*(M+2*M^2))*(M*τ)≤(7*(M^2+2*M^2))*(M*τ):=by gcongr
              _=21*M^3*τ:=by ring

private theorem converted {r z:ℝ} (rp:0≤r)(zp:0<z)(A B:ℕ)(s:Faces)(p:ℂ){τ:ℝ}
    (fee:r^(height ages s)*‖p‖≤z^(B+A*height ages s)*τ):
    ‖((r/z^A:ℝ):ℂ)^(height ages s)*p‖≤z^B*τ:=by
  let h:=height ages s
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg rp (pow_nonneg zp.le _)),div_pow]
  change r^h/(z^A)^h*‖p‖≤_
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos (pow_pos zp _) _)).mpr
  simpa only [pow_add,pow_mul,mul_right_comm,mul_assoc,mul_left_comm,mul_comm] using fee

theorem original (p q:Faces→ℂ){r z τ:ℝ}(rp:0≤r)(one:1≤z)(positive:0≤τ)(A B:ℕ)
    (high:∀s:Faces,s.Nonempty → r^(height ages s)*‖p s‖≤z^(B+A*height ages s))
    (low:∀s:Faces,s.Nonempty → r^(height ages s)*‖q s‖≤z^(B+A*height ages s))
    (delta:∀s:Faces,s.Nonempty → r^(height ages s)*‖p s-q s‖≤z^(B+A*height ages s)*τ):
    r^14*‖value p-value q‖≤21*z^(3*B+A*14)*τ:=by
  let u:=r/z^A
  have zp:0<z:=zero_lt_one.trans_le one
  have up:0≤u:=div_nonneg rp (pow_nonneg zp.le _)
  have face (f:Faces→ℂ)(paid:∀s:Faces,s.Nonempty → r^(height ages s)*‖f s‖≤z^(B+A*height ages s))
      (s:Faces)(hs:s.Nonempty):‖plant u f s‖≤z^B:=by
    simpa only [plant,u,mul_one] using converted rp zp A B s (f s) (τ:=1) (by simpa only [mul_one] using paid s hs)
  have jump(s:Faces)(hs:s.Nonempty):‖plant u p s-plant u q s‖≤z^B*τ:=by
    rw [plant,plant,←mul_sub]
    exact converted rp zp A B s _ (delta s hs)
  have cash:=seven (plant u p) (plant u q) (one_le_pow₀ one) positive (face p high) (face q low) jump
  rw [graded,graded,←mul_sub,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg up] at cash
  have unit:(z^A)^14*u^14=r^14:=by
    rw [←mul_pow]
    congr 1
    dsimp only [u]
    field_simp
  calc r^14*‖value p-value q‖=(z^A)^14*(u^14*‖value p-value q‖):=by rw [←mul_assoc,unit]
       _≤(z^A)^14*(21*(z^B)^3*τ):=mul_le_mul_of_nonneg_left cash (pow_nonneg (pow_nonneg zp.le _) _)
       _=21*z^(3*B+A*14)*τ:=by rw [pow_add,Nat.mul_comm 3 B,pow_mul,pow_mul];ring

end YM.Integration.WilsonOriginalObservedRoseSevenScale
end
