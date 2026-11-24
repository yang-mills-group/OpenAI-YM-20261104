import YM.MS.RayLimit
import YM.MS.LogTime
/-!
  Two-sided bounds for a homogeneous dimension on *all* logarithmic times force
  exact polynomial form of any constant-in-time coefficient.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Filter Set Finset Function MS.Plane Real
open scoped ContDiff Topology
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {u:ℝ} {g:E→F} {m k:ℕ} {i:ℤ}
lemma law_smul (hf:ContDiff ℝ ∞ g)(he:∀ p:E, ‖iteratedFDeriv ℝ (k+1) g p‖=0)(h:∀ m<k, ‖iteratedFDeriv ℝ m g 0‖=0)(z:ℝ)(x:E): g (z•x)=z^k • g x:= by
    induction k generalizing F x with
    | zero=> simpa only [pow_zero,one_smul] using is_const_of_fderiv_eq_zero (hf.differentiable (by simp)) (fun p=> norm_eq_zero.mp ((norm_iteratedFDeriv_one g).symm.trans ( he p))) (z • x) x
    | succ j ih=>
       let U:=fderiv ℝ g
       have hI(p:E) : U (z•p)=z^j • U p:= ih (hf.fderiv_right (by exact_mod_cast le_top)) (fun p=> norm_iteratedFDeriv_fderiv.trans (he p)) (fun m hm=> norm_iteratedFDeriv_fderiv.trans (h _ (by omega))) p
       let K:=z • ContinuousLinearMap.id ℝ E
       let P p:=g (K p) - z^(j+1) • g p
       have hp(p:E): HasFDerivAt P (0:E→L[ℝ] F) p:= by
          convert! (( (hf.differentiable (by simp) (z • p)).hasFDerivAt.comp p (K.hasFDerivAt (x:=p)) ).sub ( (hf.differentiable (by simp) p).hasFDerivAt.const_smul (z^(j+1))) ) using 1
          ext q; change (0:F)=U (z•p) (z•q)-z^(j+1) • U p q; rw [hI,smul_apply,map_smul,smul_smul,pow_succ,sub_self]
       apply sub_eq_zero.mp; have h0:g 0=0:= norm_eq_zero.mp ( norm_iteratedFDeriv_zero.symm.trans ( h 0 (by omega)) ); exact (is_const_of_fderiv_eq_zero (fun p=>(hp p).differentiableAt) (fun p=>(hp p).fderiv) x 0).trans (by simp [P,h0,K])
abbrev Sharp (u:ℝ)(g:E→F)(i:ℤ): Prop:= ∀ k:ℕ, ∃ C:ℝ,0<C∧∃ m:ℕ,∀ (p:E)(t:ℝ), ‖iteratedFDeriv ℝ k g p‖ ≤ C* ((1+‖u‖+‖t‖)*(1+exp t*‖p‖))^m * exp ( t*( (k:ℝ)-(i:ℝ) ) )
namespace Sharp
lemma melt (hp:Sharp u g i)(ht:(k:ℤ)< i): ‖iteratedFDeriv ℝ k g 0‖=0:= by
    obtain ⟨C,hC,m,h⟩:=hp k; let A:=1+‖u‖; let a:ℝ:=i; let Q t:= C*A^m *LogTime.polyExp (a-k) m t; have hQ:Tendsto Q atTop (𝓝 0):= by simpa only [Q,mul_zero] using (LogTime.vanishes (b:=a-k) (sub_pos.mpr (by unfold a; exact_mod_cast ht)) m).const_mul (C*A^m)
    refine le_antisymm ( ge_of_tendsto hQ ?_ ) (norm_nonneg _); filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht; refine ( h 0 t ).trans ?_; rw [ norm_of_nonneg ht,norm_zero,mul_zero,add_zero,mul_one ]; unfold Q LogTime.polyExp; rw [show -(a-(k:ℝ))*t=t*( (k:ℝ)-(i:ℝ)) from (by unfold a; ring),← mul_assoc (C*_ ),mul_assoc C (A^m), ← mul_pow ]; unfold A; gcongr; nlinarith [norm_nonneg u]
lemma era (hp:Sharp u g i)(x:E)(hh:i<(k:ℤ)): ‖iteratedFDeriv ℝ k g x‖=0:= by
    obtain ⟨C,hC,m,h⟩:= hp k; let A:= (1+‖u‖)*(1+‖x‖); let a:ℝ:=i; let Q t:= C*A^m * LogTime.polyExp ((k:ℝ)-a) m t; have hQ:Tendsto Q atTop (𝓝 0):= by simpa only [Q,mul_zero] using (LogTime.vanishes (b:=(k:ℝ)-a) (sub_pos.mpr (by unfold a; exact_mod_cast hh)) m).const_mul (C*A^m)
    refine le_antisymm ( ge_of_tendsto hQ ?_ ) (norm_nonneg _); filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht; refine (h x (-t)).trans ?_; rw [ norm_neg,norm_of_nonneg ht ]; unfold Q LogTime.polyExp; rw [ show -((k:ℝ)-a)*t=(-t)*((k:ℝ)-(i:ℝ)) from (by unfold a; ring),←mul_assoc (C*_),mul_assoc C (A^m),← mul_pow ]; unfold A; rw [mul_right_comm ( 1+‖u‖ ) ]; gcongr
    · nlinarith [norm_nonneg u]
    exact mul_le_of_le_one_left (norm_nonneg _) (exp_le_one_iff.mpr (neg_nonpos.mpr ht)) -- simp maybe
lemma shape {f:E→ℂ}(hp:Sharp u f i)(h:ContDiff ℝ ∞ f): Shape f i:= by
    rcases lt_or_ge i 0 with ht|ht
    · rw [show f=0 from funext (fun p=> norm_eq_zero.mp ( norm_iteratedFDeriv_zero.symm.trans ( hp.era p (k:=0) (by omega) ) ))]; exact form_zero _
    lift i to ℕ using ht
    exact ⟨ h,fun p=>(by omega),fun p z=>(by rw [zpow_natCast]; exact law_smul h (fun x=> hp.era x (k:=i+1) (by omega)) (fun m h=> hp.melt (k:=m) (by omega)) p z) ⟩
end Sharp
end YM.FVA2.Extras
