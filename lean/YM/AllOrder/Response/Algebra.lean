import YM.AllOrder.Laplace.Tilt
import YM.X.Gauss.Hook
/-!
# Same regulator formal series algebra. Coarse log scaling jets & exponent

Keep terms at EACH degree; no phase arrays read. Finite convolution
recursion (same as ordinary PowerSeries coefficients). Real scalars now;
complex/sources later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension.Series
open scoped Topology ContDiff Classical
variable {f F:ℝ→ℝ}{n:ℕ}
abbrev Tape:= Word ℝ
abbrev xpow (B:Tape) (k:ℕ):= Tested.term ((PowerSeries.mk B)^k)
lemma power {f':Tape}:  ∀ k, xpow f' (k+1)=plus (xpow f' k) f':= by
   intro k; unfold plus Tested.conv xpow; rw [show PowerSeries.mk (Tested.term _ : Tape)= _ from ?_,pow_succ];
   ext n; simp only [Tested.term,PowerSeries.coeff_mk]
lemma power_zero (a:Tape): xpow a 0=just 1:= by unfold xpow; rw [pow_zero]; exact funext PowerSeries.coeff_one
lemma plus_sum (a b:Tape)(i:ℕ): plus a b i=∑ j∈ Finset.antidiagonal i, a j.1*b j.2:=by simp [plus,Tested.conv,Tested.term,PowerSeries.coeff_mul]
lemma pow_le {f:Tape}(hf:f 0=0):∀ i n,n < i→ xpow f i n=0 := by
   intro i; induction i with
   | zero=> omega
   | succ i ih=>
      intro j hj; rw [power,plus_sum]; refine Finset.sum_eq_zero fun k hk=>?_ ; have hk:= Finset.mem_antidiagonal.mp hk; by_cases h:k.2=0
      · rw [h,hf,mul_zero]
      rw [ih k.1 (by omega),zero_mul]
lemma exact_sum {I:Type} {F:I→ℝ→ℝ}{a:I→Tape}(s:Finset I)(he:∀ i∈s,Act n (F i) (a i)): Act n (∑ i∈s,F i) (∑ i∈s,a i):= by
   induction s using Finset.induction_on with
   | empty => simp only [Finset.sum_empty]; exact ((Act.static (n:=n) (0:ℝ)).repairs (by intro i hi;simp [just]))
   | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (he _ (mem_insert_self ..)).add (ih (fun a h=> he _ (mem_insert_of_mem h)))
lemma exact_power {a:Tape}(hf:Act n f a) (k:ℕ):Act n (f^k) (xpow a k):=by induction k with
  | zero=>rw [power_zero,pow_zero]; exact Act.static _
  | succ k ih=> rw [power,pow_succ]; exact exact_prod ih hf

/-- truncated composition at zero when inner tape is light -/
def onward (a b:Tape)(n:ℕ):= (∑ k∈Finset.range (n+1),a k • xpow b k)
lemma run_frame {c:Tape}(he:light c)(hg:ContDiffAt ℝ ω F 0) {m:ℕ}(hm:m≤n) : run F c m= onward (someJ F) c n m:= by
   let b:=delay c n; have ht:= Act.swell c (show n ≤ n from le_rfl); have hb:b 0=0:=ht.zero.trans he
   let a:=someJ F; let g t:= delay a n t; have hx:Act n g a:= Act.swell a le_rfl
   have h:= ht.dial (eo_Act _ hg) he; have hp: Act n (g ∘ b) (ren c a):= ht.dial hx he
   have ht': Act n (F ∘ b) (run F c):=ht.transit (he.symm ▸ hg)
   rw [ht'.trans_at h hm,←hp.writes _ hm]
   rw [show g ∘ b=∑ i∈Finset.range (n+1),a i • b^i from funext (fun x=> by unfold Function.comp g delay; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply, Pi.pow_apply,smul_eq_mul,mul_comm (a _)] )]; exact (exact_sum (Finset.range (n+1)) (fun i _=> (exact_power ht i).smul (a i))).writes _ hm
lemma exp_pay {c:Tape}(h: light c){m:ℕ}(hm:m≤n): expS c m=onward (fun i=>(i.factorial:ℝ)⁻¹) c n m:= by
 have ht (i:ℕ) : iteratedDeriv i Real.exp=Real.exp:= by simpa using! iteratedDeriv_exp_const_mul i 1
 rw [expS,run_frame h Real.contDiff_exp.contDiffAt hm, show someJ Real.exp = (fun i : ℕ => (i.factorial:ℝ)⁻¹) from funext (fun i=> by simp [someJ,ht])]

lemma plus_ge (a b:Tape) : plus a b 0=a 0*b 0:= by simp [plus,Tested.conv,Tested.term,PowerSeries.coeff_zero_eq_constantCoeff_apply]
lemma exp_add (a b:Tape): expS (a+b)=plus (expS a) (expS b):= by
 funext k; have ha:=Act.swell a (show k ≤ k from le_rfl); have hb:=Act.swell b (show k ≤ k from le_rfl)
 exact ((ha.add hb).transit (m:=Real.exp) Real.contDiff_exp.contDiffAt).trans_at (by have hh:= exact_prod (ha.transit (m:=Real.exp) Real.contDiff_exp.contDiffAt) (hb.transit (m:=Real.exp) Real.contDiff_exp.contDiffAt); rw [show _ from (show Real.exp ∘ (delay a k+delay b k)= _ from funext (fun i=> (Real.exp_add (delay a k i) (delay b k i))))]; exact hh) le_rfl -- target unresolved from `show _`
lemma log_pay {a:Tape}(h:a 0=1){k:ℕ}(hk:k≤n): logS a k=onward (someJ (fun x:ℝ=> Real.log (x+1))) (a-just 1) n k:= by
 let d:=a-just 1; have hd: light d:= by simp [d,h,just,light]
 let T:= fun x:ℝ=> Real.log (x+1)
 have hT:ContDiffAt ℝ ω T 0:= ( (show ContDiffAt ℝ ω (fun x:ℝ=>x) 0 from contDiffAt_id).add contDiffAt_const).log (by norm_num)
 rw [← run_frame hd hT hk]; have hp:=Act.swell d (show n ≤ n from le_rfl); have he:= hp.add (Act.static (n:=n) (1:ℝ));
 have hS: Act n (T ∘ delay d n) (logS a):= by
    have hz:d+just 1=a:=sub_add_cancel ..; rw [hz] at he; exact he.transit (m:=Real.log) (by rw [h]; exact Real.contDiffAt_log.mpr one_ne_zero)
 exact hS.trans_at (hp.transit ((show d 0=0 from hd).symm ▸ hT)) hk
end YM.AllOrder.Response
