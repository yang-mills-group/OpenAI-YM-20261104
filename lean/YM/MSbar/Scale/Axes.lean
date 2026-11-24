import YM.MSbar.Scale.Rollout
/-! Ray-coordinate rollout homogeneity and linearity at fixed regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale.Flight
open Dim Symbol Function Set Filter Metric Complex MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {f g:Vec}{a:ℂ}{n i:ℕ} (hf:Great f)(hg:Great g)
include hf
include hg
lemma strip_plus : strip (f+g) = strip f+strip g := by
    funext x; rcases eq_or_ne x 0 with rfl|h
    · simp [strip,deriv_add (hf.1.differentiable (by simp) _) (hg.1.differentiable (by simp) _)]
    simp [strip,dslope_of_ne _ h,slope_def_module]; ring
omit hg
lemma strip_scale (c:ℂ): strip (c•f)=c • strip f:= by
    funext x; rcases eq_or_ne x 0 with rfl|h
    · simp only [strip, dslope_same,Pi.smul_apply]; exact deriv_const_mul c (hf.1.differentiable (by simp) _) -- defeq dslope_eq?
    simp [strip,dslope_of_ne _ h, slope_def_module]; ring
omit hf in
lemma slope_shift : Land (a-(↑(n+1 : ℕ):ℂ)) ↔ Land (a-1-n):= by push_cast; rw [← sub_add_eq_sub_sub,add_comm (1:ℂ)]
include hg
lemma plus (h:Land (a-n)): rollout n a (f+g)=rollout n a f+rollout n a g:=by
    induction n generalizing a f g with
    | zero=> replace h: Land a:= by simpa using h
             funext t; simp only [rollout,past,Pi.add_apply,mul_add]; exact integral_add (int hf h t) (int hg h t)
    | succ i ih=>rw [rollout,strip_plus hf hg,ih (strip_tame_ray hf) (strip_tame_ray hg) (slope_shift.mp h)]; funext x; simp [rollout,higher]; ring
omit hg
lemma scalar (h:Land (a-n))(c:ℂ): rollout n a (c•f)=c • rollout n a f:=by
    induction n generalizing a f with
    | zero=> funext t; simp_rw [rollout,past,Pi.smul_apply,smul_eq_mul,mul_left_comm _ c]; exact integral_const_mul ..
    | succ i ih=> rw [rollout,strip_scale hf c,ih (strip_tame_ray hf) (slope_shift.mp h)]; funext t; simp [rollout,higher]; ring
omit hf in
lemma ground (h:Land (a-n)): rollout n a 0=0:=by simpa using scalar (f:=0) (HasTemperateGrowth.const 0) h 0
-- scaling arguments & Euler operator
variable (t:ℝ)
def pull (t:ℝ)(f:Vec)(u:ℝ):= f (u*t)
lemma round : Great (pull t f) := hf.comp (show HasTemperateGrowth (fun u:ℝ=>u*t) by fun_prop)
lemma force : strip (pull t f)=(t:ℂ) • pull t (strip f):=by
    funext u; rcases eq_or_ne u 0 with rfl|hu
    · simp only [strip,dslope_same, Pi.smul_apply]; simpa only [smul_eq_mul,pull,zero_mul,dslope_same] using! (wider hf t 0).deriv
    apply smul_right_injective ℂ hu; dsimp only; rw [roll]; unfold pull; simp only [zero_mul,Pi.smul_apply,smul_eq_mul]; rw [show f _-f 0=(u*t) • strip f (u*t) from (roll f).symm]; simp; ring
lemma through : flight a (pull t f)=pull t (flight a f):=by funext s; unfold pull flight; rw [(wider hf t s).deriv]; push_cast; ring
lemma comm (ht:Land (a-n)): rollout n a (pull t f)= pull t (rollout n a f) := by
    induction n generalizing a f with
    | zero=> funext u; simp only [pull,rollout,past,mul_assoc]
    | succ i ih=> rw [rollout,force hf,scalar (round (strip_tame_ray hf) t) (slope_shift.mp ht),ih (strip_tame_ray hf) (slope_shift.mp ht)]; funext u; simp [pull,higher,rollout]; ring
-- E eigen, with sharp locality conclusions
lemma local_taylor (n:ℕ) (he: flight (n:ℂ) f=0) (t:ℝ): f t=(t:ℂ)^n*f 1 := by
    induction n generalizing f with
    | zero=> have ht:strip f=0:= (unique (n:=1) (show Approved ((↑(0:ℕ):ℂ)-1) (strip f) from (fun i hi=> by apply_fun Complex.re at hi; norm_num at hi; linarith [show (0:ℝ) ≤ ↑i by positivity])) (strip_tame_ray hf) (by rw [← zip hf,he,strip_zero]) (by norm_num [Land]))
             have heq(x:ℝ):f x=f 0:= sub_eq_zero.mp (by rw [← roll,ht]; simp); rw [heq t]; symm; simpa using heq 1
    | succ i ih=> have hx:f 0=0:= (mul_eq_zero.mp ((at_zero ↑(i+1:ℕ) f).symm.trans (congr_fun he 0))).resolve_left (by exact_mod_cast Nat.succ_ne_zero i)
                  have hh(x:ℝ): f x= (x:ℂ)* strip f x:= by rw [show (x:ℂ)* strip f x=f x-f 0 from roll _,hx,sub_zero]
                  rw [hh t,ih (strip_tame_ray hf) (by rw [show (i:ℂ)= ((↑(i+1:ℕ):ℂ)-1) by push_cast; ring,← zip hf,he,strip_zero]),hh 1]; push_cast; ring
end YM.MSbar.Scale.Flight
