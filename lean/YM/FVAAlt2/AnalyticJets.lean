import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import YM.FVAAlt2.FormExp
import YM.FVAAlt2.RawEval
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! Ring and exponential compatibility for the radial expansion of actual germs. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.AnalyticJets
open Finset Function Filter Topology Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam PertExtension.Series.Radial MS.Cylinder
open scoped ContDiff PowerSeries
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "C"=>PowerSeries.C (R:=ℂ)
local notation "cf"=>PowerSeries.coeff (R:=ℂ)
local notation "T"=>PowerSeries ℂ
variable (x:X)
lemma val_eq {f:X→ℝ}: Lam.fitR f x=Lam.raise (PowerSeries.mk fun n=> jet f n x):=rfl
lemma val_at (f:X→ℝ) (i:ℕ): cf i (fitR f x)= Complex.ofReal (jet f i x):= by rw [val_eq,cscale,PowerSeries.coeff_mk]

lemma chart_sum{B:Type}(s:Finset B)(f:B→X→ℂ)(h:∀ i∈s,Taylor.germ (f i)) : ChartC (∑ i∈s,f i) x = ∑ i∈s, ChartC (f i) x:= by
  classical
  induction s using Finset.induction with
  | empty=> simp_rw [Finset.sum_empty, show ChartC (0:X→ℂ) x=0 from (congrFun (chart_const (E:=X) 0) x).trans (map_zero _)]
  | insert i s hi ih=>
    have hd:=fun j hj=> h j (mem_insert_of_mem hj);
    have hu:ContDiffAt ℝ ω (∑ j∈s,f j) 0:=by rw [show (∑ j∈s,f j)=fun x=>∑ j∈s, f j x from funext fun _=>Finset.sum_apply ..]; exact ContDiffAt.sum hd
    rw [sum_insert hi,sum_insert hi]; exact (congrFun (chart_add ((h i (mem_insert_self ..)).of_le le_top) (hu.of_le le_top)) x).trans (congrArg (fun z:T=> _ + z) (ih hd)) -- change
lemma real_val {f:X→ℝ}(h:Taylor.germ f): fitR f x=ChartC (fun x:X=>(f x:ℂ)) x:= (chart_line (h.of_le le_top) x).symm
lemma valConst (c:ℝ): fitR (fun _:X=>c) x= C (c:ℂ):= (real_val x contDiffAt_const).trans (congrFun (chart_const (c:ℂ)) x)
lemma valMul{f g:X→ℝ}(h:Taylor.germ f)(he:Taylor.germ g): fitR (fun x=>f x*g x) x= fitR f x*fitR g x:= by rw [real_val x (h.mul he),real_val x h,real_val x he]; push_cast; exact congrFun (chart_mul (f:=fun x=>(f x:ℂ)) (g:=fun x=>(g x:ℂ)) ((Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=f) 0 h).of_le le_top) ((Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=g) 0 he).of_le le_top)) x
lemma valS {f:X→ℝ}(c:ℝ)(h:Taylor.germ f): fitR (fun x=>c*f x) x=(c:ℂ) • fitR f x:= by rw [valMul x (f:=fun _=>c) contDiffAt_const h,valConst]; ext; simp
lemma valSum{B:Type}(s:Finset B)(f:B→ X→ℝ)(h:∀ i∈s,Taylor.germ (f i)) : fitR (fun x=> ∑ i∈s,f i x) x=∑ i∈s,fitR (f i) x:= by
  rw [real_val x (ContDiffAt.sum h)]
  let g(i:B)(x:X):=(f i x:ℂ)
  have he:∑ i∈s,g i=fun x=> ((∑ i∈s,f i x :ℝ):ℂ):= by -- ascription
     funext x; simp [Finset.sum_apply,g,Complex.ofReal_sum]
  rw [← he,chart_sum x s g (fun i hi=>(Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=f i) 0 (h i hi)))]; exact sum_congr rfl fun i hi=> (real_val x (h i hi)).symm
lemma valPow{f:X→ℝ}(h:Taylor.germ f)(n:ℕ): fitR (fun y=> f y^n) x= fitR f x ^ n:= by
 induction n with| zero=> simp_rw [pow_zero]; rw [valConst]; simp| succ n ih=> simp_rw [pow_succ]; rw [valMul x (h.pow n) h, ih]
lemma valNeg{f:X→ℝ}(h:Taylor.germ f): fitR (fun y=> -f y) x= -fitR f x:= by simpa using valS x (-1) h
lemma valProd{B:Type}(s:Finset B)(f:B→ X→ℝ)(h:∀ i∈s,Taylor.germ (f i)) : fitR (fun x=> ∏ i∈s,f i x) x=∏ i∈s,fitR (f i) x:= by
 classical
 induction s using Finset.induction with
 | empty=> simp_rw [prod_empty]; rw [valConst]; simp
 | insert a s ha ih=>
   have he:= fun i hi=> h i (mem_insert_of_mem hi); simp_rw [Finset.prod_insert ha]; rw [valMul x (h a (mem_insert_self ..)) (contDiffAt_prod he), ih he]
lemma valGerm {f g:X→ℝ}(h:f=ᶠ[𝓝 0] g): fitR f x= fitR g x:= by ext n; rw [val_at,val_at]; unfold jet; rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]

def TaylorE(n:ℕ)(y:ℝ):ℝ:= ∑ i∈range (n+1),(i.factorial:ℝ)⁻¹*y^i
lemma TaylorE_s(n:ℕ): ContDiff ℝ ω (TaylorE n):=by unfold TaylorE; fun_prop
lemma expandExp{f:X→ℝ}(h:Taylor.germ f)(H:f 0=0)(i:ℕ): jet (Real.exp ∘ f) i x=jet (TaylorE i ∘ f) i x:=by
  have hs {b:ℝ→ℝ}(hs:ContDiff ℝ ω b): jet (b∘ f) i x=(i.factorial:ℝ)⁻¹* iteratedDeriv i (b ∘ fun t:ℝ=>f (t • x)) 0:= homogeneous_derivative _ _ _ ((hs.contDiffAt.comp 0 h).of_le le_top)
  let F(t:ℝ):=f (t • x); let L:=ContinuousLinearMap.toSpanSingleton ℝ x
  have hf:ContDiffAt ℝ ω F 0:= ContDiffAt.comp (f:=L) 0 (by rw [map_zero]; exact h) L.contDiff.contDiffAt
  have he{b:ℝ→ℝ}(hs:ContDiff ℝ ω b): iteratedDeriv i (b ∘ F) 0=∑ c : OrderedFinpartition i,(∏ j, iteratedDeriv (c.partSize j) F 0) • iteratedDeriv c.length b 0:= by rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hs.contDiffAt hf le_top]; simp [F,H]
  rw [hs Real.contDiff_exp, hs (TaylorE_s i), he (b:=Real.exp) Real.contDiff_exp, he (TaylorE_s i)]; apply congrArg _; apply sum_congr rfl; intro c _; congr 1
  let ε(k:ℕ)(y:ℝ):=(k.factorial:ℝ)⁻¹*y^k; have hc(k:ℕ): ContDiff ℝ ω (ε k):= by unfold ε; fun_prop
  unfold TaylorE; rw [ iteratedDeriv_fun_sum (f:=ε) (fun k _=> (hc k).contDiffAt.of_le le_top), Finset.sum_eq_single_of_mem c.length (by simp; exact c.length_le) ]
  · unfold ε; rw [iteratedDeriv_const_mul _ (by fun_prop),iteratedDeriv_fun_pow_zero]; have hh: (c.length.factorial:ℝ)≠0:= by positivity
    simpa [hh] using congrFun (iteratedDeriv_exp_const_mul c.length (1:ℝ)) 0
  intro k _ h; unfold ε; rw [iteratedDeriv_const_mul _ (by fun_prop),iteratedDeriv_fun_pow_zero]; simp [h.symm]
theorem expCanon{f:X→ℝ}(h:Taylor.germ f)(H:f 0=0): Lam.fitR (Real.exp ∘ f) x=formExp (fitR f x):= by
 ext i; rw [val_at,expandExp x h H, ← val_at, formExp_coeff]; unfold TaylorE Function.comp; rw [valSum x _ _ (fun l (_:l∈range (i+1)) => contDiffAt_const.mul (h.pow l)),map_sum]; refine Finset.sum_congr rfl fun l _=>?_; rw [valS x _ (h.pow l),valPow x h,PowerSeries.coeff_smul]; push_cast; rfl
end YM.FVAAlt2.AnalyticJets
