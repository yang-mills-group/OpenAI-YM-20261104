import YM.XSpace.Traversal
import YM.XSpace.Posters

/-!
# Every real Wick leg tested against a moving position is rational

Here turn the *real-space* `Clears` estimates in the constructive Maxwell
library into a complex line test, with denominator powers. Only for the free
kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Traverse
open Function Set Filter Tensor Maxwell Maxwell.Free
open Polynomial hiding funext
open MultiNext.SignedSource
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {n j l : ℕ}

def course (v u : E4) (t : ℝ):= v+t • u
private lemma along_multilinear (A : Tensor.T E4 ℝ n) (v u : E4) : ∃ p : ℝ[X],∀ t : ℝ,p.eval t=Tensor.diagonal A (course v u t):= by
  induction n with
  | zero => exact ⟨C (A (fun _=>0)),fun t=> by rw [eval_C]; exact congr_arg A (Subsingleton.elim ..)⟩
  | succ n ih =>
    obtain ⟨p,hp⟩:=ih (A.curryLeft v)
    obtain ⟨q,hq⟩:=ih (A.curryLeft u)
    refine ⟨p+ X*q,fun t=>?_⟩
    rw [eval_add,eval_mul,eval_X,hp,hq,show diagonal A (course v u t)=diagonal (A.curryLeft (v+t • u)) (course v u t) from ?_, _root_.map_add, _root_.map_smul]
    · rfl
    apply congr_arg A; ext1 i; refine Fin.cases ?_ (fun _=> ?_) i <;> rfl

private lemma ready (F : E4 → ℝ) (H : Pole (n+3) F) : ∃ A : Tensor.T E4 ℝ (n+1), ∀ x:E4,x∈away → rad (n+2) x*F x= diagonal A x := by
  obtain ⟨g,hg,h⟩:= H.precise
  have hh := fun x hx=> (show rad (n+2) x*F x=g x from h x hx)
  refine ⟨Tensor.coeff g (n+1) 0,fun x hx=> (hh x hx).trans (congr_fun (Powers.tensor_form (show Powers.home g (n+1) from ⟨hg,?_⟩)) x)⟩
  have he (x:E4) (hx : x ∈ away) : (fun t : ℝ=> g (t • x))=(fun t=>t^(n+1)*g x):= by
    funext t; apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜:=ℝ) (U:=Set.univ) (f:=fun t:ℝ=>g (t • x)) ?_ (g:=fun t=> t^(n+1)*g x) ?_ isPreconnected_univ (mem_univ (1:ℝ)) ?_ (mem_univ t)
    · intro t _; exact ((hg.comp (contDiff_id.smul contDiff_const)).contDiffAt).analyticAt
    · intro t _; exact (analyticAt_id.pow _).mul analyticAt_const
    filter_upwards [lt_mem_nhds (by norm_num : (0:ℝ)<1)] with t ht
    have hl : 0 < t:= ht
    rw [← hh (t • x) (smul_ne_zero hl.ne' hx), H.degree _ hl _ hx,← hh x hx]
    simp only [smul_eq_mul,rad,norm_smul,Real.norm_eq_abs,abs_of_pos hl,mul_pow,pow_add,inv_pow]; field_simp; ring
  have hh' : g 0=0:=by
    rw [← show (0:ℝ) • basis 0 = (0:E4) by simp]; simpa using congr_fun (he (basis 0) (norm_pos_iff.mp (by simp))) 0
  intro t x
  by_cases ha:x=0; simp [ha,hh']
  exact congr_fun (he _ ha) _

lemma line_numerator (a : Legs.Paint G) (b : Legs.Paint G) (v u : E4) : ∃ p:ℂ[X],∀ t:ℝ,course v u t≠0 →
    realLine p t= (rad (a.1.1+b.1.1+3) (course v u t)* legKernel (Legs.qr a) (Legs.qr b) (course v u t):ℝ) :=by
  let m := a.1.1+b.1.1
  obtain ⟨A,hA⟩:= ready _ ((show m+1+3=4+a.1.1+b.1.1 by unfold m; omega).symm ▸ kernel_pole (Legs.qr a) (Legs.qr b)); obtain ⟨p,hp⟩:= along_multilinear A v u
  refine ⟨p.map Complex.ofRealHom,fun t ht=> (eval_map_apply (p:=p) Complex.ofRealHom t).trans (congr_arg (fun x:ℝ=>(x:ℂ)) ((hp t).trans (hA _ ht).symm))⟩

def interval (v u : E4) : ℂ[X]:= C ((‖v‖^2:ℝ):ℂ) + C ((2*inner ℝ v u:ℝ):ℂ) * X+ C ((‖u‖^2:ℝ):ℂ)*X^2
lemma along_square (v u : E4) (t : ℝ): realLine (interval v u) t = (‖course v u t‖^2:ℝ):=by
  unfold realLine interval course; rw [norm_add_sq_real,norm_smul,real_inner_smul_right,mul_pow]; simp [eval_add,eval_mul,eval_pow]; ring
lemma jumps (v u : E4): jump (interval v u)= ((‖v‖^2:ℝ):ℂ) - ((‖u‖^2:ℝ):ℂ) + ((2*inner ℝ v u:ℝ):ℂ)*Complex.I:=by simp only [interval,jump,eval_add,eval_pow,eval_mul,eval_C,eval_X,Complex.I_sq]; ring

lemma sliding {v u : E4} (hu : u≠0): ∀ᶠ t:ℝ in atTop, course v u t≠0:=by
  have ht : Injective (course v u) := fun x y h=> smul_left_injective ℝ hu (add_left_cancel (a:=v) h)
  by_cases h : 0∈Set.range (course v u)
  · obtain ⟨y,rfl'⟩:=h; rw [← rfl']; exact (eventually_gt_atTop y).mono fun x hx=> ht.ne (ne_of_gt hx)
  exact Eventually.of_forall fun _ he=> h ⟨_,he⟩
lemma travels (a b: Legs.Paint G) {v u : E4} (hu : u≠0) (hx : jump (interval v u)≠0): ∃ z, Landing (fun t=> (legKernel (Legs.qr a) (Legs.qr b) (course v u t):ℂ)) z:=by
  obtain ⟨p,hp⟩:=line_numerator a b v u
  let n:= a.1.1+b.1.1+3; let q:= interval v u ^ n
  have hh : jump q≠0:=by unfold q; rw [jump,eval_pow]; exact pow_ne_zero _ hx
  refine ⟨jump p / jump q,p,q,hh,mul_div_cancel₀ _ hh,?_⟩
  filter_upwards [sliding (v:=v) hu] with t ht
  change realLine q t * _= _; rw [show realLine q t= ((rad n (course v u t):ℝ):ℂ) from ?_, ← Complex.ofReal_mul]; exact (hp t ht).symm
  unfold q; rw [realLine,eval_pow, ← show (‖course v u t‖^2:ℝ)^n=rad n (course v u t) from rfl,show (interval v u).eval _= _ from along_square v u t, Complex.ofReal_pow]
  push_cast; rfl
end YM.XSpace.Traverse
