import YM.Next.MAXWELL.Pole
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Powers

/-!
# Polynomial continuation on a complex line

Simple cross multiplied version of being regular at +i after multiplying poles.
Keep identities only for large **real** parameter, to make clearances automatic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Traverse
open Function Set Filter Polynomial Tensor Maxwell Maxwell.Free
open scoped BigOperators Topology ContDiff

def jump (p : ℂ[X]) := p.eval Complex.I
def realLine (p : ℂ[X]) : ℝ → ℂ := fun t => p.eval (t:ℂ)
def Landing (f : ℝ→ℂ) (c : ℂ) := ∃ p q, jump q≠0 ∧ jump q*c=jump p ∧ realLine q*f =ᶠ[atTop] realLine p
lemma polynomial (p : ℂ[X]): Landing (realLine p) (jump p) := ⟨p,1,by simp [jump],by simp [jump],EventuallyEq.of_eq (by simp [realLine,funext_iff])⟩
variable {f g : ℝ→ℂ} {p q r s : ℂ[X]} {a b:ℂ}
lemma vanishes_eval (p : ℂ[X]) (h : realLine p =ᶠ[atTop] 0) : p=0 := by
  obtain ⟨y,hy⟩:= eventually_atTop.mp h
  by_contra he
  have h := (Ici_infinite y).image (Complex.ofReal_injective.injOn)
  apply h; refine (p.roots.toFinset.finite_toSet).subset ?_; rintro i ⟨x,hx,rfl⟩; exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots he).mpr (hy _ hx))
lemma Landing.unique (H : Landing f a) (K : Landing f b): a=b:= by
  obtain ⟨p,q,hp,hq,h⟩:=H; obtain ⟨r,s,hr,hs,h'⟩:=K
  have he : p*s-r*q=0:=vanishes_eval _ (by
    filter_upwards [h,h'] with t ht hv
    change q.eval (t:ℂ)*f t=p.eval (t:ℂ) at ht; change s.eval (t:ℂ)*f t=r.eval (t:ℂ) at hv
    change (p*s-r*q).eval _ = 0; simp [←ht,←hv]; ring)
  have ht:= congr_arg jump he; simp only [jump,eval_sub,eval_mul,eval_zero] at ht
  change jump p * jump s-jump r*jump q=0 at ht; rw [← hq,←hs] at ht
  apply mul_left_cancel₀ (mul_ne_zero hp hr); linear_combination ht
lemma Landing.congr (H : Landing f a) (he:f=ᶠ[atTop]g): Landing g a:= by
  obtain ⟨p,q,h1,h2,h⟩:=H; exact ⟨p,q,h1,h2,((EventuallyEq.refl ..).mul he.symm).trans h⟩
lemma constant (a : ℂ): Landing (fun _=> a) a:= Landing.congr (f:=realLine (C a)) (by rw [show Landing (realLine (C a)) a ↔ Landing (realLine (C a)) (jump (C a)) by simp [jump]]; exact polynomial _) (Eventually.of_forall fun _=> eval_C ..)

lemma Landing.mul (H : Landing f a) (K : Landing g b): Landing (fun t=> f t*g t) (a*b):= by
  obtain ⟨p,q,hp,hq,h⟩:=H; obtain ⟨r,s,hr,hs,h'⟩:=K
  refine ⟨p*r,q*s,?_,?_,?_⟩
  · simpa only [jump,eval_mul] using mul_ne_zero hp hr
  · unfold jump; rw [eval_mul,eval_mul,mul_mul_mul_comm]; rw [show q.eval _*a=_ from hq,show s.eval _*b=_ from hs]; rfl
  filter_upwards [h,h'] with t ht hv; change (q*s).eval _ * (_*_) = (p*r).eval _; rw [eval_mul,eval_mul,mul_mul_mul_comm]; exact congr_arg₂ (·*·) ht hv
lemma Landing.add (H : Landing f a) (K : Landing g b): Landing (fun t=> f t+g t) (a+b):= by
  obtain ⟨p,q,hp,hq,h⟩:=H; obtain ⟨r,s,hr,hs,h'⟩:=K
  have he (a b P Q R S : ℂ) (ht : Q*a=P) (hk : S*b=R): Q*S*(a+b)=S*P+Q*R:= by rw [← ht,← hk]; ring
  refine ⟨s*p+q*r,q*s,?_,?_,?_⟩
  · simpa only [jump,eval_mul] using mul_ne_zero hp hr
  · unfold jump; simp only [eval_add,eval_mul]; exact he _ _ _ _ _ _ hq hs
  filter_upwards [h,h'] with t ht hv; change (q*s).eval _ * (_+_) = (s*p+q*r).eval _; simp only [eval_add,eval_mul]; exact he _ _ _ _ _ _ ht hv
lemma landed_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → ℝ → ℂ) (h : ∀ i∈s,Landing (f i) (a i)): Landing (fun t=>∑ i∈s,f i t) (∑ i∈s,a i):=by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact constant _
  | insert x s hx ih=>simp_rw [Finset.sum_insert hx]; exact (h x (Finset.mem_insert_self ..)).add (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))

end YM.XSpace.Traverse
