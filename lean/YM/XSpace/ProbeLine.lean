import YM.Next.MAXWELL.Flavor
import Mathlib.Algebra.Polynomial.Roots
/-!
# Finite rational point continuations used only for the Maxwell normalization

One complex line variable. `Germ.Proof` means AGREE eventually on real
ray and regular at I, not an assumption of distributional continuation
of Yang-Mills. Supports algebraic pole isolation. All finite ray lines
from the actual Wick covariance admitted through finite derivative orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.ProbeLine
open Set Filter Function MeasureTheory Maxwell Tensor
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
local notation "I" => Complex.I

structure Proves (f : ℝ→ℂ) (c:ℂ) : Prop where
  program : ∃ p q:Polynomial ℂ,q.eval I ≠ 0 ∧ p.eval I=q.eval I*c∧∀ᶠ r:ℝ in atTop,(p.eval (r:ℂ))=(q.eval (r:ℂ))*f r

namespace Proves
variable {f g: ℝ→ℂ} {c d:ℂ}
lemma ship (p:Polynomial ℂ) : Proves (fun r:ℝ=>p.eval (r:ℂ)) (p.eval I):= ⟨p,1,by simp,by simp,Eventually.of_forall fun r=>by simp⟩
lemma unit (c:ℂ): Proves (fun _:ℝ=>c) c:=by simpa using ship (Polynomial.C c)
lemma alter (h:Proves f c) (he:f=ᶠ[atTop]g) : Proves g c:= by
  obtain ⟨p,q,hq,hp,H⟩:=h; refine ⟨p,q,hq,hp,?_⟩; filter_upwards [H,he] with r hx hr; rw [← hr]; exact hx
lemma zero_of_along (p:Polynomial ℂ) (h : ∀ᶠ r:ℝ in atTop,p.eval (r:ℂ)=0): p=0:= by
  by_contra hp
  let T:= p.roots.toFinset
  let f:= Complex.re
  have he : BddAbove (f '' (T:Set ℂ)):= ((Finset.finite_toSet T).image f).bddAbove
  obtain ⟨K,hK⟩:= he
  obtain ⟨r,h₁,h₂⟩:=(h.and (eventually_gt_atTop K)).exists
  exact h₂.not_ge (show r≤K from by simpa [f] using hK (mem_image_of_mem f (show (r:ℂ)∈ (T:Set ℂ) by simpa only [T,Finset.mem_coe, Multiset.mem_toFinset] using (Polynomial.mem_roots hp).mpr h₁)))
lemma zero (h:Proves f c) (hp:∀ᶠ r:ℝ in atTop,f r=0): c=0 := by
  obtain ⟨p,q,hq,hg,H⟩:=h.program
  have ht := zero_of_along p ((H.and hp).mono fun r ⟨hu,hw⟩=> by rw [hu,hw,mul_zero]); rw [ht,Polynomial.eval_zero] at hg
  exact (mul_eq_zero.mp hg.symm).resolve_left hq

lemma add (h:Proves f c) (g':Proves g d): Proves (f+g) (c+d):= by
  obtain ⟨p,q,hq,hp,H⟩:=h.program; obtain ⟨s,r,hr,hs,J⟩:=g'.program
  refine ⟨p*r+s*q,q*r,mul_ne_zero_eval hq hr,by simp [hp,hs]; ring,?_⟩
  filter_upwards [H,J] with t ht hh; simp only [Polynomial.eval_add,Polynomial.eval_mul,Pi.add_apply,ht,hh]; ring
where mul_ne_zero_eval {p q:Polynomial ℂ}(h:p.eval I≠0)(g:q.eval I≠0): (p*q).eval I≠0:=by rw [Polynomial.eval_mul]; exact mul_ne_zero h g
lemma mul (h:Proves f c) (g':Proves g d): Proves (f*g) (c*d):= by
  obtain ⟨p,q,hq,hp,H⟩:=h.program; obtain ⟨s,r,hr,hs,J⟩:=g'.program
  refine ⟨p*s,q*r,by rw [Polynomial.eval_mul]; exact mul_ne_zero hq hr,by simp [hp,hs]; ring,?_⟩
  filter_upwards [H,J] with t ht hh; simp only [Polynomial.eval_mul,Pi.mul_apply,ht,hh]; ring
lemma sub (h:Proves f c) (hc:Proves g d): Proves (f-g) (c-d):= by
  have hp := h.add ((unit (-1)).mul hc)
  have ht : f+(fun _:ℝ=>(-1:ℂ))*g=f-g:=funext fun i=>by simp [sub_eq_add_neg]
  simpa [ht,sub_eq_add_neg] using hp -- inspect
lemma times (h:Proves f c) (r:ℂ): Proves (r • f) (r*c):= (unit r).mul h
lemma unique (h:Proves f c) (hc:Proves f d): c=d:=sub_eq_zero.mp ((h.sub hc).zero (Eventually.of_forall fun i=>by simp))
lemma pow (h:Proves f c) (n:ℕ): Proves (f^n) (c^n):= by induction n with | zero=>exact pow_zero c ▸ (show Proves (f^0) 1 by simpa using (show Proves (1:ℝ→ℂ) 1 from unit 1))| succ n ih=>rw [pow_succ,pow_succ]; exact ih.mul h
lemma inv (h:Proves f c) (hc:c≠0): Proves f⁻¹ c⁻¹:= by
  obtain ⟨p,q,hq,hp,H⟩:=h.program
  have he:p.eval I≠0:=by rw [hp]; exact mul_ne_zero hq hc
  let T:= Complex.re '' Set.range (fun a:(↥p.roots.toFinset)=> (a.val:ℂ)); obtain ⟨K,hK⟩:= ((Set.finite_range (fun a:(↥p.roots.toFinset)=> a.val)).image Complex.re).bddAbove
  refine ⟨q,p,he,?_ ,?_⟩
  · rw [hp,mul_assoc,mul_inv_cancel₀ hc,mul_one]
  filter_upwards [H,eventually_gt_atTop K] with r hr h
  have ht:p.eval (r:ℂ)≠0 := fun he'=> h.not_ge (by
    have hx : p≠0:=fun hx=>he (hx ▸ Polynomial.eval_zero)
    have hp : (r:ℂ)∈p.roots.toFinset:= Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hx).mpr he')
    exact hK ⟨↑r,⟨⟨_,hp⟩,rfl⟩,rfl⟩)
  rw [hr] at *; change _=_* (f r)⁻¹; rw [mul_assoc,mul_inv_cancel₀ (right_ne_zero_of_mul ht),mul_one]
lemma sum {α : Type*} (F:Finset α) (f:α→ℝ→ℂ) (c:α→ℂ) (h :∀ i∈F, Proves (f i) (c i)):Proves (fun r=>∑ i∈F,f i r) (∑ i∈F,c i):= by
  induction F using Finset.induction_on with
  | empty=> simp; exact unit _
  | @insert i F hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih (fun i hx=> h _ (Finset.mem_insert_of_mem hx)))
end Proves

-- list of complex values of real physical coordinate along line
variable (m u y:E4)
def drifts (t:ℝ):E4:=m+t • u-y

def corner (a:Axis):ℂ:= (m a:ℂ) + I*(u a:ℂ) - (y a:ℂ)
lemma corner_match (a:Axis): Proves (fun r=> (drifts m u y r a:ℂ)) (corner m u y a):= by
  unfold drifts corner
  have he:=Proves.ship (Polynomial.X (R:=ℂ)); simp only [Polynomial.eval_X] at he
  simpa only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,smul_eq_mul,Pi.mul_def,Pi.sub_def,Pi.add_def] using ((Proves.unit (m a)).add (he.mul (Proves.unit (↑(u a))))).sub (Proves.unit (↑(y a))) -- inspect

def cubic:= ∑ a:Axis, corner m u y a * corner m u y a
def rsq (x:E4):= ‖x‖^2
lemma square_match: Proves (fun r:ℝ=> (↑(rsq (drifts m u y r)):ℂ)) (cubic m u y):= by
  simp_rw [cubic,rsq,EuclideanSpace.real_norm_sq_eq,Complex.ofReal_sum, sq,Complex.ofReal_mul]; apply Proves.sum; intro i _; exact (corner_match m u y i).mul (corner_match m u y i)

lemma wandering (hu:u≠0): ∀ᶠ r:ℝ in atTop, drifts m u y r ∈ away:= by
  have ht : Function.Injective (drifts m u y):= fun x y h=> smul_left_injective ℝ hu (add_left_cancel (add_right_cancel (show m+x • u+-_=m+y • u+-_ from h))) -- inspect
  by_cases he : ∃ r, drifts m u y r=0
  · obtain ⟨r,h⟩:=he; exact (eventually_gt_atTop r).mono fun t hp (hq:drifts m u y t=0)=> hp.ne (ht (h.trans hq.symm)) -- order
  exact Eventually.of_forall fun r h=> he ⟨r,h⟩
end YM.XSpace.ProbeLine
