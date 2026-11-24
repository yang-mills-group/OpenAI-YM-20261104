import YM.MSbar.Grass.Shuffle
import Mathlib.Data.Finsupp.Basic

/-! Super shuffle product, for arbitrary polarizations. ∂∂ Koszul signs from left differentiation
(inside to outside). This supplies the tree and lap on Fourier momentum kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset
open scoped Classical BigOperators
variable {T : Type*} (p:T→Bit)

def swap (p:T→Bit) (f : Series T) := ∀ (a : word T)(b c:T)(l:word T), f (a++b::c::l)=sign (p b) (p c)* f (a++c::b::l)
def Support (p:T→Bit)(d:Bit)(f:Series T) := ∀ s:word T,oddity p s≠d→f s=0
structure Homogeneous (p:T→Bit) (d:Bit)(f:Series T): Prop where
    commute: swap p f
    shape: Support p d f

def field (a:T) : Series T →ₗ[ℂ] Series T := {toFun:= fun f l => f (a::l),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
variable {f g h : Series T} {d e : Bit}
namespace Homogeneous
variable {p}
lemma add (hf: Homogeneous p d f)(hg: Homogeneous p d g): Homogeneous p d (f+g) := ⟨fun a b c l=>by simp_rw [Pi.add_apply,hf.commute a b c, hg.commute a b c, mul_add],fun l h=>by simp [hf.shape _ h,hg.shape _ h]⟩
lemma scaling (c:ℂ)(hf:Homogeneous p d f):Homogeneous p d (c • f):=by
    refine ⟨fun x a b y=> ?_,fun l h=>by simp [hf.shape _ h]⟩; rw [Pi.smul_apply,hf.commute]; exact mul_left_comm ..
lemma neg (hf: Homogeneous p d f): Homogeneous p d (-f):=by simpa using hf.scaling (-1)
lemma sub (hf: Homogeneous p d f)(hg:Homogeneous p d g): Homogeneous p d (f-g):=by rw [sub_eq_add_neg]; exact hf.add hg.neg
lemma zero : Homogeneous p d (0:Series T):= ⟨fun _ _ _ _=>by simp,fun _ _=>rfl⟩
lemma sum {ι:Type*} {F:ι→Series T} {K:Finset ι} (h:∀ i∈K, Homogeneous p d (F i)) : Homogeneous p d (∑ i∈K,F i):=by induction K using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero | insert i K hi ih=> rw [Finset.sum_insert hi]; exact (h _ (Finset.mem_insert_self ..)).add (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma comm (h:Homogeneous p d f) (a b:T) : field b (field a f)= sign (p a) (p b) • field a (field b f):= by funext s; exact h.commute [] a b s
lemma derives (h:Homogeneous p d f)(a:T):Homogeneous p (p a+d) (field a f):=
    ⟨fun s i j t=> h.commute (a::s) i j t,fun l hv=> h.shape (a::l) (fun he=> hv (by rw [oddity_cons] at he; rw [← he,cycle]))⟩
end Homogeneous

def join (p:T→Bit)(f g:Series T): Series T:= split p (fun a b=>f a*g b)
lemma join_zero_left : join p 0 g=0:=by
    unfold join; simp_rw [Pi.zero_apply,zero_mul]; exact split_zero p
lemma join_zero_right : join p f 0=0:=by unfold join; simp_rw [Pi.zero_apply,mul_zero]; exact split_zero p
lemma join_add_left : join p (f+g) h=join p f h+join p g h:=by unfold join; simp_rw [Pi.add_apply,add_mul]; exact split_add p (F:=fun a b=>f a*h b) (G:=fun a b=>g a*h b)
lemma join_add_right : join p h (f+g)=join p h f+join p h g:=by unfold join; simp_rw [Pi.add_apply,mul_add]; exact split_add p (F:=fun a b=>h a*f b) (G:=fun a b=>h a*g b)
lemma join_scale_left (c:ℂ): join p (c • f) g=c • join p f g:=by unfold join; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc]; exact split_scale p (F:=fun a b=> f a*g b) c
lemma join_scale_right (c:ℂ): join p f (c • g)=c • join p f g:=by unfold join; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ c]; exact split_scale p (F:=fun a b=> f a*g b) c

def merge (p:T→Bit): Series T →ₗ[ℂ] Series T→ₗ[ℂ] Series T:=LinearMap.mk₂ ℂ (join p) (fun _ _ _=>join_add_left p) (fun _ _ _=>join_scale_left p _) (fun _ _ _=>join_add_right p) (fun _ _ _=>join_scale_right p _)
lemma join_sum_left {ι:Type*} (W:Finset ι) (f:ι→Series T) (g : Series T):join p (∑ i∈W,f i) g=∑ i∈W,join p (f i) g:=map_sum ((merge p).flip g) ..
lemma join_sum_right {ι:Type*} (W:Finset ι) (f:Series T)(g:ι→Series T):join p f (∑ i∈W,g i)=∑ i∈W,join p f (g i):=map_sum (merge p f) ..
variable {p}
lemma joined (hf : Support p d f) (hg : Support p e g): Support p (d+e) (join p f g):=by
    intro l h; refine split_clear p (v:=l) ?_; intro u w hv
    by_cases hE:oddity p u=d
    · have hG:oddity p w≠e:=fun he => h (((hv.map p).sum_eq).symm.trans (by change oddity p (u++w)=_; rw [oddity_plus,hE,he]))
      exact mul_eq_zero_of_right _ (hg _ hG)
    exact mul_eq_zero_of_left (hf _ hE) _
lemma product_rule (hf : Support p d f) (g: Series T) (a:T): field a (join p f g)=join p (field a f) g+sign (p a) d • join p f (field a g):=by
    funext v; change split p (fun s t=>f s*g t) (a::v)=_+_*_
    rw [split_next]; unfold join; congr! 1
    let F(s t):=f s*g (a::t);let c:=sign (p a) d
    refine (split_change p (G:=c • F) ?_).trans (congr_fun (split_scale (F:=F) p c) v)
    intro u w h; change _=sign (p a) d*(f u*g (a::w)); by_cases ht: oddity p u=d
    · rw [ht]
    simp [hf u ht]

end YM.MSbar.Super
