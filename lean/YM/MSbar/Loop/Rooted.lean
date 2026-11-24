import YM.MSbar.Loop.Reaches
/-! Expand R as rooted singleton terms at each external label. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Finsupp Super Finset
open scoped BigOperators Classical
variable {C M: Type*} [AddCommGroup M] {p:C→Bit} {I:Finset C} {R:Row C M} {f : Amps C M} {j k:Bit}

def flow (R:Row C M)(I:Finset C) (f:Amps C M)(x y:Field C M):= match x with
  | [a] => ∑ b∈I,R a.1 b a.2 * f ((b,a.2)::y)
  | _ => 0
private lemma enter {T : Type*} (p:T→Bit)(v:Super.word T)(F:Super.word T→ Super.word T→ℂ)(hp:∀ x v z,F (x::v) z=0): split p F v=F [] v:=by
    induction v generalizing F with
    | nil=> exact split_nil p
    | cons a x ih=> rw [split_next,split_clear (F:=fun s t=> F (a::s) t) (he:=fun u w hv=> hp a u w),ih,oddity_nil,sign_zero,one_mul,zero_add];intro x v z;rw [hp,mul_zero]
private lemma collapse (he:Kinetic p I k R) (hf:Homogeneous (lift p) j f) (a x:Wave C M)(u): sign (lift p a) (lift p x)*flow R I f [x] (a::u) = sign k (lift p a)* flow R I (field a f) [x] u:=by
    unfold flow; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y hy
    let z:=R x.1 y x.2; rcases eq_or_ne z 0 with h|h
    · change _*(z*_)=_*(z*_); rw [h]; ring
    set b:Wave C M:= (y,x.2) with hb
    have ht: oddity (lift p) [b]=p x.1+k:=by rw [oddity_cons,oddity_nil,add_zero]; exact (he _ y hy x.2 h).symm
    rw [oddity_cons,oddity_nil,add_zero] at ht
    change sign (lift p a) (lift p x)*(z*f (b::a::u))=sign k (lift p a)*(z*f (a::b::u)); rw [show f (b::a::u)=_ from hf.commute [] b a u,ht]; -- norm
    simp only [List.nil_append,sign_add]; rw [braid (lift p a)]; unfold lift; ring_nf; rw [pow_two,sign_self,one_mul]
lemma rooted (he:Kinetic p I k R)(hf:Homogeneous (lift p) j f): (rotate he).lift f=split (lift p) (flow R I f):=by
   funext x; induction x generalizing j f with
   | nil=>rw [split_nil,Transport.base];rfl
   | cons a v ih=>
      rcases a with ⟨a,t⟩; let w:Wave C M:= (a,t); change field w ((rotate he).lift f) v=_; rw [Transport.leg]; rw [split_next,Pi.add_apply,row_here,Pi.smul_apply,ih (hf.derives w)]
      rw [enter (lift p) v (fun s t=> flow R I f (w::s) t) (fun _ _ _=>rfl)]; congr! 1
      refine Eq.symm ((split_change (lift p) (G:=sign k (p a) • flow R I (field w f)) ?_).trans (congr_fun (split_scale ..) v)); intro x y h
      rcases x with _|⟨x,_|⟨_,_⟩⟩ <;>simp only [Pi.smul_apply,smul_eq_mul,flow,oddity_cons,oddity_nil,add_zero,mul_zero]
      exact collapse he hf ..
end YM.MSbar.Loops
