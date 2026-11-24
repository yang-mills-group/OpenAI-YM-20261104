import YM.X.Nest.Step
/-!
# budgets for exterior-legs. Run programs under Taylor probes. Polynomials truncated by arity on each line individually.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Asymptotics Reed Braid Finset
open scoped Topology ContDiff BigOperators Classical
variable {V I T:Type*} {i k n:ℕ}
variable (Q:T→Symmetric V)
local notation "L"=> Stella V T
local notation "ℙ"=>Code V T
variable {a b : Stella V T}(p:Code V T)(B:Subalgebra ℂ (T→ℂ))(x:Set (Stella V T))
def charge (c:T→ℂ):Code V T:=fun i=> C (c i)
def piece (a:Stella V T) : Code V T:= glyph ∘ a
def thing (l:List (Stella V T)): Code V T:= (l.map piece).prod
lemma thing_one : thing (V:=V) (T:=T) []=1:=rfl
lemma thing_cons (x:Stella V T)(l:List L) : thing (x::l)=piece x*thing l := rfl
lemma thing_val (b:List L)(t:T) : thing b t= (b.map (fun x=> glyph (x t))).prod:= by induction b with| nil=>rfl|cons a b IH=> rw [thing_cons,Pi.mul_apply, IH,List.map_cons,List.prod_cons];rfl
def Bag (n:ℕ): Submodule ℂ (Code V T):= Submodule.span ℂ {p| ∃ (l:List (Stella V T))(q:T→ℂ), (∀ a ∈l,a ∈ x)∧ q∈B ∧ l.length≤n ∧ p= charge q * thing l}
lemma bag (n:ℕ)(l:List (Stella V T)) (q:T→ℂ)(hq:q∈B)(h:∀ a ∈ l,a∈x)(hp:l.length≤n):charge q*thing l∈Bag B x n:= Submodule.subset_span ⟨l,q,h,hq,hp,rfl⟩
lemma alone (n:ℕ)(c:T→ℂ)(h:c∈B) : charge c∈ Bag B x n:= by rw [← mul_one (charge _), ← thing_one]; exact bag B x n [] c h (by simp) (Nat.zero_le n)
lemma promote (h:i≤k): Bag B x i≤ Bag B x k:= by apply Submodule.span_le.mpr; rintro _ ⟨l,z,h₁,h₂,he,rfl⟩; exact bag B x k l z h₂ h₁ (he.trans h)
lemma unify (q:T→ℂ):charge q*p=fun t=> q t • p t := funext fun i=> MvPolynomial.C_mul' ..
namespace Bag
variable {B} {x}
lemma point (h:p∈ Bag B x k)(c:T→ℂ)(hc:c∈B): charge c*p∈ Bag B x k:= by
   induction h using Submodule.span_induction with
   | mem _ h=> obtain ⟨l,y,h,g,hv,rfl⟩:=h; rw [← mul_assoc, show charge (V:=V) c*charge y =charge (c*y) from funext fun t=> (map_mul MvPolynomial.C ..).symm]; exact bag B x _ l _ (B.mul_mem hc g) h hv
   | zero=> simp
   | add u v _ _ ih ih'=> rw [mul_add]; exact Submodule.add_mem _ ih ih'
   | smul a x _ h => rw [mul_smul_comm];exact Submodule.smul_mem _ a h
lemma chap (h: a∈ x)(hp:p∈ Bag B x k): piece a * p ∈ Bag B x (k+1):= by
   induction hp using Submodule.span_induction with
   | mem _ h'=> obtain ⟨l,y,hh,g,ht,rfl⟩:= h'; rw [mul_left_comm,← thing_cons]; exact bag B x _ _ _ g (fun b hb=> by obtain rfl|p:=List.mem_cons.mp hb;exact h; exact hh _ p) (Nat.succ_le_succ ht)
   | zero=> simp
   | add u v _ _ x y=> rw [mul_add]; exact Submodule.add_mem _ x y
   | smul a v _ h=> rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
lemma necklace (l:List (Stella V T))(H:∀ a∈l, a∈x) (h:l.length≤n): thing l∈ Bag B x n:= by rw [← one_mul (thing l), show (1:Code V T)= charge (1:T→ℂ) from funext (fun i=>(map_one ..).symm)]; exact bag B x _ l _ (B.one_mem) H h
lemma retire (h:p∈ Bag B x 0): ∃ c:T→ℂ,c∈B ∧ p=charge c:= by
   induction h using Submodule.span_induction with
   | mem _ h=> obtain ⟨l,c,_,hc,ht,rfl⟩:=h; have q:= List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero ht); exact ⟨c,hc, by rw [q,thing_one,mul_one]⟩ -- edit
   | zero=> exact ⟨0,B.zero_mem,funext (fun _=> (map_zero C).symm)⟩
   | add a c _ _ ih p=> obtain ⟨x,h,rfl⟩:=ih; obtain ⟨y,hp,rfl⟩:=p; exact ⟨x+y, B.add_mem h hp,funext (fun i=> (map_add C ..).symm)⟩
   | smul a c _ x=> obtain ⟨d,h,rfl⟩:=x; refine ⟨a • d,B.smul_mem h a,funext (fun _=> ?_)⟩; simp [charge, ← C_mul'] -- check direction
lemma static_cost (v:Stella V T)(hp:∀ u∈x,cross Q v u∈B)(h:p∈Bag B x n) : stream Q v p∈ Bag B x n:= by
   have he(l:List L)(q:T→ℂ)(h: q∈B)(hc:∀ a∈l,a∈x): stream Q v (charge q * thing l)∈ Bag B x l.length := by
      induction l with
      | nil=> rw [thing_one,mul_one, show stream Q v (charge q)=0 from funext (fun i=> by rw [stream_point]; exact Derivation.map_algebraMap ..)]; exact Submodule.zero_mem _ -- defeq
      | cons a l IH=>
          rw [thing_cons, mul_left_comm]; let p:=charge q*thing l; have hi(x): x∈l→ x∈ (a::l):= List.mem_cons_of_mem a; have hf(p:Code V T): stream Q v (piece a*p)=piece a* stream Q v p+p* charge (cross Q v a):= by ext1 i; unfold piece charge cross; rw [stream_point,Pi.mul_apply]; simp only [Function.comp_apply,Derivation.leibniz,Pi.add_apply,Pi.mul_apply,Braid.link,stream_point,smul_eq_mul]
          rw [hf, mul_comm (charge q*thing l)]; exact Submodule.add_mem _ (Bag.chap (stream Q v p) (hc a (by simp)) (IH (fun x hx=> hc x (hi x hx)))) (promote B x (Nat.le_succ l.length) (Bag.point p (bag B x l.length _ _ h (fun x hx=> hc x (hi x hx)) le_rfl) _ (hp a (hc a (by simp)))))
   induction h using Submodule.span_induction with
   | mem u h=> obtain ⟨l,c,y,d,hp,rfl⟩:=h; exact promote B x hp (he l c d y)
   | zero=> rw [map_zero];exact Submodule.zero_mem _
   | add u t _ _ x y=> rw [map_add]; exact Submodule.add_mem _ x y
   | smul a u _ x=> rw [map_smul]; exact Submodule.smul_mem _ _ x
end Bag
end YM.PositionX.Crate
