import YM.MSbar.Whisk.Troop
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao PowerSeries
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d' :ℕ} {S r a b t u v B D E :ℝ}{f g g' h:Pot σ}{T R: List σ} {k k':σ→σ→ℝ}
structure Omnibus (l:σ→ Site n)(x:Site n)(a B:ℝ)(p m:ℕ)(ξ:View σ)(f g F G:Pot σ)(t ε:ℝ):Prop where
    bulk: Paired l x a B p m ξ f g t ε t
    post: Paired l x a B p m ξ F G t ε t
    drift : Starry l x a B p m ξ (f-F) (g-G) t ε t
set_option quotPrecheck false
local notation "J"=> juncture
namespace Omnibus
variable {F H v₀ v₁ u₀ u₁:Pot σ}(h₀:Gain l x a B p k k' b D)
lemma tension (h:Omnibus l x a B p m ξ f g F H t D)(he:0 ≤ D)(hq:q≤m)(ht:t≤u): Omnibus l x a B p q ξ f g F H u D:=⟨Paired.widen h.bulk ht he ht hq,Paired.widen h.post ht he ht hq,Starry.widen h.drift ht he ht hq⟩
lemma addN (h:Omnibus l x a B p m ξ f g F H t D)(u:Omnibus l x a B p m ξ v₀ v₁ u₀ u₁ b D): Omnibus l x a B p m ξ (f+v₀) (g+v₁) (F+u₀) (H+u₁) (t+b) D:=by refine ⟨h.bulk.addN u.bulk,h.post.addN u.post,?_⟩; rw [show f+_-(F+_)=f-F+(v₀-u₀) from (by abel),show g+_-(H+_)=g-H+(v₁-u₁) from (by abel)]; exact h.drift.addN u.drift
lemma scaled (h:Omnibus l x a B p m ξ f g F H t D)(r:ℝ): Omnibus l x a B p m ξ (r • f) (r • g) (r • F) (r • H) (|r| * t) D:=by
    refine ⟨h.bulk.mulR r,h.post.mulR r,?_⟩; rw [← smul_sub,← smul_sub]; exact h.drift.mulR r
lemma void : Omnibus l x a B p m ξ 0 0 0 0 0 D := by
    have hv: Vigor l x a B p m ξ (0:P) (0*D):=by rw [zero_mul]; refine ⟨le_refl _,fun i=> ?_⟩; rw [map_zero,mul_zero]; exact Quote.nill (le_refl _)
    have hh: Paired l x a B p m ξ 0 0 0 D 0:= by
       have h:Tokew l (a+B) p m ξ (0:P) 0:= by refine ⟨le_refl _,fun i=>?_⟩;rw [map_zero]; exact Quote.nill (le_refl _)
       exact ⟨h,h,(sub_self (0:P)).symm ▸ hv⟩ -- bad ▸
    refine ⟨hh,hh,?_⟩; simp only [sub_self]; refine ⟨Quote.nill (le_refl _),Quote.nill (le_refl _),?_⟩; rw [sub_self,zero_mul]; exact Quote.nill (le_refl _)
lemma pooling (f g f' g':ι→Pot σ)(s:Finset ι)(b:ι→ℝ)(h:∀ i∈s, Omnibus l x a B p m ξ (f i) (g i) (f' i) (g' i) (b i) D): Omnibus l x a B p m ξ (∑ i∈s,f i) (∑ i∈s,g i) (∑ i∈s,f' i) (∑ i∈s,g' i) (∑ i∈s,b i) D:=by
   induction s using Finset.induction_on with
   | empty=>simpa only [sum_empty] using Omnibus.void
   | insert i s hi ih=> simp only [sum_insert hi]; exact (h i (mem_insert_self ..)).addN (ih (fun i he=> h i (mem_insert_of_mem he)))
include h₀
lemma rain (h:Omnibus l x a B p (m+2) ξ f g F H t D) : Omnibus l x a B p m ξ (stove k f) (stove k' g) (stove k F) (stove k' H) (t+b*t) D:= by
    have he:b*t ≤ t+b*t:=le_add_of_nonneg_left (h.bulk.input.1); refine ⟨(h.bulk.rail h₀).widen he h₀.soft le_rfl le_rfl,(h.post.rail h₀).widen he h₀.soft le_rfl le_rfl,?_⟩
    rw [← _root_.map_sub,←_root_.map_sub]; exact (h.drift.rail h₀).widen he h₀.soft le_rfl le_rfl
lemma transit (h:Omnibus l x a B p (m+2) ξ f g F H t D)(hw:Omnibus l x a B p (m+2) ξ v₀ v₁ u₀ u₁ t D):Omnibus l x a B p m ξ (J k f v₀) (J k' g v₁) (J k F u₀) (J k' H u₁) ((4*2^m)*(t^2+b*t^2)) D:=by
    let A:= t*t+t*b*t+t*b*t; let G:=4* (2:ℝ)^m*(t^2+b*t^2); let n:=(2:ℝ)^m; have he:0 < n:= pow_pos (by norm_num) m
    have ht:=h.bulk.input.1; have hh:= h₀.full.hope
    have hc₁: 2*n*(t*(b*t)) ≤ G:=by unfold G; change _≤4*n*_ ; have hh: 0≤4*n*t^2:=mul_nonneg (by unfold n; positivity) (sq_nonneg _); nlinarith only [hh,(show 0≤n*b*t^2 from mul_nonneg (mul_nonneg he.le h₀.full.hope) (sq_nonneg _))]
    have hc₂ : 2*n*A ≤ G:= by unfold A G; change _ ≤4*n*(t^2+b*t^2); nlinarith only [(show 0≤n*t^2 from mul_nonneg he.le (sq_nonneg _))]
    have hp(e p U V:P) (T) : J T e p-J T U V=J T (e-U) p+ J (fun i j=> T j i) (p-V) U :=by rw [reversal (fun i j=>T j i)]; unfold juncture; simp_rw [map_sub,sub_mul,mul_sub,smul_sub,sum_sub_distrib]; abel
    let h₁:= h.tension h₀.soft (q:=m+1) (by omega) le_rfl; let h₂:=hw.tension h₀.soft (q:=m+1) (by omega) le_rfl
    refine ⟨(h₁.bulk.wheel h₀ h₂.bulk).widen hc₁ h₀.soft hc₂ le_rfl, (h₁.post.wheel h₀ h₂.post).widen hc₁ h₀.soft hc₂ le_rfl,?_⟩
    rw [hp, hp]
    let hV:= h₀.soft; have he':= Starry.addN (Starry.wheel h₀ h₁.drift ((h₂.bulk.widen le_rfl hV le_rfl (Nat.le_succ m)))) (Starry.wheel (H₀:=h₀.flip) h₂.drift (h₁.post.widen le_rfl hV le_rfl (Nat.le_succ m)))
    exact he'.widen (le_trans (b:=2*n*(t*(b*t))) (by unfold n; exact le_of_eq (by ring)) hc₁) hV ((le_of_eq (by ring : n*A+n*A=2*n*A )).trans hc₂) le_rfl
end Omnibus
end YM.MSbar.Whisk
