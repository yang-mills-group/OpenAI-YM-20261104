import YM.RemainderComparison.Fallow.Apogee
/-! # Input banners. An assembly-coupling proof.
Exact product without assuming even that all incoming levels already underwent
linear recapture. Full K factor replacements (including repeated alternatives
on the same slot). Multiplication in ANY commutative ring. Works at each field
on the real evaluation; not unmasked dictionary identification (later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Encore
open Function Filter Finset
open scoped Classical BigOperators
variable {ι α : Type} {K : Type*} [CommRing K]
variable (f :ι→ Option α) (g:ι→ K)(V:α→ K)
-- none = unique log Wing. All Wing alternatives on gas slots. 
def token (s:Finset ι) : Finset α := s.biUnion (fun i=>(f i).elim ∅ (fun a=>{a}))
def leaf (s:Finset ι)(i:α) := V i+∑ x∈s,if f x=some i then g x else 0
def unique (s:Finset ι):Prop:= ∀ x∈s,∀ y∈s,∀ a,f x=some a→ f y=some a→ x=y
variable (s:Finset ι)(k:Finset α)(i:α)(a:ι)
def chop : K:= if unique f s∧ token f s ⊆ k then (∏ i∈s,g i)*∏ i∈k\token f s,V i else 0
lemma songx : i∈ token f s↔ ∃ x∈s,f x=some i:=by
    unfold token; rw [mem_biUnion]; refine exists_congr fun x=> and_congr_right fun h=>?_ ; cases f x <;> simp [eq_comm]
lemma edited : unique f (insert a s) ↔ unique f s ∧ (∀ x∈ s,∀ i,f x=some i→ f a=some i→x=a):=by
    constructor; intro h; exact ⟨fun x hx y hy=> h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy),fun x hx=> h x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self ..)⟩
    rintro ⟨hp,ht⟩ x hx y hy i he hd; rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with h|hy
    · exact h.symm
    · exact (ht y hy i hd he).symm
    · rw [h] at hd ⊢; exact ht x hx i he hd
    exact hp _ hx _ hy i he hd
lemma spends (ha:a∉s)(h:f a=none): chop f g V (insert a s) k= g a*chop f g V s k:=by
    have he: unique f (insert a s) ↔ unique f s:=by rw [edited]; simp [h]
    unfold chop; rw [he]; simp only [token, biUnion_insert,h,Option.elim,empty_union,prod_insert ha]; split<;> simp [mul_assoc]
lemma yields (ha:a∉s)(h:f a=some i) : chop f g V (insert a s) k=if i∈k then g a * chop f g V s (k.erase i) else 0:=by
    have hh : unique f (insert a s)↔unique f s∧ i∉token f s:=by
       rw [edited]; apply and_congr_right; intro _; rw [songx]; constructor
       · intro hR; rintro ⟨x,hp,hv⟩; exact ha (hR x hp i hv h ▸ hp)
       intro hR x hx j he ht; exact (hR ⟨x,hx,(he.trans (ht.symm.trans h))⟩).elim
    have hp: token f (insert a s)=insert i (token f s):=by unfold token; simp only [biUnion_insert,h,Option.elim,singleton_union]
    unfold chop; rw [hp]; by_cases ht:i∈ k
    · rw [if_pos ht]; have h : unique f (insert a s)∧ insert i (token f s)⊆k↔unique f s ∧ token f s⊆ k.erase i:= by
         rw [hh, Finset.insert_subset_iff]; constructor; · rintro ⟨⟨hx,hL⟩, _,hq⟩; exact ⟨hx,fun j hj=> mem_erase.mpr ⟨fun h=>hL (h ▸ hj),hq hj⟩⟩
         rintro ⟨hA,hD⟩; exact ⟨⟨hA,fun hx=> Finset.notMem_erase _ _ (hD hx)⟩,ht,hD.trans (Finset.erase_subset ..)⟩
      simp_rw [h]; split
      next=> rw [prod_insert ha,mul_assoc, show k\ insert i (token f s)= k.erase i \ token f s from ?_]; ext x; simp [and_left_comm,and_assoc]
      next=> rw [mul_zero]
    rw [if_neg ht,if_neg (fun h=> ht (h.2 (mem_insert_self ..)))]
lemma enact (a:ι)(ha:a∉s)(hv:f a=some i)(k:Finset α) : ∏ j∈k,leaf f g V (insert a s) j= (∏ j∈k,leaf f g V s j)+(if i∈k then g a*∏ j∈k.erase i,leaf f g V s j else 0):=by
    have hk(x:α)(h:x≠i) : leaf f g V (insert a s) x=leaf f g V s x:=by unfold leaf; simp [hv,sum_insert ha,h.symm]
    by_cases h:i∈k
    · rw [if_pos h,← Finset.mul_prod_erase _ (leaf f g V s) h,← Finset.mul_prod_erase _ (leaf f g V (insert a s)) h]
      have he: (∏ j∈k.erase i,leaf f g V (insert a s) j)= ∏ j∈k.erase i,leaf f g V s j:=prod_congr rfl fun j hj=>hk j (ne_of_mem_erase hj)
      rw [he,←add_mul]; apply congr_arg (·*_); unfold leaf; simp only [sum_insert ha,hv,↓reduceIte]; ring
    rw [if_neg h,add_zero]; exact prod_congr rfl fun j hj=> hk j (by intro h'; exact h (h' ▸ hj))
lemma holiday (s:Finset ι) : ∑ t∈s.powerset,chop f g V t k=
       (∏ i∈s,if f i=none then 1+g i else 1)*(∏ i∈k,leaf f g V s i):=by
   induction s using Finset.induction generalizing k with
   | empty=> simp [chop,leaf,unique,token]
   | insert a s hA hs=>
       rw [prod_insert hA, Finset.sum_powerset_insert hA (fun t=> chop f g V t k), hs k]
       cases hv:f a with
       | none=>
          have he(t:Finset ι)(h:t⊆s): chop f g V (insert a t) k=g a* chop f g V t k:=spends f g V t k a (mt (fun ha=> h ha) hA) hv -- edit
          have ht: (∑ t∈s.powerset,chop f g V (insert a t) k)=g a*∑ t∈s.powerset,chop f g V t k:=by rw [Finset.mul_sum]; exact sum_congr rfl fun j hj=> he j (mem_powerset.mp hj)
          rw [ht,hs k, show leaf f g V (insert a s)= leaf f g V s from ?_] -- rw needs simp
          · rw [if_pos rfl]; ring
          funext j; unfold leaf; simp [sum_insert hA,hv]
       | some i=>
          have he(t:Finset ι)(h:t⊆s):= yields f g V t k i a (mt (fun x=>h x) hA) hv
          rw [enact f g V s i a hA hv k]; simp only [reduceCtorEq,↓reduceIte,one_mul,mul_add]
          by_cases h:i∈k
          · have ht: (∑ t∈s.powerset,chop f g V (insert a t) k)=g a*∑ t∈s.powerset,chop f g V t (k.erase i):=by rw [Finset.mul_sum]; exact sum_congr rfl fun j hj=> (he j (mem_powerset.mp hj)).trans (if_pos h)
            rw [ht,hs,if_pos h]; ring -- edit
          rw [if_neg h,mul_zero]; have ht:(∑ t∈s.powerset,chop f g V (insert a t) k)=0:= sum_eq_zero fun j hj=>(he j (mem_powerset.mp hj)).trans (if_neg h)
          rw [ht]
end YM.RemainderComparison.Encore
