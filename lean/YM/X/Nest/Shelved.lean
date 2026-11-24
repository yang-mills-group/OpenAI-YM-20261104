import YM.X.Nest.Gram
/-!
# Reap budget at standard points. Can send a shelf-program to helper subalgebra of Tape. no geometry-specific assumptions.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Asymptotics Reed Braid Finset
open scoped Topology ContDiff BigOperators Classical
variable {V I T:Type*} {i k d:ℕ}
local notation "L"=> Stella V T
local notation "ℙ"=> Code V T
variable (B:Subalgebra ℂ (T→ℂ)) (C':Submodule ℂ (T→ℂ))(Q:T→ Symmetric V) [DecidableEq I]
variable (S:Finset I)(u:I→ Set (Stella V T)) (p:Code V T) (f:I→ Code V T)
def swarm : List (Stella V T)→ℙ→ℙ | [],p=>p | x::l,p=> swarm l (stream Q x p) -- explicit Q arg recursion?
def fleet (p:Code V T): T→ℂ:= fun t=> (aeval (0:V→ℂ)) (p t)
def Condition : Prop:= ∀ l:List L,(∀ a∈l,∃ i∈S,a∈u i)→ fleet (swarm Q l p) ∈ C'
lemma stepW (h:Condition C' Q S u p) (v:Stella V T){i:I}(hh:i∈S)(he:v∈u i): Condition C' Q S u (stream Q v p):= by intro l hp; refine h (v::l) ?_; intro b hx; obtain rfl|hk:=List.mem_cons.mp hx; exact ⟨i,hh,he⟩; apply hp _ hk
lemma sp_free(h:Condition C' Q S u p):fleet p∈ C':= h [] (by simp)
lemma laps {g:I→ Code V T}(hh:∀ i∈S,f i=g i): lap S Q f p= lap S Q g p:= by ext1 t; unfold lap drip; rw [spiro.surge _ _ _ (fun i hi=>congr_fun (hh i hi) t)]
lemma lap_zero {i:I}(h:i∈S): lap S Q (Function.update f i 0) p=0:= by funext t; simp only [lap,drip,commute_update,spiro.pulse _ _ _ _ h,Pi.zero_apply,pzero,map_zero]
lemma lapS {i:I}(h:i∈S)(x:Code V T)(t:ℂ): lap S Q (Function.update f i (t • x)) p=t • lap S Q (Function.update f i x) p:= lap_smul S Q f p h (fun _:T=> t) x
variable {B C' Q p S u f}
abbrev Allows (B:Subalgebra ℂ (T→ℂ))(C':Submodule ℂ (T→ℂ)):= ∀ (x y:T→ℂ), x∈B→y∈C'→ x*y∈C'
abbrev Isolation (B:Subalgebra ℂ (T→ℂ))(Q:T→Symmetric V)(S:Finset I)(u:I→Set (Stella V T)) :=∀ i∈S,∀ j∈S,j≠i→∀ v∈u i,∀ x∈u j,cross Q v x∈B
private lemma restoreT (hA:Allows B C')(hC:Condition C' Q S u p) (hf:∀ i∈S,f i∈ Bag B (u i) 0):lap S Q f p ∈ C':= by
   let g(i:I):= if hi:i∈S then ⟨(Bag.retire _ (hf i hi)).choose, (Bag.retire _ (hf i hi)).choose_spec.1⟩ else (0:B)
   have hp:= hA _ _ (B.prod_mem (f:=fun i=>(g i).val) (t:=S) (fun i _=>(g i).property)) (sp_free _ _ _ _ _ hC); rw [laps Q S p f (g:=fun i t=> MvPolynomial.C ((g i).val t)) (fun i hi=>?_ ),lap_none]; exact hp; rw [show g i= _ from dif_pos hi]; exact (Bag.retire _ (hf i hi)).choose_spec.2
-- dynamic support grammar
lemma visits (hA:Allows B C')(hI:Isolation B Q S u)(hC:Condition C' Q S u p) (hf:∀ i∈S,∃ k:ℕ,f i∈Bag B (u i) k):lap S Q f p∈ C':= by
    have ht(k:ℕ): ∀ d:I→ℕ,k=∑ x∈S,d x→ ∀ (p:Code V T)(f:I→Code V T),Condition C' Q S u p→ (∀ i∈S,f i∈Bag B (u i) (d i))→lap S Q f p∈C':= by
       induction k using Nat.strong_induction_on with
       | h k IH=>
          intro d he p f hc hf
          by_cases hx:∀ i∈S,d i=0
          · exact restoreT hA hc fun i hi=> hx _ hi ▸ hf i hi
          push_neg at hx; obtain ⟨i,hi,hdi⟩:=hx; let m:=d i-1; let D:= Function.update d i m
          have hk: (∑ j∈ S,D j)<k:= by rw [he]; exact Finset.sum_lt_sum (fun i' _=> by
               by_cases he:i'=i; · subst i'; simp [D,m]
               rw [show D i'=d i' from Function.update_of_ne he ..]) ⟨i,hi,by unfold D m;rw [Function.update_self]; omega⟩
          let H:= IH _ hk D rfl
          let bagged(g:I→Code V T):=∀ i∈S,g i∈ Bag B (u i) (D i);
          have ha(x:Code V T)(h:x∈Bag B (u i) m): bagged (Function.update f i x):= by
              intro j hj; by_cases hx:j=i; · subst j; simpa [D] using h
              rw [Function.update_of_ne hx, show D j=d j from Function.update_of_ne hx ..]; apply hf _ hj
          let LH(x:Code V T):= lap S Q (Function.update f i x) p; suffices hp : ∀ x∈ Bag B (u i) (d i), LH x∈ C' by rw [← lap_pos S Q f p i _ rfl]; exact hp _ (hf i hi)
          intro x hx; induction hx using Submodule.span_induction with
          | mem a hx=>
              obtain ⟨l,b,a,c,hx,rfl⟩:=hx; rcases l with _|⟨v,l⟩;
              · exact H _ _ hc (ha _ (bag B (u i) m [] b c a (Nat.zero_le _)))
              let g:= Function.update f i (charge b * thing l); have hb : bagged g:= ha _ (bag B (u i) m l b c (fun i h=>a i (List.mem_cons_of_mem v h)) (by rw [List.length_cons] at hx; unfold m; omega)); unfold LH; rw [thing_cons, mul_left_comm];
              have hw(u:I)(b:Code V T): Function.update f i b=Function.update g i b:= by unfold g; rw [Function.update_idem]; -- name
              rw [hw i,show charge b*thing l=g i from by unfold g;rw [Function.update_self]]; change lap S Q (Function.update g i ((glyph∘ v)*g i)) p ∈ C'; rw [lap_step S Q g p v hi]; apply C'.add_mem (H _ _ (stepW _ _ _ _ _ hc v hi (a _ (by simp))) hb)
              refine C'.sum_mem (fun j hj=> H p _ hc ?_); intro z hz; by_cases hp:z=j; · subst z; rw [Function.update_self]; exact (Bag.static_cost Q (g j) v (fun q he=> hI i hi j hz (mem_erase.mp hj).1 _ (a _ (by simp)) q he) (hb _ hz))
              rw [Function.update_of_ne hp];apply hb _ hz
          | zero=>rw [show LH 0=0 from lap_zero Q S p f hi] ; exact C'.zero_mem
          | add a b _ _ x y=> unfold LH;rw [lap_add];exact C'.add_mem x y;exact hi
          | smul a k _ t=> unfold LH;rw [lapS];exact C'.smul_mem a t;exact hi
    choose! d hd using hf; exact ht _ d rfl p f hC hd
end YM.PositionX.Crate
