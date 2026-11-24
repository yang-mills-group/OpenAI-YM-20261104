import YM.MSbar.MeasureP.Shuttle
/-! rr < ℓ total Newton degree sequential. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Set Function Filter Lattice Whisk
open scoped Topology BigOperators
variable {α β γ:Type}[Fintype α][Fintype β]
open scoped Classical
section
variable (f:α→β→ℝ) (F:ℕ→α→β→ℝ)
noncomputable def arco (F:ℕ→α→β→ℝ) : ℕ→List α→List β→ ℝ
| 0,_,_=>0
| _+1,[],_=>1
| _+1,_::_,[]=>1
| k+1,i::l,j::m=> ∑ p∈Finset.range (k+1), F p i j*arco F (k+1-p) l m
noncomputable def scroll (F:ℕ→α→β→ℝ)(k:ℕ)(i:α)(j:β):=∑ z∈Finset.range k,F z i j
lemma franje (n:ℕ)(s:Finset ℕ)(f:ℕ→List β→ℝ) : Yarn n (fun l=>∑ i∈s,f i l) = ∑ i∈s,Yarn n (f i):=by induction n generalizing f with|zero=>rfl|succ n ih=> rw [twilled]; simp_rw [twilled n]; rw [Finset.sum_comm (s:=s)]; apply Finset.sum_congr rfl; intro z _; exact ih (fun r l=>f r (z::l))
lemma songE(k:ℕ)(i:α)(j:β)(t:List α)(r:List β): beads f (i::t) (j::r)-arco F (k+1) (i::t) (j::r)=(f i j-scroll F (k+1) i j)*beads f t r+∑ q∈Finset.range (k+1), F q i j* (beads f t r -arco F (k+1-q) t r):=by rw [arco,beads,sub_mul, scroll,Finset.sum_mul]; simp_rw [mul_sub,Finset.sum_sub_distrib]; ring
lemma lust (T:List β)(w:β→ℝ)(hw:∀ i,0≤w i):0 ≤ (T.map w).prod:=List.prod_nonneg (fun j hj=> by obtain ⟨i,_,hi⟩:= List.mem_map.mp hj; exact hi ▸ hw i)
variable (w:β→ℝ)(hw:∀ i,0≤w i)(a d:ℝ)(ha:0≤a)(hd:0≤d){k:ℕ}(x:List α)
include hw ha hd
lemma bases (h:∀ i∈x,(∑ j:β,w j*|f i j|)≤a): Yarn x.length (fun T:List β=> (T.map w).prod*|beads f x T|) ≤ a^x.length:=by
    refine le_trans (le_of_eq (stitch x.length ?_)) (bolt_bound (fun i j=>w j*|f i j|) (fun i j=>mul_nonneg (hw j) (abs_nonneg _)) x _ ha h); clear h; induction x with
    | nil=> intro T ht; rw [show T=[] by simpa using ht]; simp [beads]
    | cons i t ih=> intro T ht; cases T with
                    | nil=>simp at ht
                    | cons j T=>have he:= ih T (by simpa using ht); simp only [beads, List.map_cons,List.prod_cons, abs_mul,←he];ring
variable (k_max:ℕ) (hk:k ≤ k_max)
local notation "n📫" => ((k_max:ℝ)+1)
variable (hS:∀ i∈x,∀ k:ℕ,k≤k_max→(∑ j:β,w j*|F k i j|) ≤ a*d^k)
include hk hS
variable {f}
local notation "N"=>x.length
lemma loft (h:1 ≤ d) (he: 0<k) : Yarn x.length (fun T:List β=> (T.map w).prod*|arco F k x T|) ≤ (n📫*a)^x.length*d^(k-1):=by
    let s:= n📫; have hs: 0 ≤ s:=by unfold s; positivity
    induction x generalizing k with
    | nil=> obtain ⟨l,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : k≠0); change (List.map w []).prod*|arco F _ [] []| ≤_; simpa [arco] using (one_le_pow₀ (n:=l+1-1) h)
    | cons i x ih=>
       obtain ⟨l,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
       let Z:= x.length; let y:= (s*a)^x.length; have hy:0 ≤ y:=by unfold y; positivity
       let t:=y*d^l; have ht:0 ≤ t:=by unfold t; positivity
       have hp(q:ℕ)(hq:q∈Finset.range (l+1)):(∑ j:β, Yarn x.length fun T:List β=> ((j::T).map w).prod*(|F q i j| * |arco F (l+1-q) x T|)) ≤ a*t:=by
           let b:= l+1-q; let L(T:List β):= (T.map w).prod*|arco F b x T|; have he:= Finset.mem_range.mp hq
           have hL : Yarn x.length L ≤ y*d^(b-1):=ih (by omega) (fun i hi=>hS i (List.mem_cons_of_mem _ hi)) (by omega)
           calc
             _ ≤ ∑ j:β, w j*|F q i j| *(y*d^(b-1)):=by refine Finset.sum_le_sum fun j _=>?_ ; refine le_trans ?_ (mul_le_mul_of_nonneg_left hL (mul_nonneg (hw j) (abs_nonneg _))); rw [←sheen]; refine shiny _ fun m hm=>?_ ; unfold L; rw [List.map_cons,List.prod_cons]; exact le_of_eq (by unfold b; ring)
             _ ≤ a*d^q*(y*d^(b-1)):=by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hS i (List.mem_cons_self ..) q (by omega)) (by positivity)
             _ = _:=by unfold t; have he: d^q*d^(b-1)= d^l:= by rw [← pow_add]; unfold b; congr; omega
                       rw [←he]; ring
       let p(j:β)(T:List β)(q:ℕ):= ((j::T).map w).prod*(|F q i j| * |arco F (l+1-q) x T|)
       simp only [List.length_cons, twilled]
       calc
           _ ≤ ∑ j:β,Yarn x.length fun T:List β=> ∑ q∈Finset.range (l+1),p j T q:=by
               refine Finset.sum_le_sum fun j _=> shiny _ fun m _=> ?_; unfold p; rw [arco, ←Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (lust ..); simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (ι:=ℕ) (fun q=> F q i j*arco F (l+1-q) x m) (Finset.range (l+1)); exact hw -- lust
           _ = ∑ q∈Finset.range (l+1),∑ j:β,Yarn x.length fun T=>p j T q:=by rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=>?_ ; exact franje x.length _ (fun q T=> p j T q)
           _ ≤ ∑ _∈Finset.range (l+1),a*t:= Finset.sum_le_sum hp
           _ ≤ _:=by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_range]; have hh:(l+1:ℕ)≤k_max+1:= hk.trans (by omega)
                     apply le_trans (b:=s*(a*t)) (mul_le_mul_of_nonneg_right (by unfold s; exact_mod_cast hh) (by positivity)) (le_of_eq ?_); unfold t y s; rw [Nat.succ_sub_one,pow_succ (n:=x.length)]; ring
variable (f:α→β→ℝ)
variable (hv:∀ i∈x,(∑ j:β,w j*|f i j|) ≤ a)(ht:∀ i∈x,∀ k:ℕ,k≤k_max→(∑ j:β,w j*|f i j-scroll F k i j|) ≤ a*d^k)
include hv ht
lemma under : Yarn x.length (fun T:List β=> (T.map w).prod*|beads f x T-arco F k x T|)≤ (2*n📫*a)^x.length*d^k:=by
    let B:=2*n📫; have hB:2≤B:=by unfold B; linarith only [Nat.cast_nonneg (α:=ℝ) k_max]
    have Hb:1 ≤ n📫:=le_add_of_nonneg_left (Nat.cast_nonneg k_max)
    induction x generalizing k with
    | nil=> cases k with
           | zero=> rw [List.length_nil,Yarn]; simp [beads,arco]
           | succ k=> rw [List.length_nil,Yarn]; simp [beads,arco]; positivity
    | cons i x ih=>
       by_cases he:k=0
       · subst k; simp_rw [arco,sub_zero]; rw [pow_zero,mul_one]; apply (bases f w hw a d ha hd (i::x) hv).trans; gcongr; nth_rw 1 [← one_mul a]; gcongr; linarith
       obtain ⟨r,rfl⟩:= Nat.exists_eq_succ_of_ne_zero he; let k:=r+1
       have hc(j:α):j∈x → j∈ i::x:= fun h=>List.mem_cons_of_mem i h
       let y:=(B*a)^x.length; have hy:0≤y:=by unfold y; have h:0 ≤ B:=zero_le_two.trans hB; positivity
       let t:= a*y*d^k; have HP:0≤t:=by unfold t; positivity
       let I(j:β)(T:List β):=((j::T).map w).prod*(|f i j-scroll F k i j| *|beads f x T|)
       let J(j:β)(T:List β)(q:ℕ):=((j::T).map w).prod*(|F q i j| *|beads f x T-arco F (k-q) x T|)
       have HA:(∑ j:β,Yarn x.length (I j))≤ t:=by
           let R(j):= w j*|f i j-scroll F k i j|; have H(j):0 ≤ R j:=mul_nonneg (hw j) (abs_nonneg _)
           have hV : Yarn x.length (fun T:List β=> (T.map w).prod*|beads f x T|) ≤ y:=by apply (bases f w hw a d ha hd _ (fun i hi=>hv i (hc i hi))).trans; unfold y; exact pow_le_pow_left₀ ha (le_mul_of_one_le_left ha (one_le_two.trans hB)) x.length
           calc
             _ ≤ ∑ j:β,R j*y:= Finset.sum_le_sum fun j _=>by
                       refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hV (H j)); rw [←sheen]; refine stitch _ fun z _=>?_ ; simp only [I,List.map_cons,List.prod_cons]; unfold R; ring
             _ ≤ (a*d^k)*y:=by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (ht i (List.mem_cons_self ..) _ hk) hy
             _ = t:= by ring
       have HU(q:ℕ)(hq:q<k): (∑ j:β,Yarn x.length (fun T=>J j T q)) ≤ t:=by
           let p:=k-q; let R(j):=w j*|F q i j|; have H(j):0 ≤ R j:=mul_nonneg (hw j) (abs_nonneg _)
           have hc' : p≤k_max:= (Nat.sub_le k q).trans hk
           have hQ:Yarn x.length (fun T:List β=> (T.map w).prod*|beads f x T-arco F p x T|) ≤y*d^p:= ih hc' (fun i hi=>hS i (hc i hi)) (fun i hi=>hv i (hc i hi)) (fun i hi=>ht i (hc i hi))
           calc
             _ ≤ ∑ j:β, R j*(y*d^p):= Finset.sum_le_sum fun j _=> by
                     refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hQ (H j)); rw [←sheen]; refine stitch _ fun z _=>?_; unfold J p; simp only [List.map_cons,List.prod_cons]; unfold R; ring
             _ ≤ (a*d^q)*(y*d^p):= by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hS i (List.mem_cons_self ..) _ (hq.le.trans hk)) (by positivity)
             _ = t:=by unfold t; rw [show a*d^q*(y*d^p)= a*y*(d^q*d^p) from by ring,←pow_add,show q+p=k from Nat.add_sub_of_le hq.le] -- maybe
       rw [List.length_cons,twilled]
       calc
          _ ≤ ∑ j:β,Yarn x.length fun T:List β=> I j T+∑ q∈Finset.range k,J j T q:=by
              refine Finset.sum_le_sum fun j _=> shiny _ fun m hm=>?_ ; unfold J I; rw [←Finset.mul_sum,←mul_add,songE]; refine mul_le_mul_of_nonneg_left ((abs_add_le ..).trans (add_le_add ?_ ?_)) (lust _ _ hw)
              · rw [abs_mul]
              · simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun q:ℕ=>F q i j*(beads f x m-arco F (k-q) x m)) (Finset.range k)
          _ = (∑ j:β,Yarn x.length (I j))+∑ q∈Finset.range k,∑ j:β,Yarn x.length fun T=>J j T q:=by rw [← Finset.sum_comm (s:=Finset.univ (α:=β)) (t:=Finset.range k),←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [pockets]; congr 1; exact franje _ _ (fun q T=>J j T q)
          _ ≤ t+∑ q∈Finset.range k,t:= add_le_add HA (Finset.sum_le_sum fun q hq=>HU q (Finset.mem_range.mp hq))
          _ ≤ _:= by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_range]; change _ ≤ (B*a)^(_+1)*d^k
                     calc
                       _ ≤ B*t:= by rw [← one_add_mul]; gcongr; unfold B; linarith only [Hb,(show (k:ℝ) ≤ k_max by exact_mod_cast hk)]
                       _ = _:= by unfold t y; rw [pow_succ (n:=x.length)];ring
end
end YM.MSbar.Measuring
