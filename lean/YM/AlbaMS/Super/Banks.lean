import YM.AlbaMS.Super.Mote

/-! Euler, rank, local generators. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R E W : Type*} [CommRing R] [AddCommMonoid W] {ρ : ι→Bool} (p q : Bool)
variable (F G H : Coil ρ R) {l : List ι} (x y : ι) (s : Set ι) (n : ℕ)
namespace Coil

-- general split lemma independent of signs. local order support predicates
lemma occurred (h : (F*G) l≠0) : ∃ a b, (F a)≠0 ∧ G b≠0 ∧ l.Perm (a++b) := by
  induction l generalizing F G with
  | nil=> exact ⟨[],[],left_ne_zero_of_mul (b:=G []) h,right_ne_zero_of_mul (a:=F []) h,List.Perm.refl _⟩
  | cons i l ih=>
    rw [mul_cons] at h; by_cases he : (D i F*G) l=0
    · rw [he,zero_add] at h; obtain ⟨a,b,hf,hg,hh⟩:= ih _ _ h
      refine ⟨a,i::b,fun hv=> hf (by rw [polar,hv,sting_zero]),hg,?_⟩; exact (hh.cons i).trans (List.perm_middle.symm)
    obtain ⟨a,b,hf,hg,hh⟩:= ih _ _ he; exact ⟨i::a,b,hf,hg,hh.cons i⟩

def Inside (s : Set ι) (F : Coil ρ R) : Prop := ∀ l, F l≠0→ ∀ x ∈ l,x∈s
def Cap : Prop := ∀ l,F l≠0→ l.length ≤ n
-- rank negative purpose tracked by bound predicate
namespace Inside
variable {s F G H}
lemma weak {t} (h:t⊆s)(ht:Inside t F): Inside s F:= fun _ hv _ hm=> h (ht _ hv _ hm)
lemma from_all (F : Coil ρ R): Inside univ F:=fun _ _ _ _=> trivial
lemma const (c:R): Inside s (put ρ c):=by intro l hv x hm; cases l; exact False.elim (List.not_mem_nil hm);exact False.elim (hv rfl)
lemma one : Inside s (1:Coil ρ R):=const 1
lemma zero : Inside s (0:Coil ρ R):= fun _ h=>False.elim (h rfl)
lemma add (h:Inside s F)(t:Inside s G): Inside s (F+G):=by
  intro l hv x hm; by_cases hh : F l=0; exact t l (fun hu=> hv (by simp [hh,hu])) x hm; exact h l hh x hm
lemma smul (h:Inside s F)(c:R): Inside s (c • F):= fun l hv => h l (fun hu=> hv (by simp [hu]))
lemma neg (h:Inside s F): Inside s (-F):= fun l hv => h l (fun hu=> hv (by simp [hu]))
lemma sub (h:Inside s F)(t:Inside s G): Inside s (F-G):= sub_eq_add_neg F G ▸ h.add t.neg
lemma sum (v : Finset E) (f : E→ Coil ρ R) (h : ∀ i∈v, Inside s (f i)): Inside s (∑ i∈v,f i):=by
  induction v using Finset.induction_on with|empty=> simp [zero]|@insert i t ht IH=> rw [Finset.sum_insert ht]; apply add (h i (by simp)) (IH (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma dz (h:Inside s F)(x:ι): Inside s (D x F):= fun l hv y hy => h (x::l) hv y (List.mem_cons_of_mem _ hy)
lemma erased (h:Inside s F){x}(hh:x ∉ s): D x F=0:= ext _ _ (fun l=> not_not.1 fun (hv:F (x::l)≠0)=> hh (h _ hv x (by simp)))
lemma mul (h:Inside s F)(e:Inside s G): Inside s (F*G):=by
  intro l hv x hm; obtain ⟨a,b,hf,hg,he⟩:= occurred F G hv; rw [he.mem_iff,List.mem_append] at hm; exact hm.elim (h _ hf x) (e _ hg x)
end Inside
namespace Cap
variable {n F G H} {m : ℕ}
lemma up (h:Cap F n)(H:n≤m):Cap F m:= fun _ hv=> (h _ hv).trans H -- confirm order
lemma zero : Cap (0:Coil ρ R) n:=fun _ h=>False.elim (h rfl)
lemma const (c:R): Cap (put ρ c) n:=by intro l hv; cases l; exact Nat.zero_le _; exact False.elim (hv rfl)
lemma one : Cap (1:Coil ρ R) n:=const 1
lemma add (h:Cap F n)(hv: Cap G n): Cap (F+G) n:=by
  intro l he; by_cases ht:F l=0; exact hv l (fun hl=> he (by simp [hl,ht])); exact h l ht
lemma smul (h:Cap F n) (c:R): Cap (c • F) n:=fun l hv=> h l (fun hl=> hv (by simp [hl]))
lemma neg (h:Cap F n): Cap (-F) n:= fun l hv=> h l (fun hl=> hv (by simp [hl]))
lemma sub (h:Cap F n)(H:Cap G n): Cap (F-G) n:=sub_eq_add_neg F G ▸ h.add H.neg
lemma sum (v : Finset E) (f : E→ Coil ρ R) (h : ∀ i∈v, Cap (f i) n): Cap (∑ i∈v,f i) n:=by
  induction v using Finset.induction_on with|empty=>simp [zero]|@insert i t ht IH=> rw [Finset.sum_insert ht]; apply add (h i (by simp)) (IH (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma dz (h:Cap F (n+1)): Cap (D x F) n:= fun l hv=> Nat.le_of_succ_le_succ (h (x::l) hv)
lemma eroded (h:Cap F 0): F=put ρ (F []):=by ext l; cases l; rfl; next=> apply not_not.1; intro hh; have hc:= h _ hh; simp at hc
lemma mul (h:Cap F m)(H:Cap G n):Cap (F*G) (m+n):=by intro l hv; obtain ⟨a,b,ha,hb,he⟩:=occurred F G hv; rw [he.length_eq,List.length_append]; exact Nat.add_le_add (h a ha) (H b hb)
end Cap

def weight (f : ι→W)(l : List ι) := (l.map f).sum
def Pure (f : ι → W) (w : W) (F : Coil ρ R) : Prop := ∀ l, F l≠0→ weight f l=w
@[simp] lemma cons_weight (f:ι→W) : weight f (x::l)=f x+weight f l:=by simp [weight]
@[simp] lemma app_weight (f:ι→W) (a b : List ι) : weight f (a++b)=weight f a+weight f b:=by simp [weight]
lemma perm_weight (f:ι→W){a b : List ι}(h:a.Perm b): weight f a=weight f b:= (h.map f).sum_eq
namespace Pure
variable {f : ι→ W} {w u : W} {F G}
lemma zero : Pure f w (0:Coil ρ R):=fun _ h=>False.elim (h rfl)
lemma const (c:R): Pure f 0 (put ρ c):=by intro l hv; cases l; rfl; exact False.elim (hv rfl)
lemma one : Pure f 0 (1:Coil ρ R):=const 1
lemma add (h:Pure f w F)(H:Pure f w G): Pure f w (F+G):=by
  intro l he; by_cases ht:F l=0; exact H l (fun hl=> he (by simp [hl,ht])); exact h l ht
lemma smul (h:Pure f w F)(c:R): Pure f w (c • F):=fun l hv=> h l (fun hl=> hv (by simp [hl]))
lemma neg (h:Pure f w F): Pure f w (-F):= fun l hv=> h l (fun hl=> hv (by simp [hl]))
lemma sub (h:Pure f w F)(H:Pure f w G): Pure f w (F-G):=sub_eq_add_neg F G ▸ h.add H.neg
lemma sum (v : Finset E) (g : E→ Coil ρ R) (h : ∀ i∈v, Pure f w (g i)): Pure f w (∑ i∈v,g i):=by
  induction v using Finset.induction_on with|empty=>simp [zero]|@insert i t ht IH=> rw [Finset.sum_insert ht]; apply add (h i (by simp)) (IH (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma mul (h:Pure f w F)(H:Pure f u G): Pure f (w+u) (F*G):=by intro l hv; obtain ⟨a,b,ha,hb,he⟩:=occurred F G hv; rw [perm_weight f he, app_weight,h _ ha,H _ hb]
lemma dz [IsLeftCancelAdd W] (h:Pure f (f x + w) F) : Pure f w (D x F):=by intro l he; have ht := h (x::l) he; rw [cons_weight] at ht; exact add_left_cancel ht
end Pure

-- projection onto set of words
def sift (u : List ι→Prop) (h : ∀ a b,a.Perm b→u a→u b) : Coil ρ R→ₗ[R] Coil ρ R where
  toFun F:= ⟨fun l=> if u l then F l else 0, fun (a l : List ι) (i j : ι)=>show ite (u _) (F (a++i::j::l)) 0=sting (ρ i && ρ j) (ite (u _) (F (a++j::i::l)) 0) from by
    have he : u (a++i::j::l) ↔ u (a++j::i::l):= ⟨h _ _ (List.Perm.append_left _ (.swap ..)),h _ _ (List.Perm.append_left _ (.swap ..))⟩
    simp only [he]; split <;> first| exact F.trusted ..| exact (sting_zero _).symm ⟩
  map_add' F G:= ext _ _ (fun l=>by change ite (u l) (_+_) 0=ite (u l) (F l) 0+ite (u l) (G l) 0; split <;> first|rfl|simp)
  map_smul' c F:= ext _ _ (fun l=>by change ite (u l) _ 0=c*ite (u l) _ 0; split <;> first|rfl|simp)

def rankn (n : ℕ) : Coil ρ R→ₗ[R] Coil ρ R:=sift (fun l=> l.length=n) (fun _ _ h e=> h.length_eq.symm.trans e)
lemma rankn_read : rankn n F l=if l.length=n then F l else 0:= by change @ite R _ (Classical.propDecidable _) _ _ = _; congr
lemma D_rank (F : Coil ρ R): D x (rankn (n+1) F)= rankn n (D x F):= by ext l; simp only [rankn_read,D_read,List.length_cons,Nat.add_right_cancel_iff]
end Coil
end YM.MSBar.Bric
