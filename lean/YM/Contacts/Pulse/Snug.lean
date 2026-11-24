import YM.Contacts.Pulse.Group
/-! # Cole-Hopf finite calculation: time-homogeneous positive coupling grade.

r=0 infinite-volume values PADDED: never use those scalar zero-rank entries
in any claim of summability. Cover recursion is defined by these r>=1 entries,
full finite period recursion includes r=0 vacuum (positive grade, constants
remain retained until numerator accounting). -/
set_option autoImplicit false
noncomputable section
namespace YM.Pulse
open Function Set Filter Finset RG
open scoped BigOperators Topology Classical NNReal
variable {α : Type*} {n p q a e : ℕ} (g:α→α→ℝ)

abbrev Rack (α : Type*) := (r:ℕ) → Field (Fin r) α
def takeRank {p q:ℕ} (h:p=q) (F:Field (Fin p) α) : Field (Fin q) α := h ▸ F
def light (g:α→α→ℝ)(r p q:ℕ) (F : Rack α)(H : Rack α) := if h:p+q=r then takeRank h (meter g (F (p+1)) (H (q+1))) else 0
def listPay (g:α→α→ℝ)(F H : Rack α)(r:ℕ) := ∑ p∈ Finset.antidiagonal r, light g r p.1 p.2 F H
def wake (g:α→α→ℝ)(F:ℕ→ ℕ→ Rack α) (e m r:ℕ): Field (Fin r) α:= degree g (F m e (r+2))+∑ p∈antidiagonal e, ∑ q ∈ antidiagonal m, listPay g (F q.1 p.1) (F q.2 p.2) r
private lemma wake_agrees {X Y:ℕ→ℕ→Rack α}(h:∀ i≤n,X i=Y i) : wake g X e n a=wake g Y e n a:= by
  unfold wake; apply congr_arg₂ (·+·) (by rw [h n le_rfl]) (sum_congr rfl fun p hp=>sum_congr rfl fun j hj=>?_); have he :=mem_antidiagonal.mp hj; rw [h j.1 (by omega),h j.2 (by omega)]

def gathering (g:α→α→ℝ)(F:ℕ→Rack α) : ℕ → ℕ → Rack α
 | 0=> F
 | t+1=> fun e r=> ((t+1:ℕ):ℝ)⁻¹ • wake g (fun i=> if _h:i < t+1 then gathering g F i else 0) e t r
termination_by t=>t
lemma gathering_start (F : ℕ→Rack α) : gathering g F 0 = F:=by rw [gathering]
lemma gathering_next (F:ℕ→ Rack α) : gathering g F (n+1) e= fun r=> ((n+1:ℕ):ℝ)⁻¹ • wake g (gathering g F) e n r:=by
    funext r; rw [gathering]; apply congr_arg (fun x: Field (Fin r) α=> ((n+1:ℕ):ℝ)⁻¹ • x); apply wake_agrees g; intro i hi; exact (dif_pos (by omega))

@[simp] lemma print_zero {ι : Type*} [Fintype ι]: printRun (0:Field ι α)=0:= by ext1 x; simp [printRun,reorder]
@[simp] lemma light_close_left {F H:Rack α}(h:F (p+1)=0): light g n p q F H=0 := by
  unfold light; split
  next he=>
     subst n; rw [h]; dsimp only [takeRank]; unfold meter; have hS: stitch g (squeeze (0: Field (Fin (p+1)) α)) (squeeze (H (q+1))) = 0:=by ext x; simp [stitch,squeeze,reorder]
     rw [hS]; simp [show reorder finSumFinEquiv (0:Field (Fin p ⊕ Fin q) α)=0 from rfl]
  rfl
@[simp] lemma light_close_right {F H:Rack α}(h:H (q+1)=0): light g n p q F H=0 := by
  unfold light; split
  next e=>
     subst n; rw [h]; unfold meter; have hS : stitch g (squeeze (F (p+1))) (squeeze (0: Field (Fin (q+1)) α))=0:=by ext x; simp [stitch,squeeze,reorder]
     dsimp only [takeRank]; rw [hS]; simp [show reorder finSumFinEquiv (0:Field (Fin p ⊕ Fin q) α)=0 from rfl]
  rfl
@[simp] lemma nova : degree g (0:Field (Fin (n+2)) α)=0:= by
  have ht : loop g (sway (0:Field (Fin (n+2)) α))=0:=by ext x; simp [loop,sway,reorder];
  rw [degree,ht,print_zero,smul_zero]
private lemma run_even {c r:ℕ}(h:c=r)(F:Field (Fin c) α)(hf:Poem F) : Poem (takeRank h F):= by subst r; exact hf
structure Snug (F:ℕ→ Rack α) : Prop where
  poems (e r:ℕ): Poem (F e r)
  thin e r : e=0∨e+2<r →F e r=0
variable {F:ℕ→ Rack α}
lemma wake_evened (X:ℕ→ℕ→Rack α): Poem (wake g X e n p):= by
   refine Poem.add ((print_even _).scale _) (Poem.sum _ fun v _=> Poem.sum _ fun w _=> Poem.sum _ fun j _=> ?_)
   unfold light; split; exact run_even _ _ ((print_even _).scale _); exact Poem.empty
lemma Snug.bounded (h:Snug F) (n:ℕ) : Snug (gathering g F n) := by
   induction n using Nat.strongRecOn with | _ n ih =>
   cases n with
   | zero=> rwa [gathering] --
   | succ t=>
     constructor
     · intro e r; rw [gathering_next]; exact  (wake_evened g (gathering g F) (e:=e) (p:=r)).scale _
     intro e r he; rw [gathering_next]; dsimp only; unfold wake; rw [(ih t (by omega)).thin e (r+2) (by omega), nova,Finset.sum_eq_zero, add_zero,smul_zero]; intro p hp; apply Finset.sum_eq_zero; intro q hq; unfold listPay; apply Finset.sum_eq_zero; intro u hu
     have := mem_antidiagonal.mp hu; have := mem_antidiagonal.mp hq; have := mem_antidiagonal.mp hp
     by_cases hl : p.1=0 ∨ p.1+2<u.1+1
     · exact light_close_left g ((ih q.1 (by omega)).thin _ _ hl)
     exact light_close_right g ((ih q.2 (by omega)).thin _ _ (by omega))
lemma Snug.timed (h:Snug F) (t e r:ℕ) (hp: 3*e<r+2*t): gathering g F t e r=0:= by
   induction t using Nat.strongRecOn generalizing e r with | _ t ih=>
   cases t with
   | zero=> rw [gathering]; exact h.thin _ _ (by omega)
   | succ t=>
     rw [gathering_next]; dsimp only; unfold wake; rw [ ih t (by omega) e (r+2) (by omega),nova,Finset.sum_eq_zero,add_zero,smul_zero]; intro p hp; apply Finset.sum_eq_zero; intro q hq; unfold listPay; apply Finset.sum_eq_zero; intro u hu
     have := mem_antidiagonal.mp hu; have := mem_antidiagonal.mp hq; have := mem_antidiagonal.mp hp
     by_cases he : 3*p.1 < (u.1+1)+2*q.1
     · exact light_close_left g (ih _ (by omega) _ _ he)
     exact light_close_right g (ih _ (by omega) _ _ (by omega))
end YM.Pulse
