import YM.Contacts.Pulse.Pen
/-! extraction of labelled ranks using partials. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Set Filter Finset RG MvPolynomial
open scoped Classical BigOperators Topology NNReal
variable {ι κ α β : Type*} {n : ℕ}
def notch (x : α) (F:Field (Fin (n+1)) α) : Field (Fin n) α:= fun y=> F (Fin.cons x y)
lemma Poem.notched {F : Field (Fin (n+1)) α}(h:Poem F)(x:α): Poem (notch x F) := by
  intro p y; unfold notch; rw [← h (((finSuccEquiv n).trans (Equiv.optionCongr p)).trans (finSuccEquiv n).symm) (Fin.cons x y)]; congr 1; ext1 i; refine Fin.cases ?_ (fun i=>?_) i <;> simp
lemma Poem.handoff {F : Field (Fin (n+2)) α}(h:Poem F)(x y:α): notch y (notch x F)=notch x (notch y F) := by
  ext1 p; unfold notch; rw [← h (Equiv.swap 0 (Fin.succ 0))];
  apply congr_arg; ext1 i; refine Fin.cases ?_ (fun i=> Fin.cases ?_ (fun i=>?_) i) i
  · simp
  · simp
  have ha : i.succ.succ≠Fin.succ (0:Fin (n+1)):= by exact fun h => Fin.succ_ne_zero i (Fin.succ_inj.mp h)
  simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ha,Fin.cons_succ]

variable [Fintype α]
lemma verse_nil (F:Field (Fin 0) α) : verse F= C (F (fun i=> i.elim0)):= by unfold verse; rw [@Fintype.sum_unique]; simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]; exact congr_arg (fun x=> C (F x)) (Subsingleton.elim ..)
lemma verse_up (F:Field (Fin (n+1)) α) : verse F= ∑ i, (X i) * verse (notch i F):=by
  unfold verse; classical
  have := Equiv.sum_comp (Fin.consEquiv (fun _:Fin (n+1)=>α)) (fun x=> C (F x)* ∏ i:Fin (n+1),X (x i))
  trans ∑ x:α× (Fin n→α), C (F ((Fin.consEquiv (fun _:Fin (n+1)=> α)) x))* ∏ j, X ((Fin.consEquiv (fun _:Fin (n+1)=>α)) x j)
  · convert! this.symm using 1; congr 1; exact congr_arg (fun i : Fintype _ => @Finset.univ _ i) (Subsingleton.elim ..)
  rw [Fintype.sum_prod_type]; simp_rw [mul_sum];
  apply sum_congr rfl; intro i _; refine Finset.sum_congr ?_ ?_; 
  · exact congr_arg (fun i : Fintype _ => @Finset.univ _ i) (Subsingleton.elim ..)
  intro j _
  change C (F (Fin.cons i j)) * _= _; rw [Fin.prod_univ_succ]; dsimp only [Fin.consEquiv,Equiv.coe_fn_mk, Fin.cons_zero,Fin.cons_succ,notch]; ring_nf; simp
private lemma jumping (i:α) (F: Field (Fin (n+1)) α): pderiv i (verse F)=verse (notch i F) + ∑ j, X j * pderiv i (verse (notch j F)) := by
    rw [verse_up,map_sum]; simp_rw [pderiv_mul,sum_add_distrib]; rw [sum_eq_single_of_mem i (mem_univ _)]; swap
    · intro a _ h; rw [pderiv_X_of_ne h,zero_mul]
    rw [pderiv_X_self,one_mul]
lemma verse_pderiv {F:Field (Fin (n+1)) α}(h:Poem F)(i:α) : pderiv i (verse F)=((n:ℕ)+1:ℕ) • verse (notch i F):= by
  induction n with
  | zero=>
    rw [jumping]; simp [verse_nil]
  | succ n ih=>
    rw [jumping]
    conv_lhs => rhs; arg 2; intro j; rw [ih (h.notched j), h.handoff j i]
    simp_rw [mul_smul_comm,← Finset.smul_sum,←verse_up]; module
lemma unique_poem {F H:Field (Fin n) α}(h:Poem F)(hp:Poem H)(he:verse F=verse H): F=H:= by
  induction n with
  | zero => funext t; rw [verse_nil,verse_nil] at he; exact Subsingleton.elim t (fun i=> i.elim0) ▸ (C_injective α ℝ he)
  | succ n ih =>
    funext x; rw [← Fin.cons_self_tail x]; have hv i:= congr_arg (pderiv i) he
    have hh i: notch i F=notch i H:= ih (h.notched i) (hp.notched i) (nsmul_right_injective (by omega: n+1 ≠ 0) (show (n+1) • _ = (n+1:ℕ) • _ from (verse_pderiv h i).symm.trans ((hv i).trans (verse_pderiv hp i))))
    exact congr_fun (hh (x 0)) (Fin.tail x)
end YM.Pulse
