import YM.MSbar.Pole.Scale.Monomial
/-! # Log form of each Taylor coefficient at a flow value -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Curtain
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I] {A : Finset I} {d:Age}
lemma stories {C D:ℕ → ℝ → Cloud I} (k : ℕ) : polar k (C+D)=polar k C+ polar k D:= by
  funext r z n x; simp only [Pi.add_apply,polar,purePolar,Finset.sum_apply,Pi.smul_apply,smul_add,Finset.sum_add_distrib]

lemma portrait (A : Finset I) (d:Age) {G : ℂ→Cloud I} {k:ℕ} (h : Vortex k G) : ∃ C : ℕ→ℝ → Cloud I,
    (∀ i,Ledger A d.a (C i)) ∧ (∀ i≥k, C i=0) ∧ Soft ((fun r=>roll A d r G)-polar k C):=by
  induction k generalizing G with
  | zero=>
    refine ⟨0,fun _=>Ledger.zero,fun _ _=>rfl,Soft.backside (rolled A d h) ?_⟩; intro; intro; intro; intro; funext n x; simp [polar]
  | succ i ih=>
    obtain ⟨f,hh,hG⟩:= remove h
    let F : ℂ→ Cloud I:=fun z=>z⁻¹^(i+1) • f
    obtain ⟨C,hc,ht,hq⟩:= ih hG
    let E(z:ℂ) := Complex.exp (d.linear*z)
    obtain ⟨D,hd,hp⟩:= raised (i+1) 0 hh (show Differentiable ℂ E from by unfold E; fun_prop) A d
    let W j:= if j≥i+1 then 0 else (C+D) j; refine ⟨W,fun j=>?_,fun _ hj=>if_pos hj,?_⟩
    · by_cases hz:j≥i+1
      · rw [show W j=0 from if_pos hz]; apply Ledger.zero
      rw [show W j=(C+D) j from if_neg hz]; exact Ledger.merge (hc _) (hd _)
    apply Soft.backside (Soft.add (show Soft ((fun s=>roll A d s (G-F))-polar i C) from hq) hp)
    intro r z hr hz; funext n x
    have hK : polar (i+1) W r z n x = polar i C r z n x+ polar (i+1) D r z n x := by
      rw [show polar (i+1) W = polar (i+1) (C+D) by funext r; exact ext_cut _ _ _ (fun j hj=>congr_fun (show W j=(C+D) j from if_neg hj.not_ge) r),stories, show polar (i+1) C=polar i C by funext r z n x; simp [polar,purePolar_up,ht i le_rfl] ]; rfl
    have hB : (r:ℂ)^(d.alpha z) = (r:ℂ)^d.a * E ((Real.log r:ℂ)*z) := by
      have hv : (r:ℂ)≠0:= by exact_mod_cast hr.ne'
      rw [alpha,Complex.cpow_add _ _ hv,Complex.cpow_intCast,Complex.cpow_def_of_ne_zero hv]; rw [Complex.ofReal_log hr.le]; unfold E; ring_nf
    simp only [Pi.add_apply,Pi.sub_apply,roll,F, evaluate,hK,hB,Pi.smul_apply, smul_eq_mul]; ring

lemma arrange {Z : Type*} (s : Finset Z) (l : Z → ℕ) (a:ℤ) (A : Finset I) {k:ℕ} {F : Z → ℂ → Cloud I} (h : ∀ z∈s,Vortex k (F z)) :
    ∃ C : ℕ→ℝ→ Cloud I,(∀ i,Ledger A a (C i)) ∧ Soft ((∑ z∈s, fun r=>roll A ⟨a,l z⟩ r (F z))-polar k C):=by
  induction s using Finset.induction_on with
  | empty=> refine ⟨0,fun _=>Ledger.zero, ?_⟩; refine Soft.backside (Soft.zero (I:=I)) ?_; intros; funext n x; simp [polar,purePolar]
  | @insert i s hs ih=>
    obtain ⟨C,hc,hq⟩:= ih fun z hz=> h z (Finset.mem_insert_of_mem hz)
    obtain ⟨D,hd,-,hk⟩:= portrait A ⟨a,l i⟩ (h i (Finset.mem_insert_self ..)); refine ⟨D+C,fun j=> Ledger.merge (hd _) (hc _),?_⟩
    rw [Finset.sum_insert hs,stories]; convert! hk.add hq using 1; abel
end YM.MSbar.Pole.Curtain
