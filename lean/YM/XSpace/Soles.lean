import YM.XSpace.Sandal
import YM.Next.RANK.Sky

/-!
# Difference remainder bounds for low order potential jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Litter
open Lattice Sail Next.Rank.Beamer Function Set
open scoped Topology BigOperators
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]{d k:ℕ}
lemma past_stepping (z:Cover) : z=0 ∨ ∃ p : Cover, street p+1=street z ∧ reach p≤reach z ∧ ∃ i,z=p+step i∨ p=z+step i := by
  have lh (z: Cover)(i:Axis)(h:0<z i): reach (z-step i) ≤ reach z:= by obtain ⟨j,hj⟩:= reached (z-step i); have hh:=reach_at z j; rw [← hj]; simp only [Pi.sub_apply,step_apply]; split_ifs with H ; subst j; omega; omega
  by_cases h : z=0; exact Or.inl h
  right; obtain ⟨i,hi⟩ := Function.ne_iff.mp h; change z i ≠ 0 at hi
  rcases lt_or_gt_of_ne hi with h|h
  · refine ⟨z+step i,?_,?_,i,Or.inr rfl⟩
    · rw [← mirror_road z, ← mirror_road (z+_), neg_add, ← sub_eq_add_neg]; exact once_road _ (by exact neg_pos.mpr h)
    rw [← reach_neg z, ← reach_neg (z+_), neg_add, ← sub_eq_add_neg]; exact lh _ _ (by exact neg_pos.mpr h)
  exact ⟨z-step i, once_road z h, lh z i h, i, Or.inl (sub_add_cancel ..).symm⟩
lemma street_price (x:Cover):street x ≤4*reach x:= (Finset.sum_le_sum (g:=fun _=>reach x) (fun i _=>reach_at x i)).trans_eq (by simp)

private lemma sole (A:Cover→F)(B:ℝ)(hB:0≤B)(r:ℕ)(ht:∀ l:List Axis,l.length<d→crack l A 0=0)(H:∀ (l:List Axis),l.length=d→∀ x:Cover,reach x≤r→ ‖crack l A x‖ ≤ B) : ∀ (l:List Axis), l.length≤d→∀ x:Cover,reach x≤r → ‖crack l A x‖ ≤ (4*(r:ℝ))^(d-l.length)*B:=by
  intro l hk
  generalize hp : l.length=i at hk ⊢
  induction hk using Nat.decreasingInduction generalizing l with
  | self=> exact fun x hx=> by simpa using H l hp x hx
  | of_succ i hi IH=>
    intro x hx; let P:ℝ:=(4*(r:ℝ))^(d-(i+1))*B; have hP:0≤P:=by unfold P; positivity
    let X:=crack l A
    have he (x:Cover)(k:Axis)(hx:reach x≤r):‖Δf k X x‖≤P:= IH (k::l) (by simp [hp]) x hx
    have log (n:ℕ)(p : Cover) (hs:street p=n)(hp':reach p ≤ r) : ‖X p‖ ≤ n*P:=by
      induction n generalizing p with
      | zero=> obtain h|⟨z,hz,_⟩:=past_stepping p
               · rw [h, show X 0=_ from ht l (by omega)]; simp
               omega
      | succ n ih=>
        obtain h|⟨z,hz,hg,i',HZ⟩:= past_stepping p
        · rw [h,show X 0=_ from ht l (by omega),norm_zero]; positivity
        have hx' : reach z ≤r:= hg.trans hp'; have h₀ : street z=n:=by omega
        have ht : ‖X p-X z‖ ≤ P:=by cases HZ with | inl h=> rw [h]; exact he z i' hx' | inr h=> rw [norm_sub_rev,h]; exact he p i' hp'
        apply (norm_le_norm_sub_add (X p) (X z)).trans; push_cast; linarith only [ht,ih z h₀ hx']
    refine ((log _ x rfl hx).trans (mul_le_mul_of_nonneg_right (show (street x:ℝ)≤4*r from ?_) hP)).trans_eq ?_
    · exact_mod_cast ((street_price x).trans (Nat.mul_le_mul_left _ hx))
    unfold P; rw [show d-i=d-(i+1)+1 by omega,pow_succ]; ring

/-- Exact Taylor matching shell with no loss from clearance. -/
theorem sole_price (v:E4)(A:Cover→F)(B:ℝ)(hB:0≤B)(r:ℕ)(H:∀ l:List Axis,l.length=d+1→∀ x:Cover,reach x≤r→ ‖crack l A x‖ ≤ B) (l:List Axis)(h:l.length ≤ d+1)(x:Cover)(hx:reach x≤ r):
    ‖crack l (A-act v (showTime v d A)) x‖ ≤ (4*(reach x:ℝ))^(d+1-l.length)*B:=by
  apply sole _ _ hB _ (fun l h=>extracts v A l (by omega)) _ l h x le_rfl
  intro l h y hy
  rw [← peaked,map_sub,Pi.sub_apply,show peak l (act v (showTime v d A))=0 from ?_,Pi.zero_apply,sub_zero,peaked]; exact H l h y (hy.trans hx)
  unfold act; rw [LinearMap.sum_apply,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [peaked]; apply late; rw [h]; exact i.isLt

-- costs of any interpolation corrections
lemma sole_walk (v:E4)(d:ℕ)(l:List Axis): ∃ C:ℝ,0≤C ∧∀ (A:Series d F)(x:Cover), ‖crack l (act v A) x‖ ≤ C*‖A‖*(1+reach x)^(d-l.length):=by
  let s:= Fin (d+1); choose c hc H using fun i:s=> pay (F:=F) l v i.val
  refine ⟨∑ i:Fin (d+1),c i,Finset.sum_nonneg fun i _=>(hc i).le,fun A x=>?_⟩
  unfold act; rw [← peaked,LinearMap.sum_apply,map_sum,Finset.sum_apply]; simp_rw [LinearMap.comp_apply,LinearMap.proj_apply,peaked]; unfold s at *; apply (norm_sum_le ..).trans; rw [Finset.sum_mul, Finset.sum_mul]; apply Finset.sum_le_sum; intro i _
  apply (H i x (A i)).trans; have hh:=hc i; gcongr; · exact norm_le_pi_norm A i
  · linarith [Nat.cast_nonneg (reach x) (α:=ℝ)]
  have he:= i.isLt; omega
end YM.XSpace.Litter
