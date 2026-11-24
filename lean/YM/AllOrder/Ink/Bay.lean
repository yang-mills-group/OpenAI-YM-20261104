import YM.AllOrder.Ink.Drive
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
omit [Fintype α] [Fintype β]
lemma wind (x y:Cover)(hx:wrap n x=wrap n y)(hh : x ≠ y): n.val ≤ size x + size y:= by
 let z:=x-y; obtain ⟨i,h⟩:∃ i:Axis, z i≠0:=by by_contra! h; exact hh (sub_eq_zero.mp (funext h))
 have h0 : ((z i:ℤ):ZMod n.val)= (0:ℤ):= by change wrap n z i= _; rw [show wrap n z=0 from (map_sub ..).trans (sub_eq_zero.mpr hx)]; simp
 have he : (n.val:ℤ)∣0-z i:= (ZMod.intCast_eq_intCast_iff_dvd_sub ..).1 h0
 rw [zero_sub,dvd_neg] at he; have hN : n.val ∣ (z i).natAbs:= by obtain ⟨w,hw⟩:=he; refine ⟨w.natAbs,?_⟩; rw [hw, Int.natAbs_mul]; rfl
 refine (Nat.le_of_dvd (by omega) hN).trans ((Finset.single_le_sum (f:=fun i=> (z i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans ?_); unfold z; change size (x-y)≤_; rw [sub_eq_add_neg]; exact (size_add x (-y)).trans_eq (congr_arg (size x+·) (size_neg y))
section gap
variable {F:Stalk α β}(X:Field α)(h:Belt F a C) (ha:0≤a) {x:Site n} (p:Point α)(q:Point β) 
abbrev reach (p:Point α)(q:Point β):= (q.1-p.1)
abbrev gap (F:Stalk α β) (x:Site n)(p:Point α)(q:Point β):= direct F n (stood x p) (stood x q)- F p.2 q.2 (reach p q)
lemma life (F:Stalk α β)(x y:Site n) : direct F n (stood x p) (stood x q)=direct F n (stood y p) (stood y q):= by
 simp only [direct_apply,stood]; simp only [add_assoc,add_right_inj]
lemma exact_ship (u:Cover): (stood x q).1=(stood x p).1+ wrap n u↔ wrap n u=wrap n (reach p q):= by
 simp [reach,stood,eq_sub_iff_add_eq,add_assoc,add_comm (wrap n p.1),eq_comm]
include h ha
lemma wake : SumBudget (fun z:Cover=> if (stood x q).1=(stood x p).1+wrap n z ∧ z≠ reach p q then |F p.2 q.2 z| else 0)
      (Real.exp (a*(size (reach p q)- (n.val:ℝ))) * C) := by
 let r:= reach p q; let X:=Real.exp (a*(size r-(n.val:ℝ))); apply budget_mono (budget_scale (Real.exp_pos _).le (h p.2 q.2)); · intro i; split; positivity; rfl
 intro i; split
 · rename_i ht; have hs : (n.val:ℝ)≤ size i+ (size r:ℝ):= by exact_mod_cast wind _ _ ((exact_ship p q i).1 ht.1) ht.2
   rw [← mul_assoc,← Real.exp_add]; exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (show 0≤a*(↑(size r)-(n.val:ℝ))+a*size i by nlinarith only [ha,hs,mul_le_mul_of_nonneg_left hs ha]))
 positivity
lemma fare_gap : |gap F x p q|≤Real.exp (a*(size (reach p q)-(n.val:ℝ))) * C := by
 let r:=reach p q; let L:=fun z:Cover=> (stood x q).1=(stood x p).1+wrap n z∧ z≠r; let A:= fun z:Cover=> if (stood x q).1=(stood x p).1+wrap n z∧ z≠r then F p.2 q.2 z else 0; have h' := wake (x:=x) h ha p q
 have hm: SumBudget (fun z=> ‖A z‖) (Real.exp (a*(size r-(n.val:ℝ)))*C):= by unfold A; simp_rw [apply_ite norm, norm_zero]; exact h'
 let δ(z:Cover):= if z=r then F p.2 q.2 z else 0; have hd:HasSum δ (F p.2 q.2 r) := (show δ r=F p.2 q.2 r by simp [δ]) ▸ (hasSum_single r (fun x hx=> if_neg hx)); have hp: HasSum A (gap F x p q):= ((regional h ha (stood x p) (stood x q)).sub hd).congr_fun ?_
 · rw [← hp.tsum_eq]; exact (norm_tsum_le_tsum_norm hm.2.1).trans hm.2.2
 intro z; by_cases hh : z=r
 · subst z; have hv:= (exact_ship (x:=x) p q r).2 rfl; unfold A δ; rw [if_pos hv]; simp only [ne_eq,not_true_eq_false,and_false,if_false]; exact (sub_self _).symm
 unfold A δ; rw [if_neg hh,sub_zero]; by_cases he : (stood x q).1=(stood x p).1+wrap n z <;> simp only [he,true_and,false_and,if_pos (show z ≠ r from hh),if_false,if_true]  
 rfl
end gap
end YM.AllOrder.Ink
