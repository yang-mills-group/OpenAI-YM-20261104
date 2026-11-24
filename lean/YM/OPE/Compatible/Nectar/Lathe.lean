import YM.OPE.Compatible.Nectar.Burl
/-! Read A as linear multi instrumentation -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{V I W:Type*}{G:Gauge}
namespace Script
open Page
abbrev solidX (p:Script (Shade G) r) (k:Fin r→ Fin d)(x:Fin r→ Alphabet G d):ℝ:=wholeX p (fun i=>ledge (x i (k i)).val)
def itemX (p:Script (Shade G) r)(hp:soot m p c)(k:Fin r→ Fin d)(h:rankX k≤m): Chord G d r where
    toFun := solidX p k
    map_update_add' x i a b :=by
       unfold solidX; let V(j: Alphabet G d)(k:Fin d):=ledge (j k).val; let u(y:Fin r→Alphabet G d)(j: Fin r):= V (y j) (k j); have ht(y): Glob (u y) (fun j=>(k j).val+1):= fun i=>low_quiet (ledgeL _)
       change wholeX p (u _)=wholeX p (u _)+wholeX p (u _); refine choir i hp (ht _) (ht _) h ?_ ?_
       · unfold u; rw [update_self,update_self,update_self];rfl
       intro j hj; unfold u; rw [update_of_ne hj,update_of_ne hj,update_of_ne hj]; simp
    map_update_smul' x i a b:=by
       unfold solidX; change _ = a * _; apply choir_scalar (i:=i)
       · simp only [update_self];rfl
       intro j hj; simp only [update_of_ne hj]
abbrev activated (n:ℕ)(r d:ℕ):Finset (Fin r→ Fin d):=univ.filter (fun y=>rankX y=n)
def actX (p:Script (Shade G) r)(hp:soot m p c)(k:Fin r→Fin d)(h:n ≤ m): Chord G d r:= if he:rankX k=n then itemX p hp k (he.trans_le h) else 0
def honeyX (p:Script (Shade G) r)(hp:soot m p c)(h:n ≤ m)(d:ℕ): Chord G d r:=∑ i,actX p hp i h
lemma solid_mono (p:Script (Shade G) r)(hp:soot m p c)(hx:n≤m)(x:Fin r→Fin d)(v:∀ i:Fin r,Taylor G (x i).val):
   honeyX p hp hx d (fun i=>monoX (x i) (v i))=if rankX x=n then wholeX p (fun i=>ledge (v i).val) else 0:=by
    rw [honeyX,_root_.sum_apply,sum_eq_single x]; swap
    · intro i _ hi; obtain ⟨a,ha⟩:=not_forall.mp (show ¬ ∀ a,i a=x a from fun h=>hi (funext h)); unfold actX; split
      next h=>
        unfold itemX; change solidX _ _ _=0; let V:=fun j=>monoX (x j) (v j); let U j:=ledge (V j (i j)).val
        have hp(j:Page _ r):wordX U j=0:=prod_eq_zero (mem_univ a) (by unfold U V monoX;rw [Pi.single_eq_of_ne ha];rfl)
        unfold solidX wholeX; change (∑' j,p j*wordX U j)=_; simp_rw [hp];simp
      next h=> rfl
    · unfold actX; split_ifs; swap; · rfl
      change solidX _ _ _=_; unfold solidX; simp [monoX]
    simp
lemma rollX (p:Script (Shade G) r)(hp:soot m p c)(hs:p.sorted)(h:p.painted)(hx:n ≤ m): honeyX p hp hx d∈ partX G r n d:=by
    let A:=honeyX p hp hx d; refine { Perms := fun x t=> ?_, Colors:= fun g x=>?_, Grades:=fun x p' h'=> ?_ }
    · change A (x ∘ t)= A x; unfold A; rw [honeyX,_root_.sum_apply,_root_.sum_apply]; let E:(Fin r→Fin d)≃(Fin r→Fin d):=Equiv.arrowCongr t.symm (Equiv.refl _); rw [← E.sum_comp (fun y=> actX p hp y hx (x∘t))]; apply sum_congr rfl; intro i _; unfold actX; by_cases he:rankX i=n
      · rw [dif_pos (show rankX (E i)=n from (Equiv.sum_comp t (fun j=>(i j).val+1)).trans he),dif_pos he]; change wholeX p (fun j=>ledge (x (t j) (i (t j))).val)=wholeX p _; exact sortedX hs (fun j=>ledge (x j (i j)).val) t
      rw [dif_neg (show rankX (E i)≠ n from fun g=>he ((Equiv.sum_comp t (fun j=>(i j).val+1)).symm.trans g)),dif_neg he]; rfl
    · unfold honeyX; rw [_root_.sum_apply,_root_.sum_apply]; apply sum_congr rfl; intro i _; unfold actX; split
      next h'=> change solidX p i (fun j=>spray g (x j))=solidX p i x; unfold solidX; simp_rw [spray,← plume_ledge]; exact script_color hp h g (fun j=> low_quiet (ledgeL (x j (i j)).val)) (h'.trans_le hx)
      next he=> rfl
    rw [solid_mono,if_neg h']
lemma roll_inject (p:Script (Shade G) r)(hp:soot m p c) (hx:n<m)(hy:n ≤ d)(h:p.abides) (ht:Bells p n): honeyX p hp hx.le d=0 ↔ Bells p (n+1):=by
   let A:= honeyX p hp hx.le d; constructor
   · intro H; apply chimes hp h ht hx; intro y hr u
     have ht (i:Fin r): y i<d:=by have hf:= (show y i+1 ≤ n from (single_le_sum (f:=fun j=>y j+1) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans_eq hr);omega
     let x(j):Fin d:=⟨y j,ht j⟩; refine Eq.trans (show _= _ from ((solid_mono p hp hx.le x u).trans (if_pos hr)).symm) ?_; rw [H];rfl
   intro H; apply MultilinearMap.ext; intro x; change A x=0; rw [deckSum]; unfold A; simp_rw [solid_mono]; refine sum_eq_zero fun i _=>?_ ; split; next hc=> exact hail hp (fun j:Fin r=>ledgeL (x j (i j)).val) (hc.trans_le hx.le) (hc.trans_lt (Nat.lt_succ_self n)) H
   rfl

end Script
end YM.OPE.Flume
