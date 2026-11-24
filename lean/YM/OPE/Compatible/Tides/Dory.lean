import YM.OPE.Compatible.Tides.Bats
import YM.OPE.Compatible.Ash.Tea
import YM.OPE.Compatible.Parcels.Rails
/-!
# Shell cardinal and mass
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume
open scoped BigOperators Classical ContDiff
variable {j k r Q:ℕ}{a:Cover}{f:Cover→ℝ}{B:ℝ}
def pod (n:ℕ):Finset Cover:= (Fintype.piFinset fun (_:Axis)=>Finset.Icc (-(n:ℤ)) (n:ℤ)).filter (fun x:Cover=>size x≤ n)
def podAt (n:ℕ):= (pod n).filter (fun x=> size x=n)
@[simp] lemma in_pod:a∈ pod j ↔size a ≤ j:=by
    unfold pod; rw [Finset.mem_filter,Fintype.mem_piFinset]; refine ⟨fun h=>h.2,fun hh=>⟨fun i=>?_ ,hh⟩⟩; rw [Finset.mem_Icc]; have hv:=one_bead i a;omega
@[simp] lemma in_podAt:a∈podAt j ↔size a=j:=by
   rw [podAt,Finset.mem_filter,in_pod]; exact and_iff_right_of_imp Eq.le
lemma pod_walk : pod Q=(Finset.range (Q+1)).biUnion podAt:=by ext; simp
lemma gathers {E:Type*}[AddCommMonoid E](F:Cover→E)(k:ℕ): ∑ i∈ pod k,F i=∑ j∈ Finset.range (k+1),∑ i∈podAt j,F i:=by
   rw [pod_walk]; exact Finset.sum_biUnion (fun i _ j _ hij=> Finset.disjoint_left.mpr fun x hx hy=>hij (Eq.trans (in_podAt.mp hx).symm (in_podAt.mp hy))) -- x lint
lemma pot_card (j:ℕ): (podAt j).card ≤ 2*(2*j+1)^3:=by
   let F(x:Cover): Bool × (Fin 3→ℤ):=(decide (x 0 < 0),fun i=>x i.succ); let A:Finset (Fin 3→ℤ):= Fintype.piFinset (fun _=> Finset.Icc (-(j:ℤ)) (j:ℤ)); have hh(x:Cover)(hx:x∈podAt j)(i:Fin 3):((x i.succ).natAbs≤ j):=in_podAt.mp hx ▸ one_bead .. -- orientation
   have hi :(podAt j).card≤ (Finset.univ (α:=Bool) ×ˢ A).card:=by
       apply Finset.card_le_card_of_injOn F; · intro i h; apply Finset.mem_product.mpr; refine ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr (fun j'=> Finset.mem_Icc.mpr ?_)⟩; have hp:=hh i h j'; change _≤ i j'.succ∧i j'.succ≤_; omega
       intro x hx y hy H
       have hr : ∀ i:Fin 3,x i.succ=y i.succ:= congrFun (congrArg Prod.snd H); have he:(x 0<0 ↔ y 0<0) := by have ht:=congrArg Prod.fst H; simpa [F] using ht -- decide equality
       funext i; refine Fin.cases ?_ hr i; have hg:size x=size y:= by rw [in_podAt.mp hx,in_podAt.mp hy]
       unfold size at hg; change ∑ i:Fin (3+1),_= ∑ i:Fin (3+1),_ at hg; rw [Fin.sum_univ_succ (f:=fun i=>(x i).natAbs),Fin.sum_univ_succ (f:=fun i=>(y i).natAbs)] at hg; simp_rw [hr] at hg; omega
   apply hi.trans; rw [Finset.card_product,Fintype.card_piFinset, Finset.card_univ,Fintype.card_bool]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin, Int.card_Icc]; have h: (↑j + 1 - - (↑j:ℤ)).toNat=2*j+1:=by omega
   rw [h]
-- interior summations.Beta.
lemma faze_low (hf:∀ x:Cover,‖f x‖ ≤ B/(notch x:ℝ)^k)(hB:0≤B)(ht:k+r=3)(q:ℕ):∑ x∈ podAt q,‖f x‖ ≤ 16*B*(q+1:ℝ)^r:=by
   let c:ℝ:= q+1; have he:0<c:=by unfold c; positivity
   refine (Finset.sum_le_sum (g:=fun _=> B/c^k) ?_).trans ?_; · intro x h; apply le_trans (hf x); rw [notch,in_podAt.mp h,add_comm 1 q]; unfold c; push_cast;rfl
   rw [Finset.sum_const,nsmul_eq_mul]; have hh: ((podAt q).card:ℝ) ≤ 16*c^3:=by
      grw [pot_card q]; push_cast; grw [show (2*(q:ℝ)+1) ≤ 2*c from by unfold c;linarith]; exact le_of_eq (by ring)
   exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans (le_of_eq (by change 16*c^3*(B/c^k)= _*c^r; rw [← ht,pow_add];field_simp))
lemma fade_low (hf:∀ x∈pod Q,‖f x‖ ≤ B/(notch x:ℝ)^k)(hB:0≤B)(ht:k+r=3):∑ x∈pod Q, ‖f x‖ ≤ 16*B*((Q:ℝ)+1)^(r+1):=by
   let T:Cover→ℝ:=fun x=> if x∈pod Q then f x else 0; have ht'(x):‖T x‖ ≤ B/(notch x:ℝ)^k:=by unfold T; split; exact hf _ (by assumption); rw [norm_zero]; positivity
   grw [Finset.sum_congr (g:=fun x=> ‖T x‖) rfl (fun i hi=>show ‖f i‖=‖T i‖ by simp only [T,if_pos hi]), gathers (fun x=> ‖T x‖)]; apply le_trans (Finset.sum_le_sum (g:=fun _=>16*B*((Q:ℝ)+1)^r) (fun i hi=>(faze_low ht' hB ht i).trans (by gcongr; have :=Finset.mem_range.mp hi; omega))) (le_of_eq (by simp[Finset.sum_const];ring))
end YM.OPE.Balsam
