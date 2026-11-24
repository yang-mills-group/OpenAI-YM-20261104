import YM.Qlocal.Reckoner.Surgery
/-! # Portal hulls at a mask change.Reg.A.Mark.SPEND

 Predetermined (in the application to core projectors, all Π.Test.Data footprints and
 shifts to new registered roots can be drawn before the actuator). The condition is local
 AND on true history-cost weight. No inference just from equal field values on good masks
without funding the transport and every spill, including the K polynomial on the same vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V Ω J J' J₀ K α:Type}[DecidableEq V]{G:Gauge}{n:Side}{R:Census V}
variable {X: RG.Rep G n}{s:V→ Support n}{q q':Ray R} {A A' B u v a r t w δ:ℝ} 
namespace Scribe
variable {S:Scribe Ω J G n R} {T:Scribe Ω J' G n R} {p:BudgetPoint} {L:Loom K R n}
    (F:Lot K S L) (H:Lot K T L)
structure Loom.Path (L:Loom K R n) (d k M:ℕ) : Prop where
   budget i : coverNumber k (L.region i) ≤ d
   openH : ∃ V:Site n→ Support n,(∀ i,(V i).card≤M) ∧ ∀ i j,i∈ L.region j → L.region j⊆ V i
open Lot
variable {d k k' M:ℕ}
-- labor accounting.Book at elevated level α.+ small §reserve. geometric footprint of each change p.Activity.Ch primitive weights. This funds **whole operation** including all projection comparisons, without multiplying by the number of rows in reconciliations. Hull before earning.
namespace Lot
local notation "Σ★"=> F.runs
abbrev price (F:Lot K S L)(f:J→ℝ)(u:K) := ∑ i ∈F.rows u, f i
-- arbitrary occurrence.AccountBook. Use for new poses even if ξ-card could be larger than |V|. support includes each.Old.
lemma scoreCost [Fintype K] {v:J→ℝ} (hq :0≤q) (hF :∀ i,0≤v i)(hp: Ac.Hit S.region k (fun i=> q (S.tag i)*v i) a B) (he:a≥0) (hr:∀ i,(S.region i).Nonempty)
    (V: Support n) (p':Finset K) (hg:∀ i∈p', L.region i ⊆ V): ∑ i ∈p',q (L.tag i)*price F v i ≤ V.card * B:=by
 let b i:= q (S.tag i)*v i; have ht i:0 ≤ b i:= mul_nonneg (hq _) (hF _); let g (i:J)(j):=if j∈S.region i then b i*Real.exp (a*coverNumber k (S.region i)) else 0
 have h (j): SumBudget (fun i=>g i j) B:=hp j
 let Y:=p'.biUnion F.rows
 have ho: Set.PairwiseDisjoint (↑p': Set K) F.rows := fun i hi j hj h=>Finset.disjoint_left.mpr fun x hv he=> h (F.singly _ _ _ hv he)
 have hb:( ∑ i ∈p',q (L.tag i)*price F v i)=∑ i∈ Y,b i:=by
   rw [sum_biUnion ho]; unfold price; simp_rw [Finset.mul_sum]; refine sum_congr rfl fun i _=>sum_congr rfl fun j hj=>congr_arg (·*v j) (congr_arg q (F.logic i j hj|>.symm))
 rw [hb]; apply le_trans (b:=∑ i∈Y,∑ x∈ V, g i x) (sum_le_sum ?_); rotate_left
 · intro i hi; obtain ⟨j,hj,hK⟩:= Finset.mem_biUnion.mp hi; obtain ⟨p,hp'⟩:=hr i; have hh:b i ≤ g i p:=by unfold g; rw [if_pos hp']; exact le_mul_of_one_le_right (ht _) (Real.one_le_exp (mul_nonneg he (by positivity)))
   exact hh.trans (single_le_sum (fun j _=> (h j).1 _) (hg _ hj (F.cost _ _ hK hp')))
 rw [Finset.sum_comm]; refine (sum_le_sum (f:=fun i:Site n=> ∑ j∈Y,g j i) (g:=fun _=>B) (fun x (_:x∈V)=> budget_sum (h x) Y)).trans_eq ?_; rw [sum_const,nsmul_eq_mul]
-- recovery λ.Mark tags.Keep weights on *each* rebalance.Delta actual.I.Scope.Anchor.
abbrev price_Karea (A r ψ:ℝ)(M d:ℕ): ℝ:= ψ* Real.exp (r*d)*(M*A)
set_option maxHeartbeats 400000 in -- analytic paid reserve near project hull.Stem.Power.
lemma dispersed [Fintype K] {u:J→ℝ} (h:L.Path d k M)(hp: Ac.Hit S.region k (fun i=> q (S.tag i)*u i) a B) (hQ:0≤q) (hv:∀ i,(S.region i).Nonempty)(hu:∀ i,0≤u i)(ht:0≤ r)(he:0≤a)(C:Rental q') (hτ:0≤w)(hc:∀ v: R.Mode,v.val.Nonempty→ q' v≤w*q v):
     Ac.Hit L.region k (fun i=> q' (L.tag i)* price F u i) r (price_Karea B r w M d):= by
 intro x; let μ i:=price F u i; have hK(i): 0≤μ i:=sum_nonneg fun j _=>hu j
 obtain ⟨x',hx,hP⟩:= h.openH
 let W:= univ.filter fun i:K=> x∈ L.region i; let f i:= Real.exp (r*coverNumber k (L.region i)); have hh i:f i ≤ Real.exp (r*d):= Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast h.budget i) ht)
 let u' i:= q' (L.tag i)* μ i; have hu' i:0≤u' i:= mul_nonneg (C.pos _|>.le) (hK i); let g i:=if x∈L.region i then (u' i*f i) else 0; have hg i:0≤g i:= by unfold g; split; exact mul_nonneg (hu' _) (Real.exp_nonneg _); rfl
 refine budget_finite hg ?_; change ∑ i,g i≤_; rw [show ∑ i:K,g i=∑ i∈ W,(u' i*f i) from (by unfold g W; rw [Finset.sum_filter])]; let E:=Real.exp (r*d); let y i:= q (L.tag i)* μ i; have hz(i):u' i≤w*y i := (mul_le_mul_of_nonneg_right (hc _ (L.not_blank i)) (hK i)).trans_eq (mul_assoc ..)
 calc ∑ i∈W,(u' i*f i) ≤ ∑ i∈W,(w*y i*E):=sum_le_sum (fun i _=> (mul_le_mul_of_nonneg_left (hh i) (hu' i)).trans (mul_le_mul_of_nonneg_right (hz i) (Real.exp_nonneg _)))
      _ ≤ w*((x' x).card * B)*E:=by rw [← Finset.sum_mul,←Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _); exact mul_le_mul_of_nonneg_left (F.scoreCost hQ hu hp he hv _ W (fun i hi=>hP _ _ (mem_filter.mp hi|>.2))) hτ -- edit.
      _ ≤ _ :=by unfold price_Karea; rw [mul_right_comm w _ E]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show ((x' x).card:ℝ)≤M from Nat.cast_le.mpr (hx x)) (budget_nonneg (hp x))) (mul_nonneg hτ (Real.exp_nonneg _))
-- maybe auto .Exp binder issue. 
end Lot
end Scribe
end YM.Qlocal.Reckoner
