import YM.OPE.Compatible.Seeds.Pump
/-!
# Real powers Row memory
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Exterior Tensor WithLp Work.F08 Matrix Bloch Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r d' m n j:ℕ}{b e s:ℝ}{I J W:Type*} {L: Side}
namespace Script
open Page
section
variable {B: Row I J}
lemma stintCost [Fintype J](h:B.strip s b)(hs:0<s)(r:ℕ)(x:Cover×I)(z:ℝ)(q:fieldX J)(hv:0≤ z)(hp:∀ i, ‖q i‖ ≤ z*poise r i.1):
   let k(i: Cover×J):= B x.2 i.2 i.1*q (x.1+i.1,i.2);
   SumBudget (fun i=> ‖k i‖) (Fintype.card J*(widthCost s r*b*(z*poise r x.1))):=by
     intro k; let u:=widthCost s r*b; let c:=z*poise r x.1
     have hc:0 ≤ c := mul_nonneg hv (zero_le_one.trans (poise_one ..)); have hh(j:J):SumBudget (fun i:Cover=>‖k (i,j)‖) (u*c):=by
        have ht:SumBudget (fun i:Cover=> (‖B x.2 j i‖*liftCost r i)*c) (u*c):= by
           have hg:= width_income hs (h x.2 j) r; refine ⟨fun i=>mul_nonneg (hg.1 i) hc, hg.2.1.mul_right _,?_⟩;rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hg.2.2 hc
        refine budget_minor ht (fun i=> norm_nonneg _) (fun i=>?_); unfold k; rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (hp (x.1+i,j)) (norm_nonneg _)).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (mul_le_mul_of_nonneg_left (poise_cumul x.1 i r) hv).trans_eq; unfold c;rw [show poise r i=liftCost r i by unfold poise notch liftCost;push_cast; ring]; ring
     let f(i:J×Cover):= ‖k i.swap‖; have hs : Summable f:= (summable_prod_of_nonneg (f:=f) (fun _=>norm_nonneg _)).2 ⟨fun i=>(hh i).2.1, (hasSum_fintype _).summable⟩; let a:=Equiv.prodComm J Cover; refine ⟨fun i=>norm_nonneg _, a.summable_iff.mp hs,?_⟩
     rw [← a.tsum_eq]; change (∑' i, f i) ≤ _; rw [hs.tsum_prod,tsum_fintype]; exact (sum_le_sum (fun i _=> (hh i).2.2)).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ])
lemma liftCostSame (i: Cover)(r): poise r i=liftCost r i:=by unfold poise notch liftCost;push_cast; ring
end
end Script
end YM.OPE.Flume
