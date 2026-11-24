import YM.RG01.Vacuum.Actual
import YM.Extra.ITERATION_NO_LOSS.Geometry

/-!
# Stop denominator: erase per-anchor rare log price with actual masks

 Difference, not gradient. Use opposite edited configuration to cancel
 extensive costs without EVER asserting one can ignore an indicator. Use
 halo to cover all inspected links before doing so.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection
open Function Filter Set MeasureTheory Lattice Wilson RG Quotes Geo Extra.Iteration Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side} {X:Listing G n} {v:Source G n} {p:BudgetPoint} {H w:ℝ}
variable (h:Local X p v H w)

def editsFee (p:BudgetPoint)(H:ℝ)(l:ℕ) :ℝ:=2*(l*Footprint.payment 1 (4*p.B+2) 0 1 1 H (p.supportExponent+1) 0)

private lemma intercepted (P D : Support n)(he:Disjoint P (halo 8 D)) : (inspected P:Set (Site n)) ⊆ (D:Set (Site n))ᶜ:=by
   intro x hx hD; obtain ⟨y,hy,hh⟩:= Shapes.inspect_dist _ hx; exact Finset.disjoint_left.mp he hy (halo_spec.mpr ⟨x,hD,hh⟩)

private lemma habitual {U V:Config G n} (K : Support n)(he:Agrees (K:Set (Site n))ᶜ U V) (i:ℕ)
    (hp:p.Regular (X.reg i).support (v.logRead i)) (h':Disjoint (X.reg i).support (halo 8 K)) : (X.read v).regularOccurrence p i U=(X.read v).regularOccurrence p i V:=by
   let P:=(X.reg i).support
   have hh:= agrees_mono he (intercepted _ _ h')
   have hL:= hp.sites U V (agrees_mono hh fun _ hx=> Finset.mem_union_left _ hx)
   have hz:Healthy p.threshold P U ↔ Healthy p.threshold P V:=by
     unfold Healthy; simp_rw [Finset.disjoint_iff_inter_eq_empty]; rw [flags_agree p.threshold U V P hh]
   change masked _ P _ U=masked _ P _ V
   by_cases hV:Healthy p.threshold P V
   · rw [masked_eq _ P _ V hV,masked_eq _ P _ U (hz.mpr hV)]; exact hL
   rw [masked_ne _ P _ V hV,masked_ne _ P _ U (fun H=>hV (hz.mp H))]

include h
lemma Local.debit (K:Support n) (U V:Config G n) (he:Agrees (K:Set (Site n))ᶜ U V) :
    SumBudget (fun i=> ‖(X.read v).regularOccurrence p i U - (X.read v).regularOccurrence p i V‖) (editsFee p H (halo 8 K).card):=by
    obtain ⟨b,hb,Hb⟩:= h.cheap
    let p':= Footprint.payment 1 (4*p.B+2) 0 1 1 H (p.supportExponent+1) 0
    let P(i:ℕ):=(X.reg i).support
    have hA : Ac.Hit P p.B b (p.supportExponent+1) p':=by
        apply Footprint.assigned (id:Site n→ Site n) 1 (fun V:Support n=> by simp) (fun i=>(X.reg i).site) b (fun i=>(hb i).1) (fun i=> coverNumber p.B (P i)) P Hb (4*p.B+2) 0 _ (v':=1) (fun i x hi=> enlarged_dist p _ x (Finset.mem_union_left _ hi)) (by simp) zero_le_one ⟨by linarith [p.exponent_pos],by norm_num,by unfold preExponent; linarith⟩ b (fun i=>(hb i).1) (fun i=>by simp)
    let D(x:Site n)(i:ℕ):= if x∈P i then b i else 0
    let L:= halo 8 K
    have hB (x) : SumBudget (D x) p':=by
        refine budget_mono (hA x) (fun i=> by unfold D;split;exact (hb i).1;exact le_rfl) fun i=>?_
        dsimp only [D]; split
        · apply le_mul_of_one_le_right (hb i).1 (Real.one_le_exp (mul_nonneg (by linarith [p.exponent_pos]) (Nat.cast_nonneg _)))
        exact le_rfl
    have hv:= budget_scale (by norm_num : (0:ℝ)≤2) (budget_over L D (fun _=>p') (fun i _=> hB i))
    have hq (W:Config G n) (i) : ‖(X.read v).regularOccurrence p i W‖ ≤ b i:=by
        change ‖masked p.threshold (P i) (v.logRead i) W‖ ≤ b i
        by_cases ht:Healthy p.threshold (P i) W
        · rw [masked_eq p.threshold (P i) _ W ht]; exact (hb i).2 W ht [] (Nat.zero_le _) (by simp) -- rw P defeq?
        rw [masked_ne p.threshold (P i) _ W ht,norm_zero]; exact (hb i).1
    apply budget_mono (show SumBudget (fun i=>2*∑ x∈L,D x i) (editsFee p H L.card) from (by simpa only [editsFee,p',Finset.sum_const,nsmul_eq_mul] using hv)) (fun i=>norm_nonneg _) (fun i=>?_)
    by_cases ha:Disjoint (P i) (halo 8 K)
    · rw [habitual K he i (h.smooth i) ha,sub_self,norm_zero]; exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _=> (hB x).1 i)
    obtain ⟨x,hx,hK⟩:= Finset.not_disjoint_iff.mp ha
    have hg : b i ≤ ∑ x∈L,D x i:=by
      rw [← show D x i=b i from if_pos hx]; exact Finset.single_le_sum (f:=fun x=>D x i) (fun x _=> (hB x).1 i) hK
    rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add ((hq U i).trans hg) ((hq V i).trans hg))

lemma Local.varyLog (K:Support n) (U V:Config G n)(he:Agrees (K:Set _)ᶜ U V):
    ‖(X.read v).additive p U-(X.read v).additive p V‖ ≤ editsFee p H (halo 8 K).card:=by
    obtain ⟨d,hd,hD⟩:= Activities.E_total h.unweighted
    have hv (W:Config G n): Summable fun i=> (X.read v).regularOccurrence p i W := by
      apply Dominated.summable (F:=fun i W=> masked p.threshold (X.reg i).support (v.logRead i) W) _ W
      refine ⟨d,hd,fun i V=>?_⟩
      by_cases hu:Healthy p.threshold (X.reg i).support V
      · dsimp only; rw [masked_eq _ _ _ _ hu]; exact (hD i).2 V hu [] (Nat.zero_le _) (by simp)
      dsimp only; rw [masked_ne _ _ _ _ hu,norm_zero]; exact (hD i).1
    have hh:= h.debit K U V he
    unfold Activities.additive; rw [← Summable.tsum_sub (hv U) (hv V)]; exact (norm_tsum_le_tsum_norm hh.2.1).trans hh.2.2
end YM.AnalyticBridge.VerifiedReset.Collection
