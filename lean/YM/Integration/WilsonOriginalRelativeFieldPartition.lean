import YM.Integration.WilsonOriginalPinnedDeckOrbit
import YM.Integration.WilsonOriginalPinnedMixedIncome

/-! Partition a signed rooted field at its actual word center and independently resolved marked endpoints. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRelativeFieldPartition
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalOccupiedFieldLayout WilsonOriginalMixedCoveredRead
open WilsonOriginalRelativeMixedFields WilsonOriginalNamedRelativeRows WilsonOriginalPinnedDeckOrbit WilsonEmittedRootedJetWage
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

theorem split {K:Type*} [Fintype K] (flag:ι→Prop) (keep:K→Prop) (tag:ι→K) (draw:ι→ℂ)
    (bill:∀b:K,Summable (fun i=>if flag i ∧ tag i=b then draw i else 0)):
    (∑'i,if flag i ∧ keep (tag i) then draw i else 0)=
      ∑b:K,if keep b then ∑'i,if flag i ∧ tag i=b then draw i else 0 else 0:=by
  let row (b:K)(i:ι):ℂ:=if keep b then (if flag i ∧ tag i=b then draw i else 0) else 0
  have can (b:K):Summable (row b):=by
    by_cases ok:keep b
    · simpa only [row,if_pos ok] using bill b
    · simpa only [row,if_neg ok] using (summable_zero:Summable (fun _:ι=>(0:ℂ)))
  calc
    _ = ∑'i,∑b:K,row b i:=by
      apply tsum_congr;intro i
      by_cases f:flag i
      · have one:(∑b:K,row b i)=row (tag i) i:=Finset.sum_eq_single _ (fun b _ diff=>by simp [row,f,Ne.symm diff]) (fun h=>False.elim (h (mem_univ _)))
        rw [one];simp [row,f]
      · simp [row,f]
    _ = ∑b:K,∑'i,row b i:=Summable.tsum_finsetSum (fun b _=>can b)
    _ = _:=by apply sum_congr rfl;intro b _;by_cases ok:keep b <;> simp [row,ok]

variable (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (v:s.val)
theorem parts {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j r:ℕ) (b:PagesOf n N) (u:Fin r→Slot G N):
    needle h M t s v j b=
    ∑p:PagesOf n N, ∑a:Site N×(s.val→PagesOf n N), if a.2 v=b then joined h M t s a.1 j (p,a.2,u) else 0:=by
  funext z
  unfold needle shade
  rw [pages h M t stock hs,Finset.sum_apply,mul_sum,Finset.sum_apply]
  apply sum_congr rfl;intro p _
  rw [Finset.sum_apply]
  let tag:=fun i:ι=>((row h (M i) p).center,assigned h M s.val i p)
  let draw:=fun i:ι=>token h M t i p z
  let flag:=fun i:ι=>(M i).mode=s
  let good:=fun a:Site N×(s.val→PagesOf n N)=>a.2 v=b
  have pay:=split flag good tag draw (fun a=> (collects h M t stock hs (fun i _=>flag i ∧ tag i=a) p z).congr
    (fun i=>by by_cases yes:flag i ∧ tag i=a <;> simp [yes,draw]))
  have base: field h M t p (fun i=>(M i).mode=s ∧ index h (M i) p v.val=b) z=
      ∑a:Site N×(s.val→PagesOf n N),if a.2 v=b then field h M t p (selected h M s a.1 (p,a.2,u)) z else 0:=by
    convert pay using 1
    · apply tsum_congr;intro i
      by_cases yes:(M i).mode=s ∧ index h (M i) p v.val=b <;> simp [flag,good,draw,token,tag,assigned,yes]
    · apply sum_congr rfl;intro a _
      rcases a with ⟨x,Y⟩
      by_cases ok:Y v=b
      · simp only [good,if_pos ok]
        apply tsum_congr;intro i
        simp [tag,Prod.mk.injEq,selected,draw,token,flag]
      · simp [good,ok]
  rw [base,mul_sum]
  apply sum_congr rfl;intro a _
  by_cases yes:a.2 v=b <;> simp [yes,joined]

end YM.Integration.WilsonOriginalRelativeFieldPartition
