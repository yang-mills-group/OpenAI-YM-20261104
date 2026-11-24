import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskComplete

/-! Regroup the original ordered quadratic indices and their real masks at
a physical site. Summing the sites recovers the original numerical receipt,
including on configurations with flags. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Finset Lattice RG Wilson Precision Stationary
open AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open Comparison.Density.Render PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Scheduling
open scoped BigOperators Classical
open private pairIndices from YM.Integration.WilsonPhysicalHistoryRetainedSpringGram
variable {G:Gauge} {n:Side}

private def lowSplit : PlaqAxes ⊕ PairsIndex ≃ Low where
  toFun:=Sum.elim (fun a=>(a,Sum.inl ())) (fun a=>(a.1,Sum.inr a.2))
  invFun:=fun a=>a.2.elim (fun _=>Sum.inl a.1) (fun l=>Sum.inr (a.1,l))
  left_inv:=by rintro (a|⟨a,l⟩) <;> rfl
  right_inv:=by rintro ⟨a,b|l⟩ <;> rfl

theorem spring_mask_low (K:PathData G) (c:Clip) {u D Λ:ℝ} (sale:K.Bounds c u D Λ)
    (p:BudgetPoint) (v:Seat n) (U:Config G n) :
    maskedFace K c p v U+maskedGram K c p v U=∑'o:Low,o.maskedPlain K c 0 p (v.view U) := by
  let f (o:Low):=o.maskedPlain K c 0 p (v.view U)
  have h:Summable f:=Low.maskedPlain_sum sale p _ _
  have s:Summable (fun i=>f (lowSplit i)):=h.comp_injective lowSplit.injective
  calc
    _ = (∑'a:PlaqAxes,f (lowSplit (Sum.inl a)))+∑'a:PairsIndex,f (lowSplit (Sum.inr a)) := by
      rw [tsum_fintype,←pairIndices.tsum_eq (fun a=>f (lowSplit (Sum.inr a)))]
      rfl
    _ = ∑'i,f (lowSplit i):=(Summable.tsum_sum (s.comp_injective Sum.inl_injective)
      (s.comp_injective Sum.inr_injective)).symm
    _ = _ := lowSplit.tsum_eq f

theorem spring_mask_seats (f:Seat n→ℝ) :
    ∑x:Site n,∑s:Signed,f (Song.splay n (s,x))=∑v:Seat n,f v := by
  calc
    _ = ∑s:Signed,∑x:Site n,f (Song.splay n (s,x)) := sum_comm
    _ = ∑v:Seat n,f (Song.splay n v) := (Fintype.sum_prod_type (fun v:Signed×Site n=>f (Song.splay n v))).symm
    _ = _ := Equiv.sum_comp (Song.splay n) f

theorem spring_mask_second (K:PathData G) (c:Clip) {u D Λ:ℝ} (sale:K.Bounds c u D Λ)
    (p:BudgetPoint) (U:Config G n) :
    ∑x:Site n,maskedSecondAt K c p x U=Collection.receipt K c p U := by
  simp only [maskedSecondAt,Patch.average,←Finset.mul_sum]
  change factor*(∑x:Site n,∑s:Signed,(fun v=>maskedFace K c p v U+maskedGram K c p v U) (Song.splay n (s,x)))=_
  have h:=spring_mask_seats (n:=n) (fun v=>maskedFace K c p v U+maskedGram K c p v U)
  refine (congrArg (factor*·) h).trans ?_
  exact congrArg (factor*·) (Finset.sum_congr rfl fun v _=>spring_mask_low K c sale p v U)

theorem spring_mask_interaction {h:ℕ} (A:ℕ→Atom G h) (p:BudgetPoint) (U:Config G n) :
    ∑x:Site n,maskedSitePacket A p x U=Song.billOf p A U := by
  unfold maskedSitePacket Song.billOf
  simp only [Patch.average,←Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

end YM.Integration.OriginalMarkedRunAction
