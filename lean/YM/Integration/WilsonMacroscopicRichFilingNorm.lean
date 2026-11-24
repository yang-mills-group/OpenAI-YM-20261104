import YM.Integration.WilsonReportingProductInvoice
import YM.Integration.IntrinsicProductLinearity

/-! Bounds on the actual earlier raw Wilson label, after fixing its reporting date and before every regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFilingNorm
open Filter Function Set Spec OPE OPE.Orbits PhysMS Cells Wilson RG16 RG16.Literal
open Trace.Physical.GermGraph Next.UVStress FilteredWilsonProduct
open RG MergeProof Bid
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}

theorem limits (H:C.Makes){h u b:ℕ}(doors:∀p,Opened C h u p)(ub:u≤b):
    ∃A B:ℝ,0≤A ∧ 0≤B ∧ ∀N p (bN:b≤N) (Y:Cut C N p)(z:C.label h)(E:ℝ),
    quota C h b N p z≤2*E →
    mCost C h N p u (topReport C N p h H u (doors p) (ub.trans bN) Y -
      (C.factory h N p).terminal.symm z)≤E/gainChart C.path b u →
    ‖label (w:=(N,p)) H (doors p) (ub.trans bN) Y‖ ≤ A*(2*E)+B*(2*(E/gainChart C.path b u)):=by
  obtain ⟨A,apos,large⟩:=quota_stop C H ((doors 0).post.trans ub)
  obtain ⟨B,bpos,small⟩:=quota_stop C H (doors 0).post
  refine ⟨A,B,apos,bpos,?_⟩
  intro N p bN Y z E cap currency
  let T:=(C.factory h N p).terminal
  let x:=topReport C N p h H u (doors p) (ub.trans bN) Y
  let e:=x-T.symm z
  have gap:= (size_gap h N p u H (doors p) (ub.trans bN) e).2
  have paid:quota C h u N p (T e)≤2*(E/gainChart C.path b u):=by
    unfold quota
    change (C.labels.level h).coeffSize ((C.factory h N p).entries u (T.symm (T e))).x ≤ _
    rw [T.symm_apply_apply]
    exact gap.trans (mul_le_mul_of_nonneg_left currency zero_le_two)
  have issued:‖z‖≤A*(2*E):=(large N p z bN).trans (mul_le_mul_of_nonneg_left cap apos)
  have error:‖T e‖≤B*(2*(E/gainChart C.path b u)):=
    (small N p (T e) (ub.trans bN)).trans (mul_le_mul_of_nonneg_left paid bpos)
  have restore:T x=z+T e:=by
    dsimp only [e]
    rw [map_sub,T.apply_symm_apply]
    abel
  change ‖T x‖≤_
  rw [restore]
  exact (norm_add_le _ _).trans (add_le_add issued error)

end YM.Integration.WilsonMacroscopicRichFilingNorm
