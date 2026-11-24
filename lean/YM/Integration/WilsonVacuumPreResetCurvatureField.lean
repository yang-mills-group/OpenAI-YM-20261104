import YM.Integration.WilsonPhysicalHistoryRetainedSpringBareSite
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Rank
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null

/-! The three original low curvature channels in the pre-reset independent
action, with the actual masks on every field. The loop belongs to the shared
baseline, so it is absent from this source and from its local estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvatureField
open Function Filter Finset Lattice Wilson RG Marker Matrix Precision ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Next.Scheduling
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals WilsonStartup Song
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}

abbrev Rows (n:Side):=Tally n ⊕ Stave (n:=n) ⊕ Stave (n:=n)

def slot : Rows n → Songbook n :=
  Sum.elim Sum.inl (Sum.elim (fun i=>.inr (.inl i)) (fun i=>.inr (.inr (.inl i))))

def source (K:PathData G)(c:Clip)(γ β:ℝ):Rows n→ Config G n→ℝ :=
  Sum.elim (tuneLow K c γ) (Sum.elim (tuneAtom K.cubic β) (tuneAtom K.quartic β))

theorem original (B:BudgetPoint)(K:PathData G)(c:Clip){σ C Λ:ℝ}(h:K.Bounds c σ C Λ)
    (γ β:ℝ)(U:Config G n):
    HasSum (fun i:Rows n=>masked B.threshold (strings K B (slot i)).support (source K c γ β i) U)
      (γ*Collection.receipt K c B U+β*(billOf B K.cubic U+billOf B K.quartic U)):=by
  have terms:=HasSum.sum (f:=fun i:Rows n=>masked B.threshold (strings K B (slot i)).support (source K c γ β i) U)
    (pasted K c B U γ h)
    (HasSum.sum (f:=fun i:Stave (n:=n) ⊕ Stave (n:=n)=>
      masked B.threshold (strings K B (slot (.inr i))).support (source K c γ β (.inr i)) U)
      (allocated B K.cubic U β h.width h.three) (allocated B K.quartic U β h.width h.four))
  simpa only [mul_add] using terms

private theorem muscle {r:ℕ}(B:BudgetPoint)(A:ℕ→Atom G r)(U:Config G n)
    (quiet:flags B.threshold U=∅):
    billOf B A U=Patch.average (fun s:Signed=>uncut A (pull s 0 U)):=by
  unfold billOf
  simp_rw [Pane.actly _ _ B _ (Pane.tranquility U quiet _ _)]
  rfl

theorem rooted (B:BudgetPoint)(K:PathData G)(c:Clip){σ C Λ:ℝ}(h:K.Bounds c σ C Λ)
    (γ β:ℝ)(U:Config G n)(quiet:flags B.threshold U=∅):
    ∑' i:Rows n,masked B.threshold (strings K B (slot i)).support (source K c γ β i) U=
       ∑ x:Site n, (γ*OriginalMarkedRunAction.secondAt c K x U+β*OriginalMarkedRunAction.interactionAt K x U):=by
  rw [(original B K c h γ β U).tsum_eq,Collection.receipt,VerifiedReset.allGoodPrice h U quiet,
    muscle B K.cubic U quiet,muscle B K.quartic U quiet]
  have e:Patch.average (fun s:Signed=>uncut K.cubic (pull s 0 U))+
      Patch.average (fun s:Signed=>uncut K.quartic (pull s 0 U))=OriginalMarkedRunAction.interaction K U:=by
    simp only [OriginalMarkedRunAction.interaction,Patch.average,Finset.sum_add_distrib,mul_add]
  rw [e,(OriginalMarkedRunAction.bare_sites c K U).1,(OriginalMarkedRunAction.bare_sites c K U).2.1,
    Finset.mul_sum,Finset.mul_sum,Finset.sum_add_distrib]

end YM.Integration.WilsonVacuumPreResetCurvatureField
