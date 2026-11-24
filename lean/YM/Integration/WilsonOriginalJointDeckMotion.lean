import YM.Integration.WilsonOriginalSuspendedCoveredRead
import YM.Integration.WilsonOriginalPolarizedAngularPage

/-! Deck motion on the joint thermal–angular chart. The heat coordinate is fixed under every cover translation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalJointDeckMotion
open Function Finset Lattice RG Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalConnectedPeriodPage WilsonEmittedRootedJetWage
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{n N:Side}{r:ℕ}

def color (a:Site N) : Slot G N→Slot G N:= Option.map fun x=>(a+x.1,x.2)

def turn (a:Site N):(Fin r→Slot G N)≃(Fin r→Slot G N) where
  toFun u i:=color a (u i)
  invFun u i:=color (-a) (u i)
  left_inv u:=by funext i;cases e:u i <;> simp [color,e]
  right_inv u:=by funext i;cases e:u i <;> simp [color,e]

theorem home (u:Fin r→Slot G N):turn (0:Site N) u=u:=by
  funext i
  change color 0 (u i)=u i
  cases u i <;> simp [color]

def motion (G:Gauge)(a:Site N):Joint G N→L[ℝ]Joint G N:=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (edgeColor.toContinuousLinearMap ∘L
    (WilsonOriginalLinkedAngularPage.move G a) ∘L edgeColor.symm.toContinuousLinearMap)

theorem placed (a:Site N)(u:Slot G N):motion G a (peg G N u)=peg G N (color a u):=by
  cases u with
  | none =>
    apply Prod.ext
    · rfl
    · change edgeColor (WilsonOriginalLinkedAngularPage.move G a (edgeColor.symm (0:Directions G N)))=0
      simp only [map_zero]
  | some x =>
    apply Prod.ext
    · rfl
    · change edgeColor (WilsonOriginalLinkedAngularPage.move G a (edgeColor.symm (edgeColor (WilsonOriginalLinkedAngularPage.ray G x))))=edgeColor (WilsonOriginalLinkedAngularPage.ray G (a+x.1,x.2))
      rw [ContinuousLinearEquiv.symm_apply_apply]
      apply congrArg
      funext y
      change (if (y.1-a,y.2)=x then (1:ℝ) else 0)=(if y=(a+x.1,x.2) then 1 else 0)
      rcases y with ⟨v,c⟩
      rcases x with ⟨s,b⟩
      simp only [Prod.mk.injEq,sub_eq_iff_eq_add,add_comm s a]

def entry (r:ℕ) (F:Joint G N→ℂ) (u:Fin r→Slot G N):ℂ:=
  iteratedFDeriv ℝ r F 0 (peg G N ∘ u)

theorem slots (h:n.val∣N.val) (anchor:Site N) (F:Joint G N→ℂ) (smooth:ContDiff ℝ r F) (u:Fin r→Slot G N):
    entry r (WilsonOriginalPolarizedAngularPage.board h anchor (motion G) F) u=
    ∑c:Deck h,entry r F (turn c.val u):=by
  unfold WilsonOriginalPolarizedAngularPage.board entry
  rw [iteratedFDeriv_sum_apply (fun v _=>(smooth.comp (motion G _).contDiff).contDiffAt),_root_.sum_apply]
  let read:=fun y:Site N=>iteratedFDeriv ℝ r F 0 (peg G N ∘ turn (y-anchor) u)
  calc
    _ = ∑p:Fin (Pages n N),read (page h (splitter h anchor) p).val:=by
      apply sum_congr rfl
      intro p _
      let a:Site N:=(page h (splitter h anchor) p).val-anchor
      change iteratedFDeriv ℝ r (F ∘ motion G a) 0 (peg G N ∘ u)=iteratedFDeriv ℝ r F 0 (peg G N ∘ turn a u)
      rw [(motion G a).iteratedFDeriv_comp_right smooth 0 (le_refl _),map_zero,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      exact congrArg (fun z=>iteratedFDeriv ℝ r F 0 z) (funext (fun i=>placed a (u i)))
    _ = ∑c:Deck h,read (c.val+anchor):=pages h anchor read
    _ = _:=by simp only [read,add_sub_cancel_right]

end YM.Integration.WilsonOriginalJointDeckMotion
