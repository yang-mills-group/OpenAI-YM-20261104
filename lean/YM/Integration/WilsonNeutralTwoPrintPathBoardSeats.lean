import YM.Integration.WilsonNeutralTwoPrintPathFineFiber
import YM.Integration.WilsonOriginalCensusPageOrbits
import YM.Integration.WilsonNeutralTwoPrintPathBoxMean

/-! Each occupied source owns its actual fine sheet. Their physical parents
split into one common deck motion and one relative choice at each other root. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardSeats
open Function Finset Lattice RG QuadraticLocal
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalCensusPageOrbits (placed)
open WilsonOriginalCensusOrbitCenters (layout shifted escort)
open WilsonOriginalRelativePageTail (locate retained chosen)
open WilsonNeutralTwoPrintPathFineFiber (seats)
open scoped Classical BigOperators
variable {I:Type}[DecidableEq I]{n f X F:Side}
variable (P:Patch)(u:f.val=n.val*P.L.val)(v:F.val=X.val*P.L.val)(h:n.val∣X.val)(hf:f.val∣F.val)
  (S:Finset I)(o:S)(address:I→Site f)
def homes (i:I):Site n:=(Ratio.mk P.L u:Ratio n f).parent (address i)
def copies:(S→Fin (Pages n X))≃(S→Fin (Pages f F)):=
  Equiv.piCongrRight (fun i:S=>WilsonOriginalCensusChildPages.choice u v h hf (address i.val))
omit [DecidableEq I] in
private theorem parent (p:S→Fin (Pages n X))(i:S):
    WilsonNeutralTwoPrintPathFineFiber.parent P v hf S address (copies P u v h hf S address p) i=
      (page h (homes P u address i.val) (p i)).val:=by
  rw [WilsonNeutralTwoPrintPathFineFiber.numbered P u v h hf]
  let eqv:=WilsonOriginalCensusChildPages.choice u v h hf (address i.val)
  change (page h (homes P u address i.val) (eqv.symm (eqv (p i)))).val=_
  rw [Equiv.symm_apply_apply]

variable (root:Site X)(site:(S.erase o.val)→Site X)(base:Fin (Pages n X))
theorem original (front:(page h (homes P u address o.val) base).val=root)
    (others:∀i:S.erase o.val,splitter h (site i)=homes P u address i.val)
    (d:Deck h)(p:(S.erase o.val)→Fin (Pages n X)):
    seats P v h hf S address (copies P u v h hf S address
      (placed h S o.val (homes P u address) base d p)) o=
        layout h S o.val (d.val+root) (shifted h site d) (escort h site d p):=by
  let full:=placed h S o.val (homes P u address) base d p
  let pick:=copies P u v h hf S address full
  let next:=WilsonNeutralTwoPrintPathFineFiber.parent P v hf S address pick
  have center:next o=d.val+root:=by
    change WilsonNeutralTwoPrintPathFineFiber.parent P v hf S address (copies P u v h hf S address _) o=_
    rw [parent P u v h hf S address]
    dsimp only [full]
    rw [WilsonOriginalCensusPageOrbits.root h S o.val o.prop,
      WilsonOriginalLocatedDeckAction.value,front]
  let seats₁:(S.erase o.val)→Site X:=fun i=>next ⟨i.val,mem_of_mem_erase i.prop⟩
  have actual (i:S.erase o.val):seats₁ i=locate h (shifted h site d) (escort h site d p) i:=by
    change WilsonNeutralTwoPrintPathFineFiber.parent P v hf S address (copies P u v h hf S address _) _=_
    rw [parent P u v h hf S address,WilsonOriginalCensusPageOrbits.physical,WilsonOriginalCensusOrbitCenters.located]
    change d.val+(page h (homes P u address i.val) (p i)).val=d.val+(page h (splitter h (site i)) (p i)).val
    rw [others i]
  change layout h S o.val (next o) seats₁ (retained h seats₁)=_
  rw [center]
  unfold layout
  congr 1
  funext i
  unfold WilsonPointChildRelativeLift.centers
  rw [chosen,actual]

end YM.Integration.WilsonNeutralTwoPrintPathBoardSeats
end
