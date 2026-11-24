import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.PreparedScreen
import MSPositionPrescription
import MSPositionScreens
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MSPositionLabels
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.PositionStore
open YM YM.XSpace.Normalize
open YangMills.MSbar
open IssuedMaxwell.Reports (B printed lawful)
variable {g:YangMills.GaugeGroup}
variable (P:PositionPrescription (B g))(H:Admissible P)

def room (d:ℕ):Screen g.core d:=IssuedMaxwell.Windows.screened (P.screen d) (H.range d)

theorem next (d:ℕ):Screen.Next (room P H d) (room P H (d+1)):=by
  intro Q
  apply Subtype.ext
  apply LinearMap.ext
  intro p
  let U:=recruit (step d) Q
  have comp (n:ℕ)(t:YangMills.SeparatedTest n)(v:Fin n→Sec g.core d)(w:Fin n→Sec g.core (d+1))
      (eq:∀i,(v i).val=(w i).val):printed U n t v=printed Q n t w:=by
    change Q n t (fun i=>step d (v i))=Q n t w
    congr 1
    funext i
    exact Subtype.ext (eq i)
  have seen:=H.nested d (printed U) (printed Q) (lawful U) (lawful Q) comp p (step d p) rfl
  have same:(P.screen (d+1)).read (printed Q) (step d p)=step d ((P.screen d).read (printed U) p):=
    Subtype.ext seen.symm
  change prev d ((P.screen (d+1)).read (printed Q) (step d p))=(P.screen d).read (printed U) p
  rw [same,prev_step]

def original :Store g.core where
  measure:=room P H
  prepared:=IssuedMaxwell.PreparedScreen.original P.screen H.toPrepared
  respects:=next P H
  survey:=fun d=>IssuedMaxwell.Windows.survey (P.screen d) (H.range d)

theorem reported (d:ℕ)(Q:Prediction g.core d):
    (((original P H).measure d).D Q).val=(P.screen d).read (printed Q):=rfl
theorem granted : YM.XSpace.Photo.Granted (original P H) 6 P.triangle.cut:=by
  intro i x hx a b hab
  exact H.screenClearance i x hx a b hab

end IssuedMaxwell.PositionStore
end
