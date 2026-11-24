import YM.XSpace.Forecast
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Reference
import MSPositionScreens
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Reports
open YM YM.XSpace.Normalize
namespace Pub
open YangMills.MSbar
export Position (Report Lawful Window)
end Pub
abbrev B (g:YangMills.GaugeGroup):=IssuedMaxwell.Reference.issued g
variable {g:YangMills.GaugeGroup} {d:ℕ}

def printed (P:Prediction g.core d):Pub.Report (B g) d:=fun n t p=>P n t p

theorem lawful (P:Prediction g.core d):Pub.Lawful (printed P):=fun n=>⟨P n,fun _ _=>rfl⟩

def received (Q:Pub.Report (B g) d)(law:Pub.Lawful Q):Prediction g.core d:=
  fun n=>Classical.choose (law n)

theorem entire (Q:Pub.Report (B g) d)(law:Pub.Lawful Q):printed (received Q law)=Q:=by
  funext n t p
  exact ((law n).choose_spec t p).symm

def window (w:Pub.Window (B g) d):YM.XSpace.Normalize.Window g.core d:=
  ⟨w.arity,w.profile,w.fields⟩

theorem watched (w:Pub.Window (B g) d)(P:Prediction g.core d):
    watch (window w) P=printed P w.arity w.profile w.fields:=rfl

theorem free (g:YangMills.GaugeGroup)(d:ℕ):
    printed (reference g.core d)=YangMills.MSbar.Position.free (B g) d:=rfl

theorem variation (Q:Prediction g.core d)(T:FieldEnd g.core d):
    printed (varies Q T)=YangMills.MSbar.Position.variation (printed Q) T:=by
  funext n t v
  exact arrow_field _ _ _

theorem original (Q:Pub.Report (B g) d)(law:Pub.Lawful Q):
    ∃ P:Prediction g.core d,∀w:Pub.Window (B g) d,
      watch (window w) P=Q w.arity w.profile w.fields:=
  ⟨received Q law,fun w=>(watched w _).trans <|
    congrFun (congrFun (congrFun (entire Q law) _) _) _⟩
end IssuedMaxwell.Reports
end
