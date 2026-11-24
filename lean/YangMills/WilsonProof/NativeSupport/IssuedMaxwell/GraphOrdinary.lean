import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphOnlyPrice
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphReconstituted
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphValidMarks
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphOrdinary
open YM YangMills.MSbar IssuedMaxwell.Reports
variable (g:YangMills.GaugeGroup)(simple:g.IsSimple)
include simple

theorem valid:Ordinary.Valid (B g) (GraphCorrelation.read g) (GraphReader.name g):=by
  constructor
  · intro n h k d x
    exact ⟨GraphReader.form g d h k x,fun v=>rfl⟩
  · intro n h k a b x equal
    exact GraphReaderScope.original g a b equal h k x
  · intro n h k a x hx
    exact GraphReaderScope.collision g simple a h k x hx
  · intro n a homogeneous
    let p:=GraphHomogeneous.price g a
    have paid:=GraphHomogeneous.original g simple a homogeneous
    exact ⟨p,paid,fun q hq=>GraphOnlyPrice.original g simple a q p hq paid,
      fun h k x=>GraphReconstituted.original g a homogeneous h k x⟩

theorem original:Ordinary.Determined (B g) (GraphCorrelation.read g):=
  ⟨GraphReader.name g,valid g simple,fun _ h=>GraphValidMarks.original g simple h (valid g simple)⟩

theorem numerical:Ordinary.read (B g) (original g simple)=GraphReader.name g:=
  (Ordinary.eq_read (B g) (certificate:=original g simple) (valid g simple)).symm
end IssuedMaxwell.GraphOrdinary
end
