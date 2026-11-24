import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.NativeWindows
open YM YM.XSpace YM.XSpace.Normalize YangMills.MSbar
open IssuedMaxwell.Reports
variable {g:YangMills.GaugeGroup} (V:Store g.core)

def display (d:ℕ):Position.Screen (B g) d where
  size:=(V.survey d).n
  window:=fun i=>let t:=(V.survey d).scope i;⟨t.n,t.t,t.p⟩
  weights:=(Change g.core d).subtype.comp (V.survey d).tally

theorem range (d:ℕ)(v:Fin (display V d).size→ℂ):
    Position.IsChange (B g) d ((display V d).weights v):=
  (Tangents.original _).mp ((V.survey d).tally v).property

theorem reported (d:ℕ)(Q:Prediction g.core d):
    (display V d).read (printed Q) = ((V.measure d).D Q).val:=
  congrArg Subtype.val ((V.survey d).equal Q)

theorem lawful (d:ℕ)(Q:Position.Report (B g) d)(h:Position.Lawful Q):
    (display V d).read Q=((V.measure d).D (received Q h)).val:=by
  rw [← reported,entire]

theorem tangent (d:ℕ)(A:Module.End ℂ ((B g).sector d))(h:Position.IsChange (B g) d A):
    (display V d).read (Position.variation (Position.free (B g) d) A)=A:=by
  let T:Change g.core d:=⟨A,(Tangents.original A).mpr h⟩
  rw [← Reports.free,← Reports.variation,reported]
  exact congrArg Subtype.val ((V.prepared d).1 T)
end IssuedMaxwell.NativeWindows
end
