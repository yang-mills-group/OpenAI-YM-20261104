import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Windows
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Parity
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.PreparedScreen
open YM YM.XSpace.Normalize
open YangMills.MSbar
open IssuedMaxwell.Reports (B printed lawful)
variable {g:YangMills.GaugeGroup}
variable (W:(d:ℕ)→Position.Screen (B g) d)(paid:Position.Prepared W)

theorem original (d:ℕ):(IssuedMaxwell.Windows.screened (W d) (paid.range d)).Prepared:=by
  constructor
  · intro T
    apply Subtype.ext
    change (W d).read (printed ((varies (reference g.core d)) T.val))=T.val
    rw [IssuedMaxwell.Reports.variation,IssuedMaxwell.Reports.free]
    exact paid.tangent d T.val ((IssuedMaxwell.Tangents.original _).mp T.property)
  · intro Q
    apply Subtype.ext
    apply LinearMap.ext
    intro p
    let U:=recruit (hinge d) Q
    have matching (n:ℕ)(t:YangMills.SeparatedTest n)(old later:Fin n→Sec g.core d)
        (all:∀i,Position.Mirrored (B g) (old i).val (later i).val):
        printed Q n t old=printed U n t later:=by
      change Q n t old=Q n t (fun i=>hinge d (later i))
      congr 1
      funext i
      rw [(IssuedMaxwell.Parity.original _ _).mp (all i),hinges_back]
    have back:Position.Mirrored (B g) (hinge d p).val p.val:=
      (IssuedMaxwell.Parity.original _ _).mpr (hinges_back p).symm
    exact (IssuedMaxwell.Parity.original _ _).mp <|
      paid.parity d (printed Q) (printed U) (lawful Q) (lawful U) matching (hinge d p) p back
end IssuedMaxwell.PreparedScreen
end
