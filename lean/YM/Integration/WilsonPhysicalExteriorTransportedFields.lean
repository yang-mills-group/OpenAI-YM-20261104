import YM.Integration.WilsonPhysicalExteriorHomogeneousWord

/-! The independently priced marked field is carried from its own
formal coupling into the held bulk. This is the two-variable field map
after the third actual bulk substitution, not an identification of
independent untransported fee arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorTransportedFields
open PowerSeries Matrix Lattice PhysicalNext.Repeat.Legato Precision
open MS MS.Land MS.Menus MS.Rake MS.Book MS.Book.Program FVAAlt2 Lobby RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorFeeShift WilsonPhysicalExteriorRunningRows
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}
local notation "PS" => PowerSeries ℂ

theorem successive (P:Team) (u v z:ℝ) (F:PS) :
    reprice P v z (reprice P u v F)=reprice P u z F := by
  calc
    _=reprice P v z (Lobby.redo P v (undo P u F)):=congrArg _ (evaluated P v _)
    _=Lobby.redo P z (undo P u F):=WilsonPhysicalExteriorRunningRows.original P v z _
    _=_:=(evaluated P z _).symm

variable (Q:Prescription B)
def column (p:Label B) (v y z:ℝ) (a:Glyph B p.h) : PS :=
  reprice Q.team v z (coordinates Q p.h v y v (Land.read p.item) a)

theorem bought (p:Label B) (v y z:ℝ) (b:Glyph B p.h) :
    ∑ a:Glyph B p.h,column Q p v y z a * reprice Q.team y z (frame Q p.h y a b) =
      reprice Q.team v z (WilsonPhysicalExteriorFeeShift.fee Q p v b) := by
  let φ:PS→+*PS:=(reprice Q.team y v).toRingHom
  have old:oldFrame Q p.h y*frame Q p.h y=1:=by
    rw [oldFrame,WilsonPhysicalExteriorFeeShift.frame,←map_mul,Matrix.nonsing_inv_mul _ (MSFeeCoordinates.determinant Q p.h),map_one]
  have same:coordinates Q p.h v y v * φ.mapMatrix (frame Q p.h y)=frame Q p.h v:=by
    change (frame Q p.h v*φ.mapMatrix (oldFrame Q p.h y))*φ.mapMatrix (frame Q p.h y)=_
    rw [Matrix.mul_assoc,←map_mul,old,map_one,Matrix.mul_one]
  have prior:(∑ a:Glyph B p.h,coordinates Q p.h v y v (Land.read p.item) a *
      reprice Q.team y v (frame Q p.h y a b))=WilsonPhysicalExteriorFeeShift.fee Q p v b :=
    (congrFun (congrFun same (Land.read p.item)) b).trans
      (WilsonPhysicalExteriorFeeShift.padded Q v (Land.read p.item) b)
  change (∑a:Glyph B p.h, reprice Q.team v z (coordinates Q p.h v y v (Land.read p.item) a)*
    reprice Q.team y z (WilsonPhysicalExteriorFeeShift.frame Q p.h y a b))=_
  simpa only [map_sum,map_mul,successive] using congrArg (reprice Q.team v z) prior

theorem lower (R:Run G) (M:MS_Data G O) (hG:G.Simple) (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p:Label B) (v y z:ℝ) (a:Glyph B p.h) (h:a.size<p.h) : column Q p v y z a=0 := by
  unfold column
  rw [WilsonPhysicalExteriorCoherentGrades.original R M Q hG paid p.h p.item a h y v,map_zero]

end YM.Integration.WilsonPhysicalExteriorTransportedFields
end
