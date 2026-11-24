import YM.Integration.WilsonMeasuredPublicEntranceProperPhase
import YM.Integration.WilsonMeasuredPublicEntranceOrderedPins

/-! At every admitted original cutoff, a turned public direction already carried
in the coefficient is evaluated with neutral display on the named group field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionUnturnedCut
open Function Finset Lattice RG Wilson PhysicalNext.Repeat.Legato Extraction Cells
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ)(j N per:ℕ)(o:Fin n→ Cover)

theorem original (live:j≤N)(y:R.family.book.Vector d):
    R.family.omega N per (WilsonMeasuredPublicEntranceCellWords.physical R d (N:=N)
      y (fun _=>(1,false)) (fun i=>wrap (R.family.side j per) (o i)) (Stock.final (Fin n)))=
    WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) d j o N per y:=by
  classical
  have address i:anchorAt R (wrap (R.family.side j per) (o i)) N=Cells.location R.family.S j N per (o i):=by
    rw [WilsonAddressedPublicGridRooms.top R live,Cells.location,dif_pos live]
  have neutral (i:Fin n):displayed R (d i) (y i) (1,false)=y i:=by
    simp [displayed,show (1:Signed).ortho=1 from map_one Signed.inclusionO]
  apply congrArg (R.family.omega N per)
  funext U
  simp only [WilsonMeasuredPublicEntranceCellWords.physical,Stock.final,
    address,neutral]

end YM.Integration.WilsonPhysicalPositionUnturnedCut
end
