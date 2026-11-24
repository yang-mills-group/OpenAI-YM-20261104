import YM.Integration.WilsonAddressedPublicGridRoster

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicGridRooms
open Lattice Wilson RG Org Source Labels RG05Readout Native Address
open PhysicalNext PhysicalNext.Repeat.Legato Extra.Histories Motion Mix
open WilsonThermometerReflectedTrajectory WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar
open scoped Classical
variable {G:Gauge} (R:Run G) {j N p:ℕ}
local notation "C" => R.family

theorem top (hj:j≤N) (c:Site ((C).side j p)) :
    anchorAt R c N=((C).S.toDepth hj p).embed c :=by
  simp only [anchorAt,Mix.camp,dif_pos hj]

theorem position (hj:j≤N) (c:Site ((C).side j p)) :
    point R (N:=N) 0 (1,false) c j=c :=by
  let Q:Ratio ((C).side j p) ((C).side N p):=(C).S.toDepth hj p
  have z:Q.parent 0=0:=by rw [←Q.root.map_zero];exact Q.embed_parent _
  have base:anchorAt R c j=c:=Extra.Histories.Tour.begin_anchor (C) p j c
  simp only [point,location,site,dif_pos hj,base]
  change affine 1 c (Q.parent 0) = c
  rw [z]
  simp [affine]

end YM.Integration.WilsonAddressedPublicGridRooms
end

