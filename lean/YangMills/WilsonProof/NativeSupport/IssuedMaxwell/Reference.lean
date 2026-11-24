import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Detection
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Stress
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Pairings
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Reference
open YM YM.Maxwell
variable (g:YangMills.GaugeGroup)

def issued : YangMills.Maxwell.Reference g where
  toCoordinates:=IssuedMaxwell.Shell.coordinates g
  sector:=shellSector g.core
  sector_iff:=IssuedMaxwell.Sectors.original g
  moment:=fun x=>Wick.moment g.core x
  wick:=IssuedMaxwell.Pairings.original g
  stress:=IssuedMaxwell.Stress.tensor g
  stress_eval:=IssuedMaxwell.Stress.original g
  detected:=IssuedMaxwell.Detection.original g

theorem original :
    (∀d,(issued g).sector d=LinearMap.range (observable g.core d)) ∧
    (∀ n (x:YM.Points n),(issued g).moment x=Wick.moment g.core x) ∧
    ∀a b,((issued g).stress a b).val = -YM.Maxwell.Free.polStress g.core a b:=
  ⟨fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
end IssuedMaxwell.Reference
end
