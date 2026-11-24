import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.SectorSpine
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Filtered
open YM YM.Maxwell YM.Extra.FD

theorem reduce {G:Gauge} {d:ℕ} {p:Labels.Pol G} (hp:p∈Labels.limited G d):
    reduceEq p∈through G d:=
  filterMove Labels.generation costKey reduceEq
    (gradientReduce (fun j=>j+2)) (s:=Set.Iic d) hp

theorem original {G:Gauge} {d:ℕ} {p:WickPol G} (hp:p∈through G d):
    writeRaw p∈Labels.limited G d ∧ reduceEq (writeRaw p)=p:=
  ⟨filterMove costKey Labels.generation writeRaw
    (gradientWrite (fun j=>j+2)) (s:=Set.Iic d) hp,writeRaw_after p⟩
end IssuedMaxwell.Filtered
end
