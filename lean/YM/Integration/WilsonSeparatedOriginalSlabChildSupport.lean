import YM.Integration.WilsonSeparatedOriginalSlabChildWords
import YM.Integration.WilsonSeparatedOriginalSlabChildSites
import YM.Integration.WilsonSeparatedOriginalReplicaScanner

/-! Entire translated true joint and replica measurements vanish away from the original wave's finite physical parent roster. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildSupport
open Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalSlabChildSites
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){b n N per:ℕ}(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))(top:n ≤ N)
variable (A:Ratio (R.family.side b per) (R.family.side n per))(o:Fin 3 → Site (R.family.side n per))(c:Site (R.family.side n per))
variable {r cap:ℝ}(rp:0<r)(Ψ:Wave (Fin 3))(shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖ ≤ cap)
variable (J:ℕ)(outside:o∉Pulse.area (C:=R.family) (p:=per) (b:=n) J)(reach:r*cap+2*R.family.S.a n ≤ R.family.S.a n*(J:ℝ))
variable (z:E4)(hz:z∈Native.box)

include rp shape outside reach hz
theorem field:WilsonSeparatedOriginalReplicaWave.scalp s v (site A o c) top (cropX Ψ o r z)=0:=by
  have gone:=WilsonSeparatedOriginalReplicaSupport.absent s v top rp Ψ shape J o outside reach z hz
  let shift:=c+A.root (-(A.parent (o 0+c)))
  have eq:site A o c=fun i=>o i+shift:=by funext i;exact add_assoc ..
  rw [eq];funext W
  rw [←WilsonSeparatedOriginalSlabChildWords.copies top s v o shift (cropX Ψ o r z) W,gone];rfl

theorem raw (opened:b+1 ≤ N)(U:Config G (R.family.side b per)):
    WilsonSeparatedOriginalSlabWave.scan R s v (site A o c) top opened U (cropX Ψ o r z)=0:=by
  have absent:=field R s v top A o c rp Ψ shape J outside reach z hz
  rw [WilsonSeparatedOriginalSlabWave.measured]
  have vanished:Pulse.scalp s v (site A o c) top (cropX Ψ o r z)=0:=by
    funext W;rw [←WilsonSeparatedOriginalReplicaRegularity.diagonal,absent];rfl
  rw [vanished];exact integral_zero ..

theorem connected (opened:b+1 ≤ N)(U:Config G (R.family.side b per)):
    WilsonSeparatedOriginalReplicaScanner.sample R s v (site A o c) top opened U (cropX Ψ o r z)=0:=by
  have absent:=field R s v top A o c rp Ψ shape J outside reach z hz
  rw [WilsonSeparatedOriginalReplicaScanner.measured,absent]
  simp [WilsonSeparatedOriginalReplicaMeasure.read]

end YM.Integration.WilsonSeparatedOriginalSlabChildSupport
