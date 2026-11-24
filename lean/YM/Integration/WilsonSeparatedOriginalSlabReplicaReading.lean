import YM.Integration.WilsonSeparatedOriginalSlabReplicaOrbit
import YM.Integration.WilsonSeparatedOriginalReplicaFunctional

/-! The signed conditional replica functional on the actual ultraviolet gauge
fields, before and after a common native translation of those fields. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaReading
open Function MeasureTheory Set Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{n N per:ℕ}
local notation "I"=>Fin 3
local notation "Space"=>I → Config G (C.side N per)

def turn (d:Site (C.side N per)):C(Space,ℂ)→ₗ[ℂ] C(Space,ℂ) where
  toFun F:=⟨fun W=>F (fun i=>pull 1 d (W i)),F.continuous.comp (continuous_pi (fun i=>(continuous_pull ..).comp (continuous_apply i)))⟩
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def paper (s:I→ℕ)(v:(i:I)→Palette C (s i))(r:ℝ)(Ψ:Wave I)(h:n≤N)(m:ℕ)(g:Body):C(Space,ℂ):=
  ⟨WilsonSeparatedOriginalSlabReplicaOrbit.surface C s v r Ψ h m g,WilsonSeparatedOriginalSlabReplicaOrbit.regular C s v r Ψ h m g⟩

theorem moved (μ:Measure (Config G (C.side N per)))[IsProbabilityMeasure μ](d:Site (C.side N per))(H:C(Space,ℂ)):
    WilsonSeparatedOriginalReplicaFunctional.listener μ (turn (C:=C) d H)=
      WilsonSeparatedOriginalReplicaMeasure.read μ (fun W=>H (fun i=>pull 1 d (W i))):=
  WilsonSeparatedOriginalReplicaFunctional.measured μ _

end YM.Integration.WilsonSeparatedOriginalSlabReplicaReading
