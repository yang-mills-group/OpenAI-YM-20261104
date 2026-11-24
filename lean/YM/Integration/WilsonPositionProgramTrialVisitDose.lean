import YM.Integration.WilsonPositionProgramTrialFittedBudget
import YM.Integration.WilsonPositionProgramInversionMaterial

/-! The earned real or imaginary source at a fixed visit has one numerical coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramTrialVisitDose
open Finset Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb
open PhysicalNext.Repeat.Legato Precision Labels
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open scoped Classical BigOperators
open WilsonPositionProgramSubmittedCoordinates (submitted)
open WilsonPositionProgramTrialFittedBudget (scalar)
open WilsonPositionProgramInversionMaterial (Axes dose)
variable {G:Gauge}{n:ℕ}(R:Run G)(l d:Fin (n+1)→ℕ)(fit:∀i,l i<d i)
variable (x:(i:Fin (n+1))→R.family.label (l i))(φ:Fin (n+1)→ℂ →L[ℝ] ℝ)
variable (B:(i:Fin (n+1))→Volume (d i))

def amount (v:Axes R l):ℂ:=
  ∏i,((scalar (x i) (φ i) (v i):ℝ):ℂ)*((jewelBloom (fit i) (v i) (B i):ℝ):ℂ)

theorem original (v:Axes R l):
    dose R l (submitted R l d fit x φ) d fit B v=PowerSeries.C (amount R l d fit x φ B v):=by
  unfold dose amount
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_mul]
  apply congrArg (·*_)
  have one:=congrFun (WilsonPositionProgramTrialFittedBudget.source R l d fit x φ i) (v i)
  change (submitted R l d fit x φ i (v i))=PowerSeries.C (scalar (x i) (φ i) (v i)) at one
  rw [one,PowerSeries.map_C]
  rfl

end YM.Integration.WilsonPositionProgramTrialVisitDose
