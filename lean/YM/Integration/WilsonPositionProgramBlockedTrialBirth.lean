import YM.Integration.WilsonPositionProgramBlockedTrialChronology
import YM.Integration.WilsonPositionProgramBlockedTrialFiling
import YM.Integration.WilsonPositionProgramSubmittedCoordinates
import YM.Integration.WilsonPositionProgramMasterBirth
/-! At a genuine lower launch the independently filed ordinary field uses only
the one incoming solved coordinate in the original deposited vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonPositionProgramBlockedTrialBirth
open Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open scoped BigOperators Classical
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical

open WilsonPositionProgramSubmittedCoordinates (submitted)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramMasterBirth (rank)
variable {G:Gauge}(R:Run G){a:ℕ}(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
theorem at_birth (A:Levels G)(O:ChartRatio G)(K:ℕ)(Q:SealR G)(x:Verse Q.F):
    centralL A O K K K Q x=Shrine (Peaks A O Q.ans Q.path K K) x:=by
  unfold centralL polarP
  rw [Nat.sub_self]
  simp only [steep, relativeC, leeB, bindingS, steepen,Matrix.one_mulVec,musical]

theorem original (K:ℕ)(x:∀i,R.family.label (l i))(phase:Fin (a+1)→ℂ →L[ℝ] ℝ)
    (i:Fin (a+1))(n:Side)(b:Volume (d i)):
    let Q:=(deck (G:=G) l d fit) i
    let X:=(submitted R l d fit x phase) i
    let Y:=centralL R.family.path.levels R.metals.O K K K Q X
    let F:=R.family.labels.level (l i); let S:=R.family.localSection (l i)
    PowerSeries.X^rank R (d:=l i)*flash (jot b (Y.1 n))=
      ∑ s,PowerSeries.X^(rank R (d:=l i)-valence F s)*Blue.soil (X s)*
        (jewelBloom (fit i) s b • jet (Plies S (sheet F s) n)):=by
  intro Q X Y F S
  change PowerSeries.X^rank R (d:=l i)*flash (jot b ((centralL _ _ K K K Q X).1 n))=_
  rw [at_birth]
  exact WilsonPositionProgramMasterBirth.assembly R (fit i) K n X b
end YM.Integration.WilsonPositionProgramBlockedTrialBirth
end
