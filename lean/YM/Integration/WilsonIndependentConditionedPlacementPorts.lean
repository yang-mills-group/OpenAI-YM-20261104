import YM.Integration.WilsonIndependentConditionedPlacementDose
import YM.Integration.WilsonIndependentConditionedPlacementArm
import YM.Integration.WilsonIndependentConditionedBankRulerHearing
import YM.Integration.WilsonIndependentNotebookComplexCorners

/-! A single all-order coordinate on the selected ruler for both public preparations and both real components, uniformly over their actual received lattice addresses. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPlacementPorts
open Function Finset Lattice RG Wilson Source Labels Extra.Histories
open XSpace XSpace.Rose XSpace.Cirrus PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Fountain
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Wheel.Mark RG.Supply
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedBankSeats (Resident)
open WilsonIndependentConditionedBankMatrix (sample)
open WilsonIndependentConditionedBankRulerHearing (stamps wages)
open WilsonIndependentConditionedPlacementArm (stencil)
open WilsonIndependentNotebookComplexCorners (assembled)
open WilsonReflectedMixedObservedArms (Printed)
open WilsonPositionProgramTrialHomeDose (publicDose)
open scoped Classical BigOperators

local notation "J" => Fin 2
local notation "C" => Credit.leanC
local notation "choices" => Bool×Bool
variable {G:Gauge}{R:Run G}{grade top:J→ℕ}(fit:∀s,grade s<top s)
variable {e k u₀ u b grant host m f K N per target:ℕ}{up:f≤K}{live:K≤N}{η:ℝ}
variable {V:Realm G (e+1) C}{coins:Prices}{own:∀s,Rails (grade s) k u₀ e}
variable {port:∀s,Home R (deck (G:=G) grade top fit s) (own s) grant}
variable (station:J→Bool→ℕ)
variable (axes:∀s,Bool→(R.family.label (grade s)≃ₗ[ℂ]R.family.label (grade s)))
variable (bare:∀s,Bool→R.family.label (grade s))(turn:J→Bool→Signed)(hand:J→Bool→Bool)(phase:J→Bool→ℂ)
variable (I:Initialize G)(survey plain:J→Bool→Bool)

def seed (m f K N per:ℕ)(s:J)(l:choices):TowerS G (deck (G:=G) grade top fit s).D:=
  stencil R (axes s l.1) (bare s l.1) (turn s l.1) (hand s l.1) (phase s l.1)
    (station s l.1) m f K N per I (survey s l.1) (plain s l.1) l.2 (fit s)

variable (r:∀s,Bool→Resident R (grade s) f K N per target up live η)
variable {address:J→Bool→Site (R.family.side f per)}
variable (receipt:∀s c,Printed R (station s c) (axes s c) (bare s c) (turn s c) (hand s c) (address s c)
  (r s c).arm)
variable (tint:∀s c,(r s c).phase=phase s c)

include receipt tint in
theorem printed (s:J)(l:choices):
    stamps r m I survey plain top fit s l=seed fit station axes bare turn hand phase I survey plain m f K N per s l:=by
  exact WilsonIndependentConditionedPlacementArm.filed R _ _ _ _ _ _ (receipt s l.1) (tint s l.1) _ _ _ _ _

variable {fare:J→choices→ℝ}
variable (T:Assigned R (deck (G:=G) grade top fit) own V coins grant port (fun _=>choices)
  (stamps r m I survey plain top fit) fare u b host m K N)

include receipt tint in
theorem reported (s:J)(l:choices):publicDose (deck (G:=G) grade top fit s) (T.cuts s l) 1=
    WilsonIndependentConditionedPlacementDose.source V (deck (G:=G) grade top fit s) k N m K (seed fit station axes bare turn hand phase I survey plain m f K N per s l):=by
  rw [WilsonIndependentConditionedPlacementDose.original T,
    printed fit station axes bare turn hand phase I survey plain r receipt tint s l]

include receipt tint in
theorem original (s:J)(l:choices)(q:ℕ)(g:ℝ):
    sample V (deck (G:=G) grade top fit s) N m host q g (publicDose (deck (G:=G) grade top fit s) (T.cuts s l) 1)=
      sample V (deck (G:=G) grade top fit s) N m host q g (WilsonIndependentConditionedPlacementDose.source V (deck (G:=G) grade top fit s) k N m K
        (seed fit station axes bare turn hand phase I survey plain m f K N per s l)):=by
  rw [reported fit station axes bare turn hand phase I survey plain r receipt tint T s l]

include receipt tint in
theorem assembled_at (flag:J→Bool)(q:ℕ)(g:ℝ)(s:J)(c:Bool):
    assembled T (fun i im=>(flag i,im)) (fun _=>1) q g s c =
      sample V (deck (G:=G) grade top fit s) N m host q g (WilsonIndependentConditionedPlacementDose.source V (deck (G:=G) grade top fit s) k N m K
        (seed fit station axes bare turn hand phase I survey plain m f K N per s (flag s,c))):=original fit station axes bare turn hand phase I survey plain
    r receipt tint T s (flag s,c) q g

end YM.Integration.WilsonIndependentConditionedPlacementPorts
