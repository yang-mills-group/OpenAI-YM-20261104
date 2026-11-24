import YM.Integration.WilsonIndependentConditionedPlacementDose
import YM.Integration.WilsonIndependentConditionedFolioCellResponse
import YM.Integration.WilsonIndependentConditionedPlacementPorts
import YM.Integration.WilsonIndependentConditionedBankRulerHearing
import YM.Integration.WilsonIndependentNotebookComplexCorners

/-! A single all-order coordinate on the selected ruler for both public preparations and both real components, uniformly over their actual received lattice addresses. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioStations
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

open WilsonIndependentNotebookComplexCorners (reader)
open WilsonIndependentConditionedFolioTerm (picks archive)
open WilsonIndependentConditionedFolioCellResponse (entry)
open WilsonOlderFreshHybridClock (flat)
open WilsonCoeffUV.Power PertExtension Metric Precision Exterior
local notation "closed_" => (fun (_:J) (_:Bool)=>false)
local notation "x" => R.family.S.a K/R.family.S.a m
local notation "F" => R.family.labels.level
variable (r:∀s,Bool→Resident R (grade s) f K N per target up live η)
variable {address:J→Bool→Site (R.family.side f per)}
variable (receipt:∀s c,Printed R (station s c) (axes s c) (bare s c) (turn s c) (hand s c) (address s c)
  (r s c).arm)
variable (tint:∀s c,(r s c).phase=phase s c)
variable {fare:J→choices→ℝ}
variable (T:Assigned R (deck (G:=G) grade top fit) own V coins grant port (fun _=>choices)
  (stamps r m I closed_ closed_ top fit) fare u b host m K N)

def ports (n p:Lattice.Cover):J → Lattice.Cover:=Fin.cons n (Fin.cons p (fun j=>j.elim0))

def quadrant (flag:J→Bool)(re im:Bool)(φ:(i:J)→Rarity (top i))(y:ℝ)(o:CellR)(q:ℕ)(g:ℝ):ℂ:=
  let component:=fun i:J=>if i=0 then re else im
  let pay:=fun i:J=>entry R (fun i=>station i (flag i)) m K N per (fun i=>axes i (flag i))
    (fun i=>bare i (flag i)) (fun i=>turn i (flag i)) (fun i=>hand i (flag i)) component (fun i=>phase i (flag i))
    i (φ i) y o
  ∑n∈canvasM (φ 0) x y,∑p∈canvasM (φ 1) x y,∑a:(F (grade 0)).Index,∑b:(F (grade 1)).Index,
    ((pay 0 n a*pay 1 p b*flat (archive R I grade fit (ports n p) N K host (picks R grade a b)) q g:ℝ):ℂ)

include receipt tint in
theorem original (flag:J→Bool)(re im:Bool)(φ:(i:J)→Rarity (top i))(y:ℝ)(o:CellR)(z:Fin 0→YForest G)(q:ℕ)(g:ℝ)
    (layout:V.draws=R.family.path.levels)(old:host ≤ m)(km:m ≤ K)(u₁:G.ColorIndex)
    (tags:∀ i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (simple:G.Simple)(prices:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices prices R.kit):
    reader T (fun s i=>(flag s,i)) (fun _=>1) φ y o z q g re im=
      quadrant (host:=host) (m:=m) (K:=K) (N:=N) (per:=per) fit station axes bare turn hand phase I
        flag re im φ y o q g:=by
  classical
  let component:=fun i:J=>if i=0 then re else im
  let idx:=fun i:J=>(flag i,component i)
  have grid:paceT V.draws.S m K=x:=by rw [layout];rfl
  rw [WilsonIndependentConditionedFolioCuts.original T _ old km live]
  unfold WilsonIndependentConditionedFolioCuts.bill quadrant
  dsimp only
  rw [grid]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro p _
  rw [WilsonIndependentConditionedPlacementPorts.printed fit station axes bare turn hand phase I closed_ closed_ r receipt tint,
    WilsonIndependentConditionedPlacementPorts.printed fit station axes bare turn hand phase I closed_ closed_ r receipt tint]
  exact WilsonIndependentConditionedFolioCellResponse.original R I fit (fun i=>station i (flag i)) m f K N per
    (fun i=>axes i (flag i)) (fun i=>bare i (flag i)) (fun i=>turn i (flag i)) (fun i=>hand i (flag i)) component
    (fun i=>phase i (flag i)) V layout (fun i=>(own i).hk) u₁ tags simple prices funded host (old.trans km) live
    φ y o (ports n p) z q g

end YM.Integration.WilsonIndependentConditionedFolioStations
end
