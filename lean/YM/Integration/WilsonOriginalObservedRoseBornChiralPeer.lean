import YM.Integration.WilsonPositionProgramTrialPublicJointSourceSeat
import YM.Integration.WilsonOriginalObservedRoseBornChiralZeroTile

/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralPeer
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix cancel)
open WilsonPositionProgramTrialPublicJointSourceStable (seen)
open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical Topology

open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
variable {G:Gauge}{n k u e h D₀:ℕ}(R:Run G)(W:Initialize G)
variable (d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "C" => Credit.leanC

def input (side:Bool)(i:Fin (n+1))(m K:ℕ)(b:(port R W d D fit false i).Rider):Verse (R.family.labels.level (d i)):=
  if side then refill R W d D fit m K i b else received L O (port R W d D fit false i) m K K b

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:WilsonMaxwellThermometerSurveyIncome.prices W R.kit)(big:h<D₀)(rails:Rails h k u e)
    (cap:capP (deck (G:=G) d D fit) ≤ k)(i:Fin (n+1))(stock:Rails (d i) k u e)(side:Bool):
    let J:=port R W d D fit false i
    let S:=port R W d D fit side i
    ∃A:Alma (R.family.labels.level (d i))→ℝ,(∀a,0≤A a) ∧
    ∀ᶠ j:ℕ in atTop,∀(X:CutsP (hol G) J.ans J.path stock C C C C),X.ax=L → X.tx=O → j≤X.m →
    ∀b:J.Rider,
    let c:=input R W d D fit side i X.m X.ceilC b
    let field:=Shrine (plate S.ans (fit i)) c
    ∃Y:CutsP (hol G) J.ans J.path stock C C C C,
      Y.L=X.L ∧ Y.L'=X.L' ∧ Y.m=X.m ∧ Y.i=X.i ∧ Y.N=X.ceilC ∧
      Y.pt=field ∧ On (d i) Y.pt ∧ Y.fuel=charge e c A ∧ home J Y=b:=by
  intro J S
  obtain ⟨A,hA,chargePaid⟩:=WilsonIndependentMatchedFiledIncome.named R W side (d i) (fit i) stock.hk e u
  obtain ⟨_,_,own⟩:=WilsonIndependentMatchedFiledIncome.named R W side (d i) (fit i) (le_refl (d i)) e u
  refine ⟨A,hA,?_⟩
  filter_upwards [WilsonPositionProgramTrialPublicJointSourceVote.original R W d D fit simple v funded pub big rails cap] with j grant
  intro X ax tx begin₀ b c field
  obtain ⟨reach,pos,flow⟩:=chargePaid c
  let Y:=WilsonIndependentMatchedKernelResidual.diagonal X.L X.L' X.he X.m X.i X.ceilC X.ha le_rfl
    field reach (charge e c A) pos flow
  refine ⟨Y,rfl,rfl,rfl,rfl,rfl,rfl,(own c).1,rfl,?_⟩
  obtain ⟨_,_,vote⟩:=grant X.m X.ceilC begin₀ (Nat.le_add_right ..) i b
  obtain ⟨_,sur,reg⟩:=vote k stock.hk
  have price:projected L O J X.m X.ceilC k field=b:=by
    cases side
    · exact reg
    · exact sur
  have span:X.ceilC-X.m=X.i:=Nat.add_sub_cancel_left .. 
  change WilsonPositionProgramTrialFittedLens.matrix (Wray X.ax X.tx J.ans J.path X.ceilC X.m)
    (opal J.F (spools X.ax X.tx X.ceilC k (d i) X.m X.i field))=b
  simpa only [projected,span,ax,tx] using price

end YM.Integration.WilsonOriginalObservedRoseBornChiralPeer
