import YM.Integration.WilsonPositionProgramTrialPublicJointSourceSeat
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceWallet

/-! Both actual native sections have their own paid stable projection on the
same original levels, ratio, interval and report, including the surveyed
section when it acts as the inverse bank. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceCampus
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonPositionProgramTrialPublicJointSourceVote (port)
open WilsonMaxwellThermometerSurveyIncome (master prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G:Gauge}{n k u e:ℕ}(R:Run G)(W:Initialize G)(d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

def Campus (side:Bool)(i:Fin (n+1))(v:Rails (d i) k u e)(j:ℕ):Prop:=
  let Q:=port R W d D fit side i
  ∃(Y:Torch (hol G) Q.ans (fit i) v CC CC CC)(A:ChorusLine (hol G) Q.ans (fit i) e CC CC CC),
    Y.L.V.draws=L ∧ Y.L.V.paid=O ∧ Y.L.V.y=zz L ∧ Y.L.V.anchor=j ∧ A.arch=Y.L

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices W R.kit)(i:Fin (n+1))(stock:Rails (d i) k u e)(cap:capP (deck (G:=G) d D fit) ≤ k):
    ∀ᶠ j:ℕ in atTop,∀side,Campus R W d D fit side i stock j:=by
  let M:=master W
  let Q:=fun a=>BayV M (d a) (D a) (fit a)
  have receipt:=reported (hol G) M pub.1 pub.2
  have capacity:capP Q ≤ k:=cap
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded (fit i) stock d D fit cap,
    PortsTogether simple (chart_ok G) R.alloy.B.valid receipt tendsto_id (fit i) stock Q (fun _=>rfl) capacity] with j reg sur
  intro side
  cases side with
  | false =>
    obtain ⟨A,Y,ax,tx,clock,age,joined,_⟩:=reg
    exact ⟨Y,A,ax,tx,clock,age,joined⟩
  | true =>
    obtain ⟨A,Y,ax,tx,clk,j0,_,joined,rest⟩:=sur
    exact ⟨Y,A,joined ▸ ax,joined ▸ tx.trans funded.1.symm,joined ▸ clk,joined ▸ j0,joined⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceCampus
