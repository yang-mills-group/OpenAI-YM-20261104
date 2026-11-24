import YM.Integration.WilsonPositionProgramTrialPublicJointSourceSeat
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceOperator
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceWallet

/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceMerit
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

variable {G:Gauge}{h k w e:ℕ}{Q:SealR G}{H:Hol G}{rail:Rails Q.h k w e}{E W B V:Credit}

variable {n u h' D':ℕ}(R:Run G)(U:Initialize G)(d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "J" i:arg => port R U d D fit false i
local notation "S" i:arg => port R U d D fit true i

open WilsonPositionProgramTrialPublicJointSourceWallet (tickets tuition)
open WilsonIndependentMatchedFreshInverseIncome (age)
theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices U R.kit)(big:h'<D')(outer:Rails h' k w e)(cap:capP (deck (G:=G) d D fit) ≤ k)
    (i:Fin (n+1))(stock:Rails (d i) k u e):
    ∃AJ AS A:Alma (R.family.labels.level (d i))→ℝ,(∀a,0 ≤ AJ a) ∧ (∀a,0 ≤ AS a) ∧
    (∀a,0 ≤ A a) ∧ ∃C W₀:Credit,
    ∀ᶠ j:ℕ in atTop,∀(X:CutsP (hol G) (J i).ans (fit i) stock E W B V),
      X.ax=L → X.tx=O → j ≤ X.m → ∀b:(J i).Rider,
      let c:=received L O (J i) X.m X.ceilC X.ceilC b
      let a:=refill R U d D fit X.m X.ceilC i b
      let P:=Shrine (plate (J i).ans (fit i)) c
      let A':=Shrine (plate (S i).ans (fit i)) a
      let cost:=charge e c AJ+W₀.buy (age L (zz L) X.m X.ceilC)*charge e c A*tickets e AS
      ∃Y:CutsP (hol G) (J i).ans (fit i) stock E W B V,
        Y.L=X.L ∧ Y.L'=X.L' ∧ Y.m=X.m ∧ Y.i=X.i ∧ Y.N=X.ceilC ∧ Y.pt=P-A' ∧
        Y.fuel ≤ cost ∧ Y.tileP=0 ∧ Y.pt=Y.springP Y.i ∧
        ∀t ≤ e,∀j ≤ X.i,∀r,Fruit 0 1 u ((Y.springP j).2 t r)
          (C.buy Y.Age*Real.exp (-(R.family.S.scale X.ceilC-R.family.S.scale (X.m+j))/4)*Y.fuel):=by
  obtain ⟨AJ,AS,nJ,nS,C,seats⟩:=WilsonPositionProgramTrialPublicJointSourceSeat.original
    (E:=E) (W:=W) (B:=B) (V:=V) R U d D fit simple v funded pub big outer cap i stock
  obtain ⟨A,nA,W₀,ops⟩:=WilsonPositionProgramTrialPublicJointSourceOperator.original R U d D fit simple v funded pub i stock cap
  refine ⟨AJ,AS,A false,nJ,nS,nA false,C,W₀ true,?_⟩
  filter_upwards [seats,ops,WilsonPositionProgramTrialPublicJointSourceVote.original R U d D fit simple v funded pub big outer cap] with j filed bounded book
  intro X ax tx live b c a P A' cost
  have before:X.m ≤ X.ceilC:=Nat.le_add_right ..
  have equal:= (book X.m X.ceilC live before i b).1
  have wallet:=tuition e a AS nS ((W₀ true).buy (age L (zz L) X.m X.ceilC)*charge e c (A false))
    (by intro t ht α;rw [show a= _ from equal];exact bounded X.m X.ceilC live before true false c t ht α)
  obtain ⟨Y,one,two,m',i',N',pt,fee,zero,stable,_,growth⟩:=filed X ax tx live b
  refine ⟨Y,one,two,m',i',N',pt,?_,zero,pt.trans stable,?_⟩
  · rw [fee];exact add_le_add_right wallet _
  · intro t ht j hj r
    rw [fee];exact growth t ht j hj r

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceMerit
