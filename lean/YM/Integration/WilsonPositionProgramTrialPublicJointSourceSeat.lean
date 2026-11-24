import YM.Integration.WilsonPositionProgramTrialPublicJointSourceStable
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceVote

/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceSeat
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

theorem common (X:CutsP H Q.ans Q.path rail E W B V)(P A:TowerS G Q.D)
    (equal:projected X.ax X.tx Q X.m X.ceilC k P=projected X.ax X.tx Q X.m X.ceilC k A):
    seen X P=seen X A:=by
  have before:X.m ≤ X.ceilC:=Nat.le_add_right .. 
  have inv:IsUnit (Wray X.ax X.tx Q.ans Q.path X.ceilC X.m).det:=
    wick_unit _ (production X.L.L before X.ha).1 _ _
  have width:X.ceilC-X.m=X.i:=Nat.add_sub_cancel_left ..
  unfold projected at equal
  rw [width] at equal
  exact (cancel _ (seen X P) inv).symm.trans ((congrArg (matrix (Wray X.ax X.tx Q.ans Q.path X.ceilC X.m)⁻¹) equal).trans (cancel _ (seen X A) inv))

variable {n u h' D':ℕ}(R:Run G)(U:Initialize G)(d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "J" i:arg => port R U d D fit false i
local notation "S" i:arg => port R U d D fit true i

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices U R.kit)(big:h'<D')(outer:Rails h' k w e)(cap:capP (deck (G:=G) d D fit) ≤ k)
    (i:Fin (n+1))(stock:Rails (d i) k u e):
    ∃AJ AS:Alma (R.family.labels.level (d i))→ℝ,(∀a,0 ≤ AJ a) ∧ (∀a,0 ≤ AS a) ∧ ∃C:Credit,
    ∀ᶠ j:ℕ in atTop,∀(X:CutsP (hol G) (J i).ans (fit i) stock E W B V),
      X.ax=L → X.tx=O → j ≤ X.m → ∀b:(J i).Rider,
      let c:=received L O (J i) X.m X.ceilC X.ceilC b
      let a:=refill R U d D fit X.m X.ceilC i b
      let P:=Shrine (plate (J i).ans (fit i)) c
      let A:=Shrine (plate (S i).ans (fit i)) a
      ∃Y:CutsP (hol G) (J i).ans (fit i) stock E W B V,
        Y.L=X.L ∧ Y.L'=X.L' ∧ Y.m=X.m ∧ Y.i=X.i ∧ Y.N=X.ceilC ∧ Y.pt=P-A ∧
        Y.fuel=charge e c AJ+charge e a AS ∧ Y.tileP=0 ∧ P-A=Y.springP Y.i ∧
        (∀j<X.i,Spout L O X.ceilC (X.m+j) (d i) k (Y.springP (j+1))=Y.springP j) ∧
        ∀t ≤ e,∀j ≤ X.i,∀r,Fruit 0 1 u ((Y.springP j).2 t r)
          (C.buy Y.Age*Real.exp (-(R.family.S.scale X.ceilC-R.family.S.scale (X.m+j))/4)*
            (charge e c AJ+charge e a AS)):=by
  obtain ⟨AJ,nJ,paidJ⟩:=WilsonIndependentMatchedFiledIncome.named R U false (d i) (fit i) stock.hk e u
  obtain ⟨AS,nS,paidS⟩:=WilsonIndependentMatchedFiledIncome.named R U true (d i) (fit i) stock.hk e u
  obtain ⟨C,commonPrice⟩:=WilsonIndependentMatchedKernelResidual.original (hol G) (J i).ans (fit i) stock E W B V
  refine ⟨AJ,AS,nJ,nS,C,?_⟩
  filter_upwards [WilsonPositionProgramTrialPublicJointSourceVote.original R U d D fit simple v funded pub big outer cap] with j vote
  intro X ax tx live b c a P A
  have before:X.m ≤ X.ceilC:=Nat.le_add_right ..
  obtain ⟨_,_,test⟩:=vote X.m X.ceilC live before i b
  obtain ⟨_,sur,reg⟩:=test k stock.hk
  have joint:projected X.ax X.tx (J i) X.m X.ceilC k P=projected X.ax X.tx (J i) X.m X.ceilC k A:=by
    rw [ax,tx];exact reg.trans sur.symm
  have same:=common (Q:=J i) X P A joint
  obtain ⟨pj,fj,bj⟩:=paidJ c
  obtain ⟨ps,fs,bs⟩:=paidS a
  obtain ⟨_,court⟩:=WilsonPositionProgramTrialPublicJointSourceStable.original X
  obtain ⟨Y,YL,YL',ym,yi,yn,yp,yf,yt,pure,st,_⟩:=court P A _ _ pj ps fj fs bj bs same
  refine ⟨Y,YL,YL',ym,yi,yn,yp,yf,yt,pure,by simpa only [ax,tx] using st,?_⟩
  intro t ht a' ha r
  have yy:Y.ax=L:=by change Y.L.L.V.draws=_;rw [YL];exact ax
  have cc:Y.ceilC=X.ceilC:=by change Y.m+Y.i=X.m+X.i;rw [ym,yi]
  have bill:=(commonPrice Y).2.2 t ht a' (yi ▸ ha) r
  change Fruit 0 1 u _ (C.buy Y.Age*Real.exp (-(Y.ax.S.scale Y.ceilC-Y.ax.S.scale (Y.m+a'))/4)*Y.fuel) at bill
  simpa only [yy,cc,ym,yf] using bill

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceSeat
