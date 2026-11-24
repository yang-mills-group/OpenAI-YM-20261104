import YM.Integration.WilsonOriginalObservedRoseBornChiralTender
import YM.Integration.WilsonMovingForkCorrectedRetained

/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralRegister
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

open WilsonIndependentMatchedPhysicalSector (stamp Courts)
open WilsonOriginalObservedRoseBornChiralPeer (input)

open WilsonIndependentMatchedFreshInverseIncome (age)
open WilsonIndependentMatchedProxyIncome (cost)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonOriginalObservedRoseBornChiralTender (plan size)
open WilsonPositionProgramTrialHomeDose (scaled)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:WilsonMaxwellThermometerSurveyIncome.prices W R.kit)(big:h<D₀)(rails:Rails h k u e)
    (cap:capP (deck (G:=G) d D fit) ≤ k)(stock:∀i,Rails (d i) k u e):
    let J:=port R W d D fit false
    ∃A:(i:Fin (n+1))→Bool→Alma (R.family.labels.level (d i))→ℝ,
    ∃P:Fin (n+1)→Bool→Credit,∃B:Fin (n+1)→Credit,(∀i side a,0≤A i side a) ∧
    ∀ᶠ j:ℕ in atTop,∀(V:Realm G (e+1) C),V.draws=L → V.paid=O → ∀m K N,j ≤ m → m ≤ K →
    ∀X:Courts (H:=hol G) (Q:=J) (v:=stock),stamp V X m K N → (∀i,(X i).vesselsC.y=zz L) →
    ∀b:∀i,(J i).Rider,
    ∃Y:(i:Fin (n+1))→Bool→CutsP (hol G) (J i).ans (J i).path (stock i) C C C C,
      (∀i side,let c:=input R W d D fit side i m K (b i)
               let field:=Shrine (plate ((port R W d D fit side i).ans) (fit i)) c
               let principal:=(Fintype.card (Alma (J i).F):ℝ)*(B i).buy (zz L m)*cost e (b i)
               let window:=age L (zz L) m K
               (Y i side).L=(X i).L ∧ (Y i side).L'=(X i).L' ∧ (Y i side).pt=field ∧
                 On (d i) (Y i side).pt ∧ (Y i side).fuel=charge e c (A i side) ∧
                 home (J i) (Y i side)=b i ∧ (Y i side).Age=window ∧
                 cost e (dose (Y i side) 1) ≤ principal*size (J i).F e ∧
                 (Y i side).fuel ≤ ((P i side).buy window*principal)*plan e (A i side)) ∧
      ∀side:Fin (n+1)→Bool,stamp V (fun i=>Y i (side i)) m K K:=by
  intro J
  choose A nn receipt using fun i side=>WilsonOriginalObservedRoseBornChiralPeer.original R W d D fit
    simple v funded pub big rails cap i (stock i) side
  obtain ⟨P,B,budget⟩:=WilsonOriginalObservedRoseBornChiralTender.original R W d D fit simple v funded pub big rails cap
  have bought:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (receipt i))
  refine ⟨A,P,B,nn,?_⟩
  filter_upwards [bought,budget] with j sale wage
  intro V draws ratio m K N early before X old resident b
  choose Y earned using fun i side=>sale i side (X i) ((old i).1.trans draws) ((old i).2.1.trans ratio)
    (early.trans (old i).2.2.1.ge) (b i)
  have allDates (side:Fin (n+1)→Bool):stamp (H:=hol G) (Q:=J) (v:=stock) V (fun i=>Y i (side i)) m K K:=by
    intro i
    obtain ⟨school,_,birth,length,prior,_⟩:=earned i (side i)
    obtain ⟨levels,chart,base,ceiling,_⟩:=old i
    exact ⟨(congrArg (fun l=>l.L.V.draws) school).trans levels,
      (congrArg (fun l=>l.L.V.paid) school).trans chart,birth.trans base,
      (congrArg₂ (·+·) birth length).trans ceiling,prior.trans ceiling⟩
  refine ⟨Y,?_,allDates⟩
  intro i side
  obtain ⟨school,dean,_,_,_,field,sound,cash,home₀⟩:=earned i side
  rw [(old i).2.2.1,(old i).2.2.2.1] at field cash
  have date:=allDates (fun _=>side) i
  have ax:(Y i side).ax=L:=date.1.trans draws
  have tx:(Y i side).tx=O:=date.2.1.trans ratio
  have base:(Y i side).m=m:=date.2.2.1
  have top:(Y i side).ceilC=K:=date.2.2.2.1
  have span:(Y i side).i=K-m:=by change (Y i side).m+(Y i side).i=K at top; omega
  have y:(Y i side).vesselsC.y=zz L:=(congrArg (fun l=>l.L.V.y) school).trans (resident i)
  have life:(Y i side).Age=age L (zz L) m K:=by
    change (Y i side).vesselsC.y (Y i side).m+((Y i side).ax.S.scale (Y i side).ceilC-
      (Y i side).ax.S.scale (Y i side).m)+((Y i side).i:ℝ)=_
    rw [y,ax,base,top,span]
    rfl
  have input₀:PermuteLens (Y i side).ax (Y i side).tx (J i) (Y i side).N (Y i side).m (home (J i) (Y i side))=
      dose (Y i side) 1:=by
    simpa only [scaled,one_smul] using (WilsonPositionProgramTrialHomeDose.original (J i) (Y i side) 1).1
  rw [ax,tx,date.2.2.2.2,base,home₀] at input₀
  have costed:=wage m K early before i (b i) side (A i side) (nn i side)
  exact ⟨school,dean,field,sound,cash,home₀,life, input₀ ▸ costed.1,cash.symm ▸ costed.2⟩

end YM.Integration.WilsonOriginalObservedRoseBornChiralRegister
