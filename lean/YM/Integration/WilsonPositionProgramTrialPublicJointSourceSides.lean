import YM.Integration.WilsonPositionProgramTrialPublicJointSourceMerit
import YM.Integration.WilsonIndependentMatchedPhysicalReturn

/-! The two complete compact source panels on one original fresh vacuum with their identical returned numerical coordinates on every leg. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceSides
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

open WilsonPositionProgramTrialPublicJointSourceWallet (row)
open WilsonPositionProgramTrialAccrued (home returns)
open WilsonIndependentMatchedPhysicalSector (stamp)
variable {G:Gauge}{n h H k u e:ℕ}(R:Run G)(W:Initialize G)
variable (d D:Fin (n+1) → ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "Q" => port R W d D fit false
local notation "C" => Credit.leanC
abbrev Courts (w:∀i,Rails (d i) k u e):=
  (i:Fin (n+1)) → CutsP (hol G) (Q i).ans (fit i) (w i) C C C C
theorem original (simple:G.Simple)(v:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices W R.kit)(big:h<H)(outer:Rails h k u e)(cap:capP (deck (G:=G) d D fit)  ≤  k)
    (w:∀i,Rails (d i) k u e):
    ∃A:∀(_:Bool)(i:Fin (n+1)),Alma (Q i).F → ℝ,(∀s i a,0 ≤ A s i a) ∧
    ∀ᶠ j:ℕ in atTop,∀(V:Realm G (e+1) C)(X:Courts R W d D fit w)(m K N:ℕ),
    V.draws=L  →  V.paid=O  →  stamp V X m K N  →  j ≤ m  →  m ≤ K  → 
    ∀b:(i:Fin (n+1)) → (Q i).Rider,∃Y:Bool → Courts R W d D fit w,
      (∀s,stamp V (Y s) m K K) ∧ ∀s i,
      let c:=row R W d D fit s m K i (b i)
      (Y s i).L=(X i).L ∧ (Y s i).L'=(X i).L' ∧
      (Y s i).pt=Shrine (plate (sectionAt R W s (d i)) (fit i)) c ∧
      (Y s i).fuel=charge e c (A s i) ∧ On (d i) (Y s i).pt ∧
      home (Q i) (Y s i)=b i ∧ (Y s i).tileP=received L O (Q i) m K K (b i):=by
  choose A nn input using fun (s:Bool)(i:Fin (n+1))=>WilsonIndependentMatchedFiledIncome.named R W s (d i) (fit i) (w i).hk e u
  refine ⟨A,nn,?_⟩
  filter_upwards [WilsonPositionProgramTrialPublicJointSourceVote.original R W d D fit simple v funded pub big outer cap] with j ballot
  intro V X m K N levels ratio issued live interval b
  let c:=(fun s i=>row R W d D fit s m K i (b i))
  let P:=(fun s i=>Shrine (plate (sectionAt R W s (d i)) (fit i)) (c s i))
  let Y (s:Bool)(i:Fin (n+1)):CutsP (hol G) (Q i).ans (fit i) (w i) C C C C:=
    WilsonIndependentMatchedKernelResidual.diagonal (X i).L (X i).L' (X i).he (X i).m (X i).i
      (X i).ceilC (X i).ha le_rfl (P s i) (input s i (c s i)).1 (charge e (c s i) (A s i))
      (input s i (c s i)).2.1 (input s i (c s i)).2.2
  have posted (s:Bool):stamp V (Y s) m K K:=fun i=>
    ⟨(issued i).1,(issued i).2.1,(issued i).2.2.1,(issued i).2.2.2.1,(issued i).2.2.2.1⟩
  refine ⟨Y,posted,?_⟩
  intro s i
  have seen_:=ballot m K live interval i (b i)
  have home_:home (Q i) (Y s i)=b i:=by
    have law:= (posted s i).1.trans levels
    have clock:= (posted s i).2.1.trans ratio
    have bottom:=(posted s i).2.2.1
    have top:=(posted s i).2.2.2.1
    have upper:=(posted s i).2.2.2.2
    have span:(Y s i).i=K-m:=by rw [←bottom,←top];exact (Nat.add_sub_cancel_left ..).symm
    unfold home
    rw [law,clock,upper,bottom,span,show (Y s i).pt=P s i from rfl]
    cases s
    · exact (seen_.2.2 k (w i).hk).2.2
    · exact (seen_.2.2 k (w i).hk).2.1
  have cash:=(returns (Q i) (Y s i)).1.symm
  rw [home_,(posted s i).1,levels,(posted s i).2.1,ratio,(posted s i).2.2.1,
    (posted s i).2.2.2.1,(posted s i).2.2.2.2] at cash
  have legal:On (d i) (P s i):=((Classical.choose_spec (WilsonIndependentMatchedFiledIncome.named R W s (d i) (fit i) le_rfl e u)).2 (c s i)).1
  exact ⟨rfl,rfl,rfl,rfl,legal,home_,cash⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceSides
