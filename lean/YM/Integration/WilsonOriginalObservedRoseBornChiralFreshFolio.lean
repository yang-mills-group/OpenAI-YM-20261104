import YM.Integration.WilsonOriginalObservedRoseBornChiralPeer

/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralFreshFolio
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

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:WilsonMaxwellThermometerSurveyIncome.prices W R.kit)(big:h<D₀)(rails:Rails h k u e)
    (cap:capP (deck (G:=G) d D fit) ≤ k)(stock:∀i,Rails (d i) k u e):
    let J:=port R W d D fit false
    ∃A:(i:Fin (n+1))→Bool→Alma (R.family.labels.level (d i))→ℝ,(∀i side a,0≤A i side a) ∧
    ∀ᶠ j:ℕ in atTop,∀(V:Realm G (e+1) C),V.draws=L → V.paid=O → ∀m K N,j ≤ m →
    ∀X:Courts (H:=hol G) (Q:=J) (v:=stock),stamp V X m K N →
    ∃Y:(i:Fin (n+1))→Bool→CutsP (hol G) (J i).ans (J i).path (stock i) C C C C,
      (∀i side,let c:=input R W d D fit side i m K (home (J i) (X i))
               let field:=Shrine (plate ((port R W d D fit side i).ans) (fit i)) c
               (Y i side).L=(X i).L ∧ (Y i side).L'=(X i).L' ∧ (Y i side).pt=field ∧
                 On (d i) (Y i side).pt ∧ (Y i side).fuel=charge e c (A i side) ∧
                 home (J i) (Y i side)=home (J i) (X i)) ∧
      ∀side:Fin (n+1)→Bool,stamp V (fun i=>Y i (side i)) m K K:=by
  intro J
  choose A nonneg issued using fun i side=>WilsonOriginalObservedRoseBornChiralPeer.original
    R W d D fit simple v funded pub big rails cap i (stock i) side
  refine ⟨A,nonneg,?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (issued i))] with j sale
  intro V draws ratio m K N age X old
  choose Y earned using fun i side=>sale i side (X i) ((old i).1.trans draws) ((old i).2.1.trans ratio)
    (age.trans (old i).2.2.1.ge) (home (J i) (X i))
  refine ⟨Y,?_,?_⟩
  · intro i side
    obtain ⟨school,dean,_,_,_,field,proper,cash,home₀⟩:=earned i side
    rw [(old i).2.2.1,(old i).2.2.2.1] at field cash
    exact ⟨school,dean,field,proper,cash,home₀⟩
  · intro side i
    obtain ⟨school,_,birth,length,prior,_⟩:=earned i (side i)
    obtain ⟨levels,chart,age₀,ceiling,_⟩:=old i
    exact ⟨(congrArg (fun l=>l.L.V.draws) school).trans levels,
      (congrArg (fun l=>l.L.V.paid) school).trans chart,birth.trans age₀,
      (congrArg₂ (·+·) birth length).trans ceiling,prior.trans ceiling⟩

end YM.Integration.WilsonOriginalObservedRoseBornChiralFreshFolio
