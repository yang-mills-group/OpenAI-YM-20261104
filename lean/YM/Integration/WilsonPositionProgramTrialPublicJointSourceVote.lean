import YM.Integration.WilsonPositionProgramTrialPublicJointSourceExchange
import YM.Integration.WilsonMaxwellThermometerSurveyCourse
import YM.Integration.WilsonIndependentMatchedFreshWhole

/-! A single re-entry of a measured public source on the authentic mixed finite course. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceVote
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMaxwellThermometerSurveyCourse (shelf)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialPublicJointSourceExchange (change carried)
open WilsonIndependentMatchedFreshWhole (projected)
open scoped BigOperators Classical Topology

variable {G:Gauge}{n h H k u e:ℕ}(R:Run G)(W:Initialize G)
variable (d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "C" => Credit.leanC

abbrev port (s:Bool)(i:Fin (n+1)):SealR G:=
  ⟨d i,R.family.labels.level (d i),D i,sectionAt R W s (d i),fit i⟩

def refill (m K:ℕ)(i:Fin (n+1))(b:Verse (R.family.labels.level (d i))):Verse (R.family.labels.level (d i)):=
  steep L O (sectionAt R W true (d i)) (fit i) K m (K-m)
    (PermuteLens L O (port R W d D fit false i) K m b)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices W R.kit)(big:h<H)(rails:Rails h k u e)(cap:capP (deck (G:=G) d D fit) ≤ k):
    ∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K → ∀i (b:Verse (R.family.labels.level (d i))),
      let J:=port R W d D fit false i
      let S:=port R W d D fit true i
      let c:=received L O J m K K b
      let a:=refill R W d D fit m K i b
      a=change S.ans J.ans (fit i) L O m K c ∧
      change J.ans S.ans (fit i) L O m K a=c ∧
      ∀r,d i ≤ r →
        opal J.F (spools L O K r (d i) m (K-m) (Shrine (plate S.ans (fit i)) a))=
          PermuteLens L O J K m b ∧
        projected L O J m K r (Shrine (plate S.ans (fit i)) a)=b ∧
        projected L O J m K r (Shrine (plate J.ans (fit i)) c)=b:=by
  filter_upwards [WilsonMaxwellThermometerSurveyCourse.original R W d D fit simple v funded pub big rails cap] with j course
  obtain ⟨_,chair,levels,ratio,_,gate,_,_,_,seats⟩:=course
  intro m K late before i b J S c a
  let f:AheadT (hol G) chair.L.V C C J C:=((seats (fun _=>false)).1 i).some
  let g:AheadT (hol G) chair.L.V C C S C:=((seats (fun _=>true)).1 i).some
  have ef:f.p.f.arch.V.anchor ≤ m:=by rw [f.p.tap,gate];exact late
  have eg:g.p.f.arch.V.anchor ≤ m:=by rw [g.p.tap,gate];exact late
  have reach:m+(K-m) ≤ K:=by omega
  have ret:street L O J.ans (fit i) K m (K-m) c=PermuteLens L O J K m b:=by
    simpa only [c,received,f.p.lands,f.p.modes,levels,ratio] using Street_up f.p.f.arch (PermuteLens L O J K m b) ef reach
  have give:street L O S.ans (fit i) K m (K-m) a=PermuteLens L O J K m b:=by
    simpa only [a,refill,g.p.lands,g.p.modes,levels,ratio] using Street_up g.p.f.arch (PermuteLens L O J K m b) eg reach
  refine ⟨?_,?_,?_⟩
  · change a=steep L O S.ans (fit i) K m (K-m) (street L O J.ans (fit i) K m (K-m) c)
    rw [ret];rfl
  · change steep L O J.ans (fit i) K m (K-m) (street L O S.ans (fit i) K m (K-m) a)=c
    rw [give];rfl
  · intro r room
    have genuine:=carried S.ans (fit i) g.p.f.arch m K eg before room a
    rw [g.p.lands,g.p.modes,levels,ratio,give] at genuine
    have registered:=WilsonIndependentMatchedFreshWhole.returned (hol G) J f.p.f.arch m K ef before room b
    rw [f.p.lands,f.p.modes,levels,ratio] at registered
    have start:=carried J.ans (fit i) f.p.f.arch m K ef before room c
    rw [f.p.lands,f.p.modes,levels,ratio,ret] at start
    refine ⟨genuine,?_,registered⟩
    change WilsonPositionProgramTrialFittedLens.matrix _ _=b
    rw [genuine,←start]
    exact registered

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceVote
