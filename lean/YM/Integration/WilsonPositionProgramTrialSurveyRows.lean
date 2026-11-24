import YM.Integration.WilsonPositionProgramTrialFittedSurvey
import YM.Integration.WilsonPositionProgramTrialFittedHead

/-! Every cofunded component uses its own honest Wick inverse on the shared vector. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialSurveyRows
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonMaxwellThermometerSurveyCourse (shelf)
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonPositionProgramTrialFittedTable (head)
open WilsonPositionProgramTrialFittedSurvey (stamp)
open scoped BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}


def pure (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(K:ℕ)(z:(i:Fin (a+1))→Alma (Q i).F→ℝ):Herit Q:=
  fun i=>head ((Wray L O (Q i).ans (Q i).path K K)⁻¹ *ᵥ z i)

def Chart (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(j:ℕ):Prop:=
  ∀m K:ℕ,j ≤ m → m ≤ K → (∀(v:Herit Q)(s:Fin (a+1)),
    let X:=stamp L O Q m K v
    let T:=normalized L O Q X m K
    steep L O (Q s).ans (Q s).path K m (K-m) (T s)=v s) ∧
    (∀(z:(i:Fin (a+1))→Alma (Q i).F→ℝ), (∀i b,(Q i).h≠weight (Q i).F b → z i b=0) →
      ∀s,fee (stamp L O Q m K (pure L O Q K z)) 0 s=∑b,‖z s b‖)

theorem original (R:Run G)(W:XSpace.Initialize G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (simple:G.Simple)(s:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices s R.kit)
    (survey:prices W R.kit)(big:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) l d fit) ≤ k):
    ∀ᶠ j:ℕ in atTop,∀tag,Chart R.family.path.levels R.metals.O (shelf W l d fit tag) j:=by
  filter_upwards [WilsonMaxwellThermometerSurveyCourse.original R W l d fit simple s funded survey big rails cap] with j sale
  obtain ⟨_,Y,levels,cash,_,home,_,_,_,all⟩:=sale
  intro tag m K late before
  let Q:=shelf W l d fit tag
  obtain ⟨rows,_⟩:=all tag
  have entered (i):((rows i).some.p.f.arch).V.anchor ≤ m:=by rw [(rows i).some.p.tap,home];exact late
  constructor
  · intro v i X T
    let board:=(rows i).some
    have read:=(WilsonPositionProgramTrialFittedLens.original _ (Q i) board.p.f.arch (entered i) before le_rfl (v i)).2.1
    simpa only [T,X,normalized,stamp,board.p.lands,board.p.modes,levels,cash] using read
  · intro z paid i
    let b:=(rows i).some
    let L:=R.family.path.levels
    let O:=R.metals.O
    have raw:=WilsonPositionProgramTrialFittedHead.original _ (Q i) b.p.f.arch (entered i) before le_rfl (z i) (paid i)
    have each (u:Alma (Q i).F):PowerSeries.coeff 0 ((stamp L O Q m K (pure L O Q K z)) i u)=z i u:=by
      simpa only [L,O,stamp,pure,b.p.lands,b.p.modes,levels,cash] using congrFun raw u
    unfold fee
    apply Finset.sum_congr rfl
    intro u _
    change (∑t:Fin 1,‖PowerSeries.coeff t.val ((stamp L O Q m K (pure L O Q K z)) i u)‖)=_
    rw [Fin.sum_univ_one]
    exact congrArg norm (each u)

end YM.Integration.WilsonPositionProgramTrialSurveyRows
