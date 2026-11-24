import YM.Integration.WilsonPositionProgramTrialSurveyRows

/-! The actual fitted field clock is a two-sided change of coordinates at every
original nonbare date, for each independently enrolled field and the unit. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialReverseLens
open Function Filter Finset Lattice Wilson RG RG.Supply Precision XSpace PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonMaxwellThermometerSurveyIncome (master prices)
open WilsonOriginalThermometerPalette (levels)
open WilsonPositionProgramInvertedStencil (packet)
open WilsonPositionProgramInversionMaterial (ceiling dose)
open WilsonPositionProgramTrialFittedSurvey (stamp)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Classical BigOperators

open WilsonPositionProgramInvertedStencil (packet)
open WilsonMaxwellThermometerSurveyCourse (shelf)
open WilsonCoeffUV.Wheel.Flooring


open Wilson RG RG.Supply Precision Source Labels WilsonCoeffUV.Bank.Carp
open WilsonPositionProgramTrialFittedLens (ticket matrix compose)
variable {G:Gauge}{h D k u e:ℕ}

def received (L:Levels G)(O:ChartRatio G)(Q:SealR G)(m K N:ℕ)(X:Q.Rider):Q.Rider:=
  steep L O Q.ans Q.path N m (K-m) (PermuteLens L O Q N m X)

theorem field (H:Hol G)(Q:SealR G){U V:Credit}(T:Theatre H Q.ans Q.path e U V)
    {m K N:ℕ}(entered:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)(X:Q.Rider):
    ticket T.V.draws T.V.paid Q N m K (received T.V.draws T.V.paid Q m K N X)=X:=by
  have visit:m+(K-m) ≤ N:=by omega
  have unit:IsUnit (Wray T.V.draws T.V.paid Q.ans Q.path N m).det:=
    wick_unit _ (production T (before.trans live) entered).1 _ _
  rw [received,ticket,Street_up T _ entered visit]
  change matrix _ (matrix _ X)=_
  rw [compose,Matrix.mul_nonsing_inv _ unit]
  funext i
  simp [matrix,Matrix.one_apply]

variable {a:ℕ}(R:Run G)(W:Initialize G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
def input (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(m K N:ℕ)(X:Herit Q):Herit Q:=
  fun i=>received L O (Q i) m K N (X i)

local notation "L" => R.family.path.levels
local notation "O" => R.metals.O

theorem original (simple:G.Simple)(s:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices s R.kit)
    (pub:prices W R.kit)(big:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) l d fit) ≤ k):
    ∀ᶠ j:ℕ in atTop,∀tag m K N,j ≤ m → m ≤ K → K ≤ N →
    let Q:=shelf W l d fit tag
    ∀X:Herit Q, (fun i=>ticket L O (Q i) N m K (input L O Q m K N X i))=X:=by
  filter_upwards [WilsonMaxwellThermometerSurveyCourse.original R W l d fit simple s funded pub big rails cap] with j sale
  obtain ⟨_,Y,levels,cash,_,home,_,_,_,all⟩:=sale
  intro tag m K N late before live Q X
  obtain ⟨rows,_⟩:=all tag
  funext i
  let b:=(rows i).some
  have entered:b.p.f.arch.V.anchor ≤ m:=by rw [b.p.tap,home];exact late
  have paid:=field _ (Q i) b.p.f.arch entered before live (X i)
  simpa only [input,b.p.lands,b.p.modes,levels,cash] using paid

end YM.Integration.WilsonPositionProgramTrialReverseLens
end
