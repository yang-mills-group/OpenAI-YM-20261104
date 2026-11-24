import YM.Integration.WilsonIndependentMatchedOwnHomeCoordinates
import YM.Integration.WilsonIndependentMatchedOwnHomeProfile
import YM.Integration.WilsonIndependentSpoutMasterArms
import YM.Integration.WilsonIndependentFittedProductClock

/-! Every arm is read on its prescribed date on one genuine running unmarked
history.  The identity takes place before the conditional integral. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeRoster
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentSpoutMasterArms (arm)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentFittedReportedFilm (funded)
open WilsonMarkedIndependentNormalizedElection (normalized)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{e n:ℕ}{U W:Credit}

theorem spacing (S:Schedule)(t m K:ℕ):paceT S t K=paceT S m K/paceT S m t:=by
  unfold paceT
  field_simp [(S.a_pos m).ne',(S.a_pos t).ne']

def away (A:Levels G)(O:ChartRatio G)(Q:SealR G)(φ:Rarity Q.D)(b:Q.Rider)
    (t m K N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  let T:=paceT A.S m t
  arm A O Q (scaled φ T (pace_pos ..)) (brought A O Q N t m b) t K N (y/T) o

theorem placed (Q:SealR G)(F:Theatre H Q.ans Q.path e U W)(φ:Rarity Q.D)(b:Q.Rider)
    (t m K N:ℕ)(awake:F.V.anchor ≤ t)(first:t ≤ m)(second:m ≤ K)(cap:K ≤ N)(y:ℝ)(o:CellR):
    let A:=F.V.draws
    let O:=F.V.paid
    away A O Q φ b t m K N y o=(paceT A.S m t)^Q.h • arm A O Q φ b m K N y o:=by
  intro A O
  have norm:received A O Q t K N (brought A O Q N t m b)=received A O Q m K N b:=
    (WilsonIndependentMatchedOwnHomeCoordinates.original Q F N K t m awake first second cap b).1
  unfold away arm
  rw [norm,spacing A.S t m K]
  exact WilsonIndependentMatchedOwnHomeProfile.original _ _ _ (pace_pos ..) _ _ (pace_pos ..) _ _

theorem cash (c:ℝ)(P:Era G ℝ):funded (PowerSeries.C c) P=c • P:=
  Prod.ext (funext fun _=>purePayment ..) (purePayment ..)

theorem real_product (P:Fin (n+1)→Era G ℝ)(c:Fin (n+1)→ℝ):
    MassP G ℝ n (fun i=>c i • P i)=(∏i,c i) • MassP G ℝ n P:=by
  simp_rw [←cash]
  rw [WilsonIndependentFittedProductClock.ordinary,map_prod]

theorem original (R:Realm G (e+1) U)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(b:Herit Q)
    (home:Fin (n+1)→ℕ)(m K N:ℕ)(awake:∀i,R.anchor ≤ home i)(first:∀i,home i ≤ m)
    (second:m ≤ K)(cap:K ≤ N)(ear:HorizonP H R W W Q)(y:ℝ)(o:CellR):
    let A:=R.draws
    let O:=R.paid
    MassP G ℝ n (fun i=>away A O (Q i) (φ i) (b i) (home i) m K N y o)=
      (∏i,(paceT A.S m (home i))^(Q i).h) • Ashore Q A O φ (normalized A O Q b m N) m K N y o:=by
  intro A O
  have row (i:Fin (n+1)):away A O (Q i) (φ i) (b i) (home i) m K N y o=
      (paceT A.S m (home i))^(Q i).h • arm A O (Q i) (φ i) (b i) m K N y o:=by
    let P:PassportC H R (Q i) W W:=(ear i).some
    change away R.draws R.paid _ _ _ _ _ _ _ _ _=(paceT R.draws.S m (home i))^_ • arm R.draws R.paid _ _ _ _ _ _ _ _
    rw [←P.lands,←P.modes]
    exact placed (Q i) P.f.arch (φ i) (b i) (home i) m K N (P.tap.symm ▸ awake i) (first i) second cap y o
  rw [funext row,real_product]
  rfl

end YM.Integration.WilsonIndependentMatchedOwnHomeRoster
end
