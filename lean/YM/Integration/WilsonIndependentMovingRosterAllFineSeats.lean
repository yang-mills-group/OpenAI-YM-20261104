import YM.Integration.WilsonIndependentCutJoinPassport
import YM.Integration.WilsonIndependentMovingRosterAllFine

/-! A single original auxiliary mint supplies the finite rank and moment
requests for the fine and middle joins and the specific filed master sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAllFineSeats
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentCutJoinPassport (All)
open scoped BigOperators Topology Classical

local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{e n height seats:ℕ}

/-- Test the actual native source frame at its own horizon. -/
def Named (M:Master H)(height seats:ℕ)(Q:SealR G):Prop:=
  Q.h ≤ height ∧ Q.D ≤ seats ∧ BayV M Q.h Q.D Q.path=Q

structure Elected (M:Master H)(R:Realm G (e+1) C)(height seats:ℕ):Prop where
  dorm k u:k ≤ seats → u ≤ seats → Dormitory R k u C
  spring k u b:k ≤ b → b ≤ seats → u ≤ seats → SpringD R k u b C
  mark (Q:SealR G):Named M height seats Q → Nonempty (PassportC H R Q C C)

/-- Use the very realm already assigned to the joined return. Every
individual source keeps its own elected section and dimension. -/
theorem original (M:Master H)(A:Levels G)(chart:ChartRatio G)(y:ℕ→ℝ)(s:ℕ)
    (grant:All M A chart y e s height seats)(R:Realm G (e+1) C)
    (draw:R.draws=A)(quiet:R.paid=chart)(tariff:R.y=y)(anchor:R.anchor=s)
    (rates:∀k u d:ℕ,k+d ≤ seats → u ≤ seats → Dormitory R k u C ∧ SpringD R k u (k+d) C):
    Elected M R height seats:=by
  constructor
  · intro k u h hu
    exact (rates k u 0 (by omega) hu).1
  · intro k u b lo hi hu
    have book:= (rates k u (b-k) (by omega) hu).2
    rwa [show k+(b-k)=b by omega] at book
  · intro Q word
    obtain ⟨W,source,clock,price,home,_⟩:=grant Q.h Q.D Q.path word.1 word.2.1
    have issued:Nonempty (PassportC H R (BayV M Q.h Q.D Q.path) C C):=
      ⟨⟨W,source.trans draw.symm,clock.trans quiet.symm,price.trans tariff.symm,home.trans anchor.symm⟩⟩
    rwa [word.2.2] at issued

theorem roster {M:Master H}{R:Realm G (e+1) C}(sold:Elected M R height seats)
    (Q:Fin (n+1)→SealR G)(F:SealR G)(near:∀i,Named M height seats (Q i))(far:Named M height seats F):
    HorizonP H R C C Q ∧ Nonempty (PassportC H R F C C):=
  ⟨fun i=>sold.mark (Q i) (near i),sold.mark F far⟩

/-- The required capacity is fixed by the grades, the moment and the requested
spatial power. It applies to every thermal order. -/
def needed (k u target:ℕ):ℕ:=2*k+2*u+target+2

theorem finance {M:Master H}{R:Realm G (e+1) C}(sold:Elected M R height seats)
    (Q:Fin (n+1)→SealR G)(F:SealR G)(u target:ℕ)(budget:needed (F.h+capP Q) u target ≤ seats):
    let k:=F.h+capP Q
    let τ:=target+k
    let a:=F.h+(u+τ)
    let b:=capP Q+F.h+(u+τ+2)
    SpringD R k u b C ∧ SpringD R k u a C ∧
    SpringD R (capP Q) (u+a) (capP Q+(u+a+2)) C ∧
    Dormitory R (capP Q) (u+a) C ∧ Dormitory R k u C ∧
    SpringD R k u (F.h+(u+τ+2)) C ∧
    SpringD R (capP Q) (u+(F.h+(u+τ+2))) (capP Q+2) C ∧
    Dormitory R (capP Q) (u+(F.h+(u+τ+2))) C:=by
  dsimp only [needed] at budget
  dsimp only
  exact ⟨sold.spring _ _ _ (by omega) (by omega) (by omega),
    sold.spring _ _ _ (by omega) (by omega) (by omega),
    sold.spring _ _ _ (by omega) (by omega) (by omega),sold.dorm _ _ (by omega) (by omega),
    sold.dorm _ _ (by omega) (by omega),sold.spring _ _ _ (by omega) (by omega) (by omega),
    sold.spring _ _ _ (by omega) (by omega) (by omega),sold.dorm _ _ (by omega) (by omega)⟩

end YM.Integration.WilsonIndependentMovingRosterAllFineSeats
