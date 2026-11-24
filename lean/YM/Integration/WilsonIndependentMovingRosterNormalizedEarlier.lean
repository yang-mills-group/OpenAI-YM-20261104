import YM.Integration.WilsonIndependentMovingRosterMarginOptics

/-! One earlier continuation credit and the whole moving source roster
share a single optical margin. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedEarlier
open Filter Finset RG Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.AuxPlates
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb PathCost Ore
open WilsonIndependentMovingRosterMarginOptics (Billed)
open WilsonIndependentMatchedCoverDate (age)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (count)
open RegulatorIR RegulatorIR.Ledger
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}{I J:Type}[Fintype I][Fintype J]

def Extended (R:Realm G (e+1) E)(prior C S:Credit)(d:ℕ)(rates:I→Credit)(s N:ℕ)(bill:ℝ):Prop:=
  ∀old m day:ℕ,s ≤ old → old ≤ m → m ≤ day → day ≤ N →
    ∀w:I→ℝ,(∀b,1 ≤ w b ∧ w b ≤ epoch R s N) →
      (prior.buy (age R old m)*(C.buy (age R m day)*R.cash S day*((ll R.draws day).L.val:ℝ)^d))*
        (∏b,(rates b).buy (w b)) ≤ bill

theorem ranked (R:Realm G (e+1) E)(s old m N:ℕ)(live:R.anchor ≤ s)
    (start:s ≤ old)(stop:old ≤ m)(top:m ≤ N):
    1 ≤ age R old m ∧ age R old m ≤ epoch R s N:=by
  have prepaid:=R.depth old (live.trans start)
  constructor
  · unfold age
    linarith only [prepaid,scales R.draws.S stop,Nat.cast_nonneg (α:=ℝ) (m-old)]
  · have cost:age R old m ≤ epoch R s m:=(window R s old m live start stop).2.2.1
    apply le_trans cost
    unfold WilsonSeparatedPrefixMovingCalendar.epoch
    linarith only [scales R.draws.S top]

theorem enter (R:Realm G (e+1) E)(prior C S:Credit)(d:ℕ)(rates:I→Credit)(s N:ℕ)(bill:ℝ)
    (live:R.anchor ≤ s)
    (all:Billed R C S d (fun x:Option I=>x.elim prior rates) s N bill):
    Extended R prior C S d rates s N bill:=by
  intro old m day first second inside last w within
  let age₀:=age R old m
  let weights (i:Option I):ℝ:=i.elim age₀ w
  have valid (i:Option I):1 ≤ weights i ∧ weights i ≤ epoch R s N:=by
    cases i with
    | none=>exact ranked R s old m N live first second (inside.trans last)
    | some i=>exact within i
  have receipt:=(all m day (first.trans second) inside last).2 weights valid
  rw [Fintype.prod_option] at receipt
  dsimp only [weights,Option.elim,age₀] at receipt
  calc
    _= (C.buy (age R m day)*R.cash S day*((ll R.draws day).L.val:ℝ)^d)*
      ((∏i,(rates i).buy (w i))*prior.buy (age R old m)):=by ring
    _≤bill:=by simpa only [mul_comm] using receipt

theorem original (V:XSpace.Run)(a phase:ℕ)(ha:0 < a)(hj:4 ≤ phase)
    (prior C S:J→Credit)(d:J→ℕ)(rates:I→Credit)(cap η:ℝ)(gain:0 < η):
    ∀ᶠ idx:ℕ in atTop,∀i:Requests a,i.val=idx → ∀(A:Levels G)(s:ℕ),
      (∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i →
        (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
          (WilsonIndependentExactPlate.S V a ha phase hj).pactP f) →
      ∀(R:Realm G (e+1) E),R.draws=A → R.anchor=s → R.y s ≤ cap →
        ∀q:J,Extended R (prior q) (C q) (S q) (d q) rates s (s+count V a i.val) ((V.step idx).spacing^(-η)):=by
  filter_upwards [(eventually_all).mpr fun q:J=>WilsonIndependentMovingRosterMarginOptics.original (G:=G) (e:=e) (E:=E)
    V a phase ha hj (C q) (S q) (d q) (fun t:Option I=>t.elim (prior q) rates) cap η gain]
      with idx certified i eq A s patches R drawn start quote q
  exact enter R (prior q) (C q) (S q) (d q) rates s _ _ start.le (certified q i eq A s patches R drawn start quote)

end YM.Integration.WilsonIndependentMovingRosterNormalizedEarlier

