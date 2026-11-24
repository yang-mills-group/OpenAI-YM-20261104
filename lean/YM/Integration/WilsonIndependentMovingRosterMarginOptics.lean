import YM.Integration.WilsonIndependentMovingRosterMarginLedger

/-! A finite menu of genuine receiver tariffs and all the marked source
credits on the same public board can spend a single arbitrarily small
mesh power. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterMarginOptics
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RegulatorIR RegulatorIR.Ledger
open WilsonIndependentEvenPassport (count)
open WilsonIndependentExactPlate (Requests)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonIndependentMovingRosterMarginLedger (market local_cost)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}{I J:Type}[Fintype I]

private theorem fees (pay:I→Credit):∃F:Credit,∀z:ℝ,1 ≤ z → (∏i,(pay i).buy z) ≤ F.buy z:=by
  suffices ∀S:Finset I,∃F:Credit,∀z:ℝ,1 ≤ z → (∏i∈S,(pay i).buy z) ≤ F.buy z by
    exact this Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Credit.unit,fun z hz=>?_⟩
    simpa only [Finset.prod_empty] using Credit.unit.purchase hz
  | @insert a s ha ih =>
    obtain ⟨F,paid⟩:=ih
    refine ⟨(pay a).prodC F,fun z hz=>?_⟩
    rw [Finset.prod_insert ha,Credit.products]
    exact mul_le_mul_of_nonneg_left (paid z hz) (zero_le_one.trans ((pay a).purchase hz))

def Billed (R:Realm G (e+1) E)(C S:Credit)(d:ℕ)(pay:I→Credit)(s N:ℕ)(bound:ℝ):Prop:=
  ∀m j:ℕ,s ≤ m → m ≤ j → j ≤ N →
    let net:=C.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash S j*((ll R.draws j).L.val:ℝ)^d
    net ≤ bound ∧ ∀price:I→ℝ,(∀i,1 ≤ price i ∧ price i ≤ epoch R s N) →
      net*(∏i,(pay i).buy (price i)) ≤ bound

theorem original (V:XSpace.Run)(a phase:ℕ)(ha:0 < a)(hj:4 ≤ phase)(C S:Credit)(d:ℕ)(pay:I→Credit)
    (cap η:ℝ)(gain:0 < η):
    ∀ᶠ j:ℕ in atTop,∀i:Requests a,i.val=j → ∀(A:Levels G)(s:ℕ),
    (∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i →
      (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
        (WilsonIndependentExactPlate.S V a ha phase hj).pactP f) →
    ∀(R:Realm G (e+1) E),R.draws=A → R.anchor=s → R.y s ≤ cap →
      Billed R C S d pay s (s+count V a i.val) ((V.step j).spacing^(-η)):=by
  obtain ⟨F,fee⟩:=fees pay
  let tariff:=(market C S E d).prodC F
  filter_upwards [WilsonIndependentMovingRosterAllFineAge.original (e:=e+1) (E:=E) (G:=G)
    V a phase ha hj tariff cap η gain] with idx clock i same A s patch R draw anchor start
  let N:=s+count V a i.val
  let Z:=epoch R s N
  have live:R.anchor ≤ s:=anchor.le
  have root:s ≤ N:=Nat.le_add_right .. 
  have charge:=clock i same A s patch R draw anchor s N le_rfl root le_rfl start
  change tariff.buy Z ≤ _ at charge
  rw [show tariff.buy Z=(market C S E d).buy Z*F.buy Z from Credit.products ..] at charge
  have warm:1 ≤ Z:=(window R s s N live le_rfl root).1
  have paid:0 ≤ (market C S E d).buy Z:=zero_le_one.trans ((market C S E d).purchase warm)
  intro m j sm mj top net
  have single:=local_cost R C S d s m j N live sm mj top
  refine ⟨single.trans ((le_mul_of_one_le_right paid (F.purchase warm)).trans charge),?_⟩
  intro price within
  have roof: (∏i,(pay i).buy (price i)) ≤ F.buy Z:=
    (Finset.prod_le_prod (fun i _=>zero_le_one.trans ((pay i).purchase (within i).1))
      (fun i _=>(pay i).elder (within i).1 (within i).2)).trans (fee Z warm)
  exact (mul_le_mul single roof (Finset.prod_nonneg fun i _=>zero_le_one.trans ((pay i).purchase (within i).1)) paid).trans charge

theorem family [Fintype J](V:XSpace.Run)(a phase:ℕ)(ha:0 < a)(hj:4 ≤ phase)
    (C S:J→Credit)(d:J→ℕ)(pay:I→Credit)(cap η:ℝ)(gain:0 < η):
    ∀ᶠ j:ℕ in atTop,∀i:Requests a,i.val=j → ∀(A:Levels G)(s:ℕ),
    (∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i →
      (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
        (WilsonIndependentExactPlate.S V a ha phase hj).pactP f) →
    ∀(R:Realm G (e+1) E),R.draws=A → R.anchor=s → R.y s ≤ cap →
      ∀q:J,Billed R (C q) (S q) (d q) pay s (s+count V a i.val) ((V.step j).spacing^(-η)):=by
  filter_upwards [(eventually_all).mpr fun q=>original (G:=G) (E:=E) (e:=e)
    V a phase ha hj (C q) (S q) (d q) pay cap η gain] with j paid i idx A s patches R draw start mark q
  exact paid q i idx A s patches R draw start mark

end YM.Integration.WilsonIndependentMovingRosterMarginOptics

