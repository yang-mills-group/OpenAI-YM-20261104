import YM.Integration.WilsonIndependentFittedOpticalBallot

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedBallotReserve
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentFittedStoppedWage (numerical)
open WilsonIndependentFittedPivotCash (gross)
open WilsonIndependentFittedMixedCash (embed bill)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentEvenPassport (count old)
open WilsonIndependentExactPlate (Requests)
open RegulatorIR RegulatorIR.Ledger
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

def receipt (X:CutsP H T p v E W K U)(s q:ℕ)(d:Verse F):ℝ:=
  ∑j,belt q (embed (clock X.ax X.tx X.N X.m s (d j)))

theorem reserve (X:CutsP H T p v E W K U)(s q:ℕ)(d:Verse F)(A:ℝ)
    (paid:gross X s q 1 d≤numerical X s q 1 d+2*|(1:ℝ)|^(q+1)*A):
    receipt X s q d≤A:=by
  unfold receipt
  unfold gross numerical bill at paid
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at paid
  simp only [abs_one,one_pow,mul_one] at paid
  linarith

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit)
    (run:XSpace.Run)(base phase:ℕ)(ha:0<base)(good:4≤phase)(B η:ℝ)(positive:0<η):
    ∀ᶠ idx:ℕ in atTop,∀(i:Requests base),i.val=idx →
      let δ:=(run.step i.val).spacing
      ∀(X:CutsP H T p v E W K U)(L:Torch H T p v E W K)(f:ℕ)(amp ξ fee:ℝ)(stem:TowerS G D),
      Filed X L run base i.val f amp δ ξ fee stem →
      L.L.V.anchor=f →
      (∀m≤count run base i.val,L.L.V.y (f+m)≤B) →
      (∀w:Flap (WilsonIndependentExactPlate.M run base),w.volW=i →
        (L.L.V.draws.clock.op (f+(count run base i.val-(w.offset+1))) 0).patch=
          (WilsonIndependentExactPlate.S run base ha phase good).pactP w) →
      ∀(stop:ℕ),stop≤old run base i.val →∀(q:ℕ),q≤e →∀a:ℝ,
        receipt X (f+stop) q (dose X (a/amp))≤
        (Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*(δ^(-((h:ℝ)+η))*(|a| * fee)):=by
  filter_upwards [WilsonIndependentFittedOpticalBallot.original H T p v E W K U run base phase ha good B η positive]
    with idx bid i hi δ X L f amp ξ fee stem field anchor ages acts stop older q hq a
  exact reserve X (f+stop) q (dose X (a/amp)) _ (bid i hi X L f amp ξ fee stem field anchor ages acts stop older q hq a 1)

end YM.Integration.WilsonIndependentFittedBallotReserve
