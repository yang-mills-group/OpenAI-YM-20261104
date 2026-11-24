import YM.Integration.WilsonNeutralTwoPrintPathItinerary

/-! The independently reprinted whole old source is submitted at its literal child offsets. Its connected pupil on the true course has the same covered coefficients as the original uninterrupted fixed-site itinerary, at every retained degree and angular rank. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathBooked
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint (Issued printed)
open WilsonMarkedIndependentEnrolledPeriod (registered)


open WilsonReceivedDatedVerseReprint (printed Issued)
open WilsonReceivedCanonicalVerseTrial (result)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h:I→ℕ}
variable (R:Run G)(k K:I→ℕ)(κ:(j:I) → Knob (h j))(pt:I → Chamber)


open WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Rolls
open Work.F08 WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Cadenza
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonReceivedDatedVerseReprint WilsonReceivedCompactVerseEntrance
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily


open WilsonReceivedFixedDigitHistory (Digits itinerary)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCoverGrade (Same)

open WilsonCapturedPrimaryWeakTrialFixedInput (places)
def route {L:Levels G}(same:L=R.family.path.levels)(cells:Digits R.family.path.levels I):Digits L I:=same.symm ▸ cells
open FundedMarkedPathSelection (Input output)

omit [Fintype I] [DecidableEq I] in
private theorem coordinates {L:Levels G}(same:L=R.family.path.levels)(cells:Digits R.family.path.levels I)
    (j:ℕ)(y:I → Cover):
    (fun v=>(ll L j).L.val • y v+lift (route R same cells j v))=
      chartIn (loose R.family.path.levels j) y (cells j):=by
  subst L
  rfl

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠj:ℕ in atTop,∀b,j<b → ∃s A:ℝ,0<s ∧ 1≤A ∧
    ∀(N:ℕ),b≤N → ∀(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor≤j)
      (same:Y.draws=R.family.path.levels),Y.paid=R.metals.O → (Y.mint (j+1) (by omega)).σ ≤ s →
    ∀(S:Finset I)(cells:Digits R.family.path.levels I)(q:(i:I)→Choice R k i),
    let old:=fixed R k κ pt N b (j+1) cells q
    let offset:=fun (_:I → Cover)=>route R same cells j
    ∃X:Input Y lo S k h A,X.offsets=offset ∧
      (∀y,X.familyAt y=(submit old k e) (fun v=>(ll Y.draws j).L.val • y v+lift (offset y v))) ∧
      (∀y J,Same e (output X J N y) (fixed R k κ pt N b j cells q y J)):=by
  obtain ⟨_,_,birth⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e zero_lt_one
  obtain ⟨j₀,clock⟩:=eventually_atTop.1 (WilsonReceivedFixedDigitCanonical.original R k κ pt simple quiet price funded e)
  filter_upwards [eventually_ge_atTop j₀] with j late
  intro b jb
  obtain ⟨s,A,hs,ha,fare⟩:=clock (j+1) (by omega) b jb
  refine ⟨s,A,hs,ha,?_⟩
  intro N after Y lo same coin width S cells q old offset
  have well:Wellness k old:=WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N
    cells simple R.alloy.B.ratio _ (birth q).1 _ _ (by omega)
  have wallet:CoverBill old e s A:=fun p t a da r=>((fare N after 1 cells q).1 p t a da r).access
  have book:=WilsonReceivedCompactVerseEntrance.original old well hs ha wallet
  let atChild (y:I → Cover):I → Cover:=fun v=>(ll Y.draws j).L.val • y v+lift (offset y v)
  let X:Input Y lo S k h A:={
    familyAt:=fun y=>(submit old k e) (atChild y)
    offsets:=offset
    empty:=fun y=>book.2.1.quiet' _
    degree:=fun y=>book.2.1.level' _
    price:=by
      intro y t _ a da r
      rw [(book.2.2.1 (atChild y) t a da).1]
      exact (wallet (atChild y) t a da r).shave width }
  refine ⟨X,rfl,fun _=>rfl,?_⟩
  intro y J
  have child:atChild y=chartIn (loose R.family.path.levels j) y (cells j):=by
    exact coordinates R same cells j y
  change Same e (logO Y.draws Y.paid j N ((submit old k e) (atChild y)) k J) _
  rw [same,coin,child,WilsonNeutralTwoPrintPathItinerary.unroll R k κ pt N b j jb cells q y J]
  exact WilsonNeutralTwoPrintPathItinerary.step k _ _ N j (fun t u hu=>(book.2.2.1 _ t u hu).1) J

end YM.Integration.WilsonNeutralTwoPrintPathBooked
end
