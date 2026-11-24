import YM.Integration.WilsonNeutralTwoPrintPathStart
import YM.Integration.WilsonNeutralTwoPrintPathFixed
import YM.Integration.WilsonReceivedCoverFaces

/-! On a fixed fine-site itinerary the incoming whole independent catalogue may be reprinted before each genuine reset. The retained covered output uses the original count of occupied source indices, including all lower subwords. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathItinerary
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

omit [Fintype I] in
theorem step (L:Levels G)(O:ChartRatio G)(N j:ℕ){E W:family G h}{e:ℕ}
    (registered:∀J,Same e (E J) (W J))(J:Finset I):
    Same e (logO L O j N E k J) (logO L O j N W k J):=by
  unfold logO
  apply WilsonReceivedCoverFaces.connected
  intro S
  exact WilsonReceivedCoverGrade.verse L O j N _ (WilsonReceivedCoverFaces.ordinary registered S)

theorem unroll (N b j:ℕ)(live:j<b)(cells:Digits R.family.path.levels I)(q:(i:I)→Choice R k i)
    (y:I → Cover)(J:Finset I):
    fixed R k κ pt N b j cells q y J=logO R.family.path.levels R.metals.O j N
      (fixed R k κ pt N b (j+1) cells q (chartIn (loose R.family.path.levels j) y (cells j))) k J:=by
  unfold fixed
  rw [show b-j=(b-(j+1))+1 by omega]
  rfl

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠj:ℕ in atTop,∀b,j<b → ∀(J:Finset I)(a r:ℕ),a≤e → ∃C σ:ℝ,0≤C ∧ 0<σ ∧
    ∀N,b≤N → ∀(q:(i:I)→Choice R k i)(n:Side)(y:I → Cover)(cells:Digits R.family.path.levels I),
    let old:=fixed R k κ pt N b (j+1) cells q
    let predicted:=fixed R k κ pt N b j cells q y J
    MarkU y J (WilsonNeutralTwoPrintPathCalendar.spent R k N j e n old y (cells j) J a r)
      (predicted.2 a r) σ C:=by
  obtain ⟨_,Q,draws,coins,_⟩:=(FundedMarkedCoverRows.realm R simple price funded 0
    (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) e 0 0).exists
  obtain ⟨A₀,_,birth⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e zero_lt_one
  obtain ⟨j₀,buy⟩:=eventually_atTop.1 (WilsonReceivedFixedDigitCanonical.original R k κ pt simple quiet price funded e)
  filter_upwards [eventually_ge_atTop (max j₀ Q.anchor)] with j birthday
  intro b before J a r grade
  obtain ⟨s,A,hs,one,hear⟩:=buy (j+1) (by omega) b before
  obtain ⟨C,σ,nn,hσ,paid⟩:=WilsonNeutralTwoPrintPathTariff.submitted (D:=h) (k:=k) Q j (by omega) J a r grade hs
  rw [draws,coins] at paid
  refine ⟨C*A^J.card,σ,mul_nonneg nn (pow_nonneg (zero_le_one.trans one) _),hσ,?_⟩
  intro N top q n y cells old predicted
  have well:Wellness k old:=WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N
    cells simple R.alloy.B.ratio _ (birth q).1 _ _ (by omega)
  have wallet:CoverBill old e s A:=fun p S u hu l=>((hear N top 1 cells q).1 p S u hu l).access
  have enroll:=WilsonReceivedCompactVerseEntrance.original old well hs one wallet
  have current:=paid N (before.trans_le top) n old A one well wallet y (cells j)
  have shared:∀S,Same e
      ((submit old k e) (chartIn (loose R.family.path.levels j) y (cells j)) S)
      (old (chartIn (loose R.family.path.levels j) y (cells j)) S):=
    fun S u hu=>(enroll.2.2.1 _ S u hu).1
  have head:=congrFun (step k R.family.path.levels R.metals.O N j shared J a grade) r
  change MarkU y J _ ((logO _ _ j N _ k J).2 a r) _ _ at current
  rw [head] at current
  dsimp only [predicted]
  rw [unroll R k κ pt N b j before cells q y J]
  exact current

end YM.Integration.WilsonNeutralTwoPrintPathItinerary
end
