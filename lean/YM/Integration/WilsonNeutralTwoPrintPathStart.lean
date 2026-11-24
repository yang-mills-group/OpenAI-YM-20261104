import YM.Integration.WilsonNeutralTwoPrintPathCalendar
import YM.Integration.WilsonRegisteredBareMarkedWinding

/-! The bare fixed-date source retains its literal periodization on the original Gaussian conditional before reset. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathStart
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


open WilsonReceivedCanonicalVerseRegister (start offer)
theorem frozen (q:(l:I)→Choice R k l)(y:I → Cover):
    repaint (start R k κ pt q y)=start R k κ pt q y:=by
  funext J
  apply Prod.ext
  · funext n a r
    exact (WilsonRegisteredBareMarkedWinding.original (offer R k κ pt q) y
      (fun l _=>WilsonReceivedCanonicalVerseBasis.grade R k κ pt l (q l)) J n a r).symm
  · rfl

def returned (N m:ℕ)(n:Side)(q:(l:I)→Choice R k l)(y:I → Cover)
    (d:I→Site (loose R.family.path.levels m).L)(J:Finset I) :=
  let L:=R.family.path.levels
  let P:=loose L m
  let E:=start R k κ pt q (chartIn P y d)
  mist (stepAt P L.clock.kernel n) (xree P L.clock.kernel n)
    (freeForms L N (m+1)) (roam L N m n) R.metals.O
    (emera (actionW L R.metals.O N (m+1)) (n*P.L)) E (ratioHigh L R.metals.O N m) k J

theorem original (simple:G.Simple)(price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀(J:Finset I)(a r:ℕ),a≤e → ∃C σ:ℝ,0≤C ∧ 0<σ ∧
    ∀N,m<N → ∀(q:(l:I)→Choice R k l)(n:Side)(y:I → Cover)(d:I→Site (loose R.family.path.levels m).L),
    let E:=start R k κ pt q (chartIn (loose R.family.path.levels m) y d)
    MarkU y J (returned R k κ pt N m n q y d J a r) ((logO R.family.path.levels R.metals.O m N E k J).2 a r) σ C:=by
  obtain ⟨_,Q,draws,coins,_⟩:=(FundedMarkedCoverRows.realm R simple price funded 0
    (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) e 0 0).exists
  obtain ⟨A,one,sources⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e zero_lt_one
  filter_upwards [eventually_ge_atTop Q.anchor] with m beyond
  intro J a r grade
  obtain ⟨C,σ,hC,hσ,paid⟩:=WilsonNeutralTwoPrintPathTariff.invoice (D:=h) (k:=k) Q m beyond J a r grade zero_lt_one
  rw [draws,coins] at paid
  refine ⟨C*A^J.card,σ,mul_nonneg hC (pow_nonneg (zero_le_one.trans one) _),hσ,?_⟩
  intro N live q n y d E
  have W:=sources q
  specialize paid N live n E y d A (zero_le_one.trans one) (W.1.level' _) (W.1.quiet' _)
    (fun K _ u hu v=>W.2.1 _ K u hu v)
  unfold coilH at paid
  rw [frozen R k κ pt q _] at paid
  exact paid

end YM.Integration.WilsonNeutralTwoPrintPathStart
end
