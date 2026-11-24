import YM.Integration.WilsonNeutralTwoPrintPathTariff
import YM.Integration.WilsonNeutralTwoPrintPeriod

/-! The inherited fixed-date compact pays for its complete original Gaussian
angular deposit before the remaining ultraviolet cutoff and period. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathCalendar
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


def spent (N m e:ℕ)(n:Side)(Y:Outerm G h)(y:I → Cover)
    (d:I→Site (loose R.family.path.levels m).L)(J:Finset I) :=
  let L:=R.family.path.levels
  let P:=loose L m
  let E:=submit Y k e (chartIn P y d)
  mist (stepAt P L.clock.kernel n) (xree P L.clock.kernel n)
    (freeForms L N (m+1)) (roam L N m n) R.metals.O
    (emera (actionW L R.metals.O N (m+1)) (n*P.L)) E (ratioHigh L R.metals.O N m) k J

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m<b → ∀(J:Finset I)(a r:ℕ),a≤e → ∃C σ:ℝ,0≤C ∧ 0<σ ∧
    ∀N,b≤N → ∀(q:(j:I)→Choice R k j)(n:Side)(y:I → Cover)(d:I→Site (loose R.family.path.levels m).L),
    let Y:=result R k K κ pt e N b (m+1) q
    let E:=submit Y k e (chartIn (loose R.family.path.levels m) y d)
    MarkU y J (spent R k N m e n Y y d J a r) ((logO R.family.path.levels R.metals.O m N E k J).2 a r) σ C:=by
  obtain ⟨_,Q,draws,coins,_⟩:=(FundedMarkedCoverRows.realm R simple price funded 0
    (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) e 0 0).exists
  obtain ⟨m₀,h₀⟩:=eventually_atTop.1 (WilsonReceivedCanonicalVerseTrial.original R k K κ pt simple quiet tags price funded e)
  filter_upwards [eventually_ge_atTop (max m₀ Q.anchor)] with m beyond
  intro b live J a r grade
  obtain ⟨s,A,hs,hA,sources,_⟩:=h₀ (m+1) (by omega) b live
  obtain ⟨C,σ,hC,hσ,paid⟩:=WilsonNeutralTwoPrintPathTariff.submitted (D:=h) (k:=k) Q m (by omega) J a r grade hs
  refine ⟨C*A^J.card,σ,mul_nonneg hC (pow_nonneg (zero_le_one.trans hA) _),hσ,?_⟩
  rw [draws,coins] at paid
  intro N cutoff q n y d Y E
  have already:=sources N cutoff q
  exact paid N (live.trans_le cutoff) n Y A hA already.1 already.2.1 y d

end YM.Integration.WilsonNeutralTwoPrintPathCalendar
end
