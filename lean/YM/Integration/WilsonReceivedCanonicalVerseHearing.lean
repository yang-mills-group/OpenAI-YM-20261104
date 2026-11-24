import YM.Integration.WilsonReceivedOrdinaryReplant
import YM.Integration.WilsonReceivedCanonicalVerseTrial
/-! A whole finite socket selection is entered on the original K-blocked trial with
its full N-quiet history. Each later replant includes its scalar and all mixed
ordinary faces. Its retained widths and incomes precede the regulator limits. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVerseHearing
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

open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedMicroscopicVerseWallet (gross)

open WilsonReceivedReplantedVerseTrail (Paid)

open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (start)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h:I→ℕ}
variable (R:Run G)(k K:I→ℕ)(κ:(j:I) → Knob (h j))(pt:I → Chamber)

open WilsonReceivedCanonicalVerseTrial (result)
open WilsonMarkedOrdinaryCaptureGap (tariff)
def fee (e r:ℕ)(S:Finset I)(n:Side)(s t A B:ℝ):ℝ:=
  (tariff h e r S*A^S.card)*catchW s n.val+(tariff h e r S*B^S.card)*catchW t n.val

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∃σ t A B:ℝ,0<σ ∧ 0<t ∧ 1 ≤ A ∧ 1 ≤ B ∧
    ∀N,b ≤ N → ∀p (q:(j:I)→Choice R k j)(u:G.ColorIndex)(y:I → Cover)(S:Finset I)(f:Pen h S→L[ℝ]ℝ)
      (a:ℕ),a ≤ e → ∀(r:ℕ)(x:Fin r→YForest G)(c:Cover)(D:ℕ),
    (∀j∈S,terrain.gap c (y j) ≤ D) → (∀i,terrain.gap c (x i).1 ≤ D) → 8*D < (R.family.side m p).val →
    let n:=R.family.side m p
    let Y:=start R k κ pt q
    let Z:=result R k K κ pt e N b m q
    ‖WilsonMarkedFiniteIndependentHistory.moments R u tags N K Y (b-m) m y S f n a r (slideC n x)-
      f ((levelsO (submit Z k e y) S).1 n a r (slideC n x))‖ ≤ ‖f‖*fee (h:=h) e r S n σ t A B:=by
  obtain ⟨V,hV,source⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e (s:=1) zero_lt_one
  filter_upwards [WilsonReceivedOrdinaryReplant.original (h:=h) R simple quiet price funded K k e] with m bought
  intro b geo
  obtain ⟨σ,t,A,B,hσ,ht,hA,hB,ready⟩:=bought b geo 1 zero_lt_one
  refine ⟨σ,t,A*V,B*V,hσ,ht,one_le_mul_of_one_le_of_one_le hA hV,one_le_mul_of_one_le_of_one_le hB hV,?_⟩
  intro N high p q u y S f a ha r x c D positions hull fits n Y Z
  have signed:=ready N high p Y (source q).1 V hV ((source q).2.2 (R.family.side b p))
  rw [←WilsonMarkedFiniteIndependentHistory.original R u tags simple price funded geo high K k Y (source q).1 y S f n]
  let U:=Gears R.family.path.levels R.metals.O K k N b m Y
  change ‖f ((levelsO (U y) S).1 n a r (slideC n x))-f ((levelsO (submit Z k e y) S).1 n a r (slideC n x))‖ ≤ _
  rw [←f.map_sub]
  exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (signed y S a ha r x c D positions hull fits) (norm_nonneg _))

end YM.Integration.WilsonReceivedCanonicalVerseHearing
