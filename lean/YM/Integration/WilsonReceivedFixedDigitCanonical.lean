import YM.Integration.WilsonReceivedFixedDigitProgram
import YM.Integration.WilsonReceivedCanonicalVerseHearing

/-! All finite winding charges for the individually positioned canonical K-born trials. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedFixedDigitCanonical
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

open WilsonReceivedFixedDigitHistory (Digits itinerary)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open WilsonMarkedOrdinaryCaptureGap (Within tariff)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h:I→ℕ}(R:Run G)(k:I→ℕ)
  (κ:(j:I)→Knob (h j))(pt:I→Chamber)

def fixed (N b m:ℕ)(cells:Digits R.family.path.levels I)(q:(j:I)→Choice R k j):Outerm G h:=
  itinerary R.family.path.levels R.metals.O k N cells (b-m) m (start R k κ pt q)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∃σ A:ℝ,0<σ ∧ 1≤A ∧
      ∀N,b≤N → ∀per (cells:Digits R.family.path.levels I) (q:(j:I)→Choice R k j),
        let Y:=fixed R k κ pt N b m cells q
        let n:=R.family.side m per
        PairedAt e Y n σ A ∧
        ∀(S:Finset I)(r:ℕ)(y:I → Cover)(c:Cover)(D:ℕ),(∀a∈S,terrain.gap c (y a)≤D) → 8*D<n.val →
          Within n (fun X=>terrain.gap c X.1≤D) e r (catchW σ n.val) (tariff h e r S*A^S.card)
            (levelsO (Y y) S):=by
  obtain ⟨B,hB,source⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e (s:=1) zero_lt_one
  filter_upwards [WilsonReceivedFixedDigitProgram.original (h:=h) R simple quiet price funded k e] with m calendar
  intro b later
  obtain ⟨σ,C,positive,hC,loan⟩:=calendar b later 1 zero_lt_one
  refine ⟨σ,C*B,positive,one_le_mul_of_one_le_of_one_le hC hB,?_⟩
  intro N live per cells q Y n
  have paid:PairedAt e Y n σ (C*B):=loan N live per cells _ (source q).1 B hB
    ((source q).2.2 (R.family.side b per))
  refine ⟨paid,?_⟩
  intro S r y c D origins small
  exact WilsonReceivedOrdinaryReplant.compact S e r positive.le (by positivity) paid y c D origins small

end YM.Integration.WilsonReceivedFixedDigitCanonical
