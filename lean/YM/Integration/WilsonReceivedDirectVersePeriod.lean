import YM.Integration.WilsonReceivedCoverTrail
import YM.Integration.WilsonReceivedBlockedVerseDocket

/-! Fixed-date numerical re-entry of the complete independently prescribed connected table.
The marked rows may depend on the higher cutoff. Their enrolled cover income is at the actual birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDirectVersePeriod
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
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h k:I → ℕ}{e:ℕ}
variable (R:Run G)
def IssuedAt (K k:I → ℕ)(e m b:ℕ)(s σ C:ℝ):Prop:=
  ∀N,b ≤ N → ∀p (Y:Outerm G h),Wellness k Y → ∀A:ℝ,1 ≤ A →
    PairedAt e Y (R.family.side b p) s A →
    PairedAt e (Gears R.family.path.levels R.metals.O K k N b m Y) (R.family.side m p) σ (C*A)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(K k:I → ℕ)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∀s:ℝ,0<s → ∃σ C:ℝ,0<σ ∧ 1 ≤ C ∧
      IssuedAt (h:=h) R K k e m b s σ C:=by
  obtain ⟨floor,bank⟩:=eventually_atTop.mp (quiet e)
  filter_upwards [eventually_ge_atTop floor,FundedMarkedCoverRows.realm R simple price funded 0
    (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) e 0 0] with m eligible signed
  obtain ⟨Q,draws,coins,_,anchor,_⟩:=signed
  intro b later s hs
  obtain ⟨t,V,ht,hV,quietFee⟩:=bank b (eligible.trans later)
  have hw:=lt_min ht hs
  obtain ⟨d,B,σ,hB,hσ,bought⟩:=WilsonMarkedIndependentOnePeriod.original (D:=h) (k:=k) Q K m b anchor.le later hw
  rw [draws,coins] at bought
  refine ⟨σ,B*V^d,hσ,one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hV),?_⟩
  intro N high p Y lawful A hA input
  have paid:=bought N high (registered R p) Y lawful V A hV hA
    (fun a ha he r hr=>((quietFee N p high).2 a ha he r hr).mono (min_le_left ..))
    (fun y J a ha r=>(input y J a ha r).mono (min_le_right ..))
  exact paid.2

end YM.Integration.WilsonReceivedDirectVersePeriod
