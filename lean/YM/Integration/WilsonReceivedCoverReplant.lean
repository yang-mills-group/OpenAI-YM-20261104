import YM.Integration.WilsonReceivedDirectVersePeriod

/-! On each genuine receiving date print the entire previously issued independent table.
Every intermediate scalar and connected proper subword enters the next ordinary Wick program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCoverReplant
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

open WilsonReceivedReplantedVerseCourse (lower)
open WilsonReceivedReplantedVersePeriod (Charge)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h k:I → ℕ}{e:ℕ}
variable (R:Run G)

open WilsonReceivedReplantedVerseTrail (path Paid)
open WilsonReceivedCoverGrade (Same)
open WilsonReceivedCoverFaces (step self ordinary)

open WilsonReceivedCoverTrail (declared)
def Difference (Y P:Outerm G h)(k:I → ℕ)(e:ℕ)(n:Side)(σ A:ℝ):Prop:=
  ∀(J:Finset I)(c:I),c∈J → ∀(z:I → Site n)(a:ℕ),a ≤ e → ∀(r:ℕ)(x:Fin r → Woods G n),
    let y:=PeriodicMarkedWinding.roots n z c
    ‖(Y y J).1 n a r x-((submit P k e) y J).1 n a r x‖ ≤
      (((priceM (Hooks G) r σ+tiePay (Hooks G) r (σ/4)+1)*A^J.card+A^J.card)*
        catchW (σ/32/16) n)*Real.exp (-(σ/32/2)*Syn (tor n) z J x)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(K k:I → ℕ)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∀s:ℝ,0<s → ∃σ C:ℝ,0<σ ∧ 1 ≤ C ∧
      ∀N,b ≤ N → ∀p (Y:Outerm G h),Wellness k Y → ∀A:ℝ,1 ≤ A → PairedAt e Y (R.family.side b p) s A →
      let U:=Gears R.family.path.levels R.metals.O K k N b m Y
      let Z:=WilsonReceivedReplantedVerseTrail.path R K k e N (b-m) m Y
      PairedAt e U (R.family.side m p) σ (C*A) ∧
      (∀y J a,a ≤ e → ∀(n:Side) r,((submit Z k e) y J).1 n a r=plume ((U y J).2 a r) n) ∧
      (∀y J,Same e (levelsO (Z y) J) (levelsO (U y) J)) ∧
      Difference U Z k e (R.family.side m p) σ (C*A):=by
  filter_upwards [WilsonReceivedCoverTrail.original (h:=h) R simple quiet price funded K k e,
    WilsonReceivedReplantedVerseTrail.original (h:=h) R simple quiet price funded K k e,
    WilsonReceivedDirectVersePeriod.original (h:=h) R simple quiet price funded K k e] with m labels road sheet
  intro b geo s hs
  obtain ⟨σ,C,hσ,hC,raw⟩:=sheet b geo s hs
  obtain ⟨t,V,ht,hV,previous⟩:=road (b-m) m le_rfl s hs
  refine ⟨σ,C,hσ,hC,?_⟩
  intro N high p Y lawful A hA rent U Z
  have native:PairedAt e U (R.family.side m p) σ (C*A):=raw N high p Y lawful A hA rent
  have fiscal:CoverBill Y e s A:=fun y J a ha r=>(rent y J a ha r).access
  have stamped:Paid R k e (b-m) m Z t (V*A):=previous N (by omega) Y lawful A hA fiscal
  have same (x:I → Cover)(J:Finset I):Same e (Z x J) (U x J):=by
    simpa only [Z,U,declared,show m+(b-m)=b by omega] using labels (b-m) m le_rfl N (by omega) Y lawful s A hs hA fiscal x J
  have compact:=(WilsonReceivedCompactVerseEntrance.original Z stamped.1 ht
    (one_le_mul_of_one_le_of_one_le hV hA) stamped.2.1).2.2.1
  have lift (y:I → Cover)(J:Finset I)(a:ℕ)(ha:a ≤ e)(n:Side)(r:ℕ):
      ((submit Z k e) y J).1 n a r=plume ((U y J).2 a r) n:=by
    rw [(compact y J a ha).2 n r,same y J a ha]
  refine ⟨native,lift,fun y J=>WilsonReceivedCoverFaces.ordinary (same y) J,?_⟩
  intro J c root z a ha r x y
  rw [lift y J a ha]
  exact (norm_sub_rev _ _).le.trans ((PeriodicMarkedWinding.periodized z c root hσ
    (native y J a ha r)).2 x)

end YM.Integration.WilsonReceivedCoverReplant
