import YM.Integration.WilsonReceivedCompactVerseEntrance
import YM.Integration.WilsonReceivedBlockedVerseDocket

/-! Fixed-date numerical re-entry of the complete independently prescribed connected table.
The marked rows may depend on the higher cutoff. Their enrolled cover income is at the actual birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedReplantedVerseCourse
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
def lower (K k:I → ℕ)(e N b m:ℕ)(Y:Outerm G h):Outerm G h:=
  Gears R.family.path.levels R.metals.O K k N b m (submit Y k e)

def Calibrated (K k:I→ℕ)(e b m:ℕ)(s σ C:ℝ):Prop:=
  ∀N,b ≤ N → ∀p:ℕ,∀(Y:Outerm G h),Wellness k Y → ∀A:ℝ,1 ≤ A → CoverBill Y e s A →
    PairedAt e (lower R K k e N b m Y) (R.family.side m p) σ (C*A)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(K k:I → ℕ)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∀s:ℝ,0<s → ∃σ C:ℝ,0<σ ∧ 1 ≤ C ∧
      Calibrated (h:=h) R K k e b m s σ C ∧
      ∀J:Finset I,∃t M:ℝ,0<t ∧ t ≤ σ ∧ 0 ≤ M ∧ ∀c:I,c∈J → ∀N,b ≤ N → ∀(Y:Outerm G h),
        Wellness k Y → ∀A:ℝ,1 ≤ A → CoverBill Y e s A → ∀y,
          Issued (lower R K k e N b m Y) k e J c y t σ M ((C*A)^J.card):=by
  classical
  obtain ⟨floor,unmarked⟩:=eventually_atTop.mp (quiet e)
  filter_upwards [eventually_ge_atTop floor,FundedMarkedCoverRows.realm R simple price funded
    0 (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) e 0 0] with m quietDate realm
  obtain ⟨Q,draws,coins,_,anchor,_⟩:=realm
  intro b live s hs
  obtain ⟨s₀,V,spos,hV,raw⟩:=unmarked b (quietDate.trans live)
  let w:=min s₀ (s/32)
  have hw:0<w:=lt_min spos (div_pos hs (by norm_num))
  obtain ⟨d,B,σ,hB,hσ,bought⟩:=WilsonMarkedIndependentOnePeriod.original (D:=h) (k:=k) Q K m b anchor.le live hw
  rw [draws,coins] at bought
  let C:=B*V^d*gross G (mass k univ+e) s 1
  have hC:1 ≤ C:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hV))
    (WilsonReceivedMicroscopicVerseWallet.one ..)
  have paid:Calibrated (h:=h) R K k e b m s σ C:=by
    intro N cut p Y well A hA source
    obtain ⟨atLeast,law,_,paired⟩:=WilsonReceivedCompactVerseEntrance.original Y well hs hA source
    have next:=bought N cut (registered R p) _ law V _ hV atLeast
      (fun a ha he r hr=>((raw N p cut).2 a ha he r hr).mono (min_le_left ..))
      (fun y J a ha r=>(paired (R.family.side b p) y J a ha r).mono (min_le_right ..))
    simpa only [C,lower,WilsonMarkedIndependentEnrolledPeriod.registered,mul_assoc] using next.2
  refine ⟨σ,C,hσ,hC,paid,?_⟩
  intro J
  obtain ⟨t,M,hT,small,hM,ready⟩:=planet G J.card (mass k J) (e+1) σ hσ
  refine ⟨t,M,hT,small,hM,?_⟩
  intro c root N cut Y well A hA source y
  have accepted:=(WilsonReceivedCompactVerseEntrance.original Y well hs hA source).2.1
  let L:=lower R K k e N b m Y
  have law:Wellness k L:=Cog R.family.path.levels R.metals.O cut _ accepted simple R.alloy.B.ratio live
  have pos:0 ≤ (C*A)^J.card:=pow_nonneg (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hA)) _
  obtain ⟨rain,rent,jet⟩:=ready _ (L y J) I J y c _ (law.level' y J) root le_rfl pos
    (fun a ha r=>(paid N cut 0 Y well A hA source y J a (Nat.le_of_lt_succ ha) r).access) (e+1) le_rfl
  exact ⟨rain,rent,fun a ha=>shineZ (L y J) y rain hT jet a (Nat.lt_succ_of_le ha)⟩

theorem ordinary (simple:G.Simple)(price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)
    (u:G.ColorIndex)(tags:∀j n,(Flat.primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (K:I → ℕ)(N b m:ℕ)(entered:b ≤ N)(atDate:m ≤ b)(Y:Outerm G h)(well:Wellness k Y)
    {s A:ℝ}(hs:0<s)(hA:1 ≤ A)(source:CoverBill Y e s A)(x:I → Cover)(S:Finset I)(f:Pen h S →L[ℝ] ℝ)(n:Side):
    (tuftV f (levelsO (lower R K k e N b m Y x) S)).1 n=
      WilsonMarkedFiniteIndependentHistory.moments R u tags N K (submit Y k e) (b-m) m x S f n:=
  WilsonMarkedFiniteIndependentHistory.original R u tags simple price funded atDate entered K k _
    (WilsonReceivedCompactVerseEntrance.original Y well hs hA source).2.1 x S f n

end YM.Integration.WilsonReceivedReplantedVerseCourse
