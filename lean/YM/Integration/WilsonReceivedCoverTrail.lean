import YM.Integration.WilsonReceivedCoverFaces

/-! On each genuine receiving date print the entire previously issued independent table.
Every intermediate scalar and connected proper subword enters the next ordinary Wick program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCoverTrail
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

def declared (K k:I → ℕ)(N l m:ℕ)(Y:Outerm G h):Outerm G h:=
  Gears R.family.path.levels R.metals.O K k N (m+l) m Y

omit [Fintype I] in
theorem entry (K k:I → ℕ)(N m:ℕ)(Y:Outerm G h):declared R K k N 0 m Y=Y:=by
  unfold declared
  rw [Nat.add_zero,gearTop]

omit [Fintype I] in
theorem later (K k:I → ℕ)(N l m:ℕ)(Y:Outerm G h):
    declared R K k N (l+1) m Y = stout R.family.path.levels R.metals.O m N K k (declared R K k N l (m+1) Y):=by
  unfold declared
  rw [gearUp _ _ _ (by omega : m < m+(l+1))]
  rw [show m+(l+1)=m+1+l by omega]

omit [Fintype I] in
theorem stamped (K k:I → ℕ)(e N m:ℕ)(P:Outerm G h):
    WilsonReceivedReplantedVerseCourse.lower R K k e N (m+1) m P=stout R.family.path.levels R.metals.O m N K k (submit P k e):=by
  unfold WilsonReceivedReplantedVerseCourse.lower
  rw [gearUp _ _ _ (Nat.lt_succ_self m),gearTop]

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(K k:I → ℕ)(e:ℕ):
    ∀ᶠf:ℕ in atTop,∀l m,f ≤ m → ∀N,m+l ≤ N → ∀(Y:Outerm G h),Wellness k Y →
    ∀s A:ℝ,0 < s → 1 ≤ A → CoverBill Y e s A → ∀y J,
    Same e (path R K k e N l m Y y J) (declared R K k N l m Y y J):=by
  filter_upwards [WilsonReceivedReplantedVerseTrail.original (h:=h) R simple quiet price funded K k e] with f grants
  intro l
  induction l with
  | zero =>
    intro m _ N _ Y _ s A _ _ _ y J
    rw [WilsonReceivedReplantedVerseTrail.path,entry]
    exact self _
  | succ l ih =>
    intro m eligible N high Y well s A hs hA bill y J
    have upper:f ≤ m+1:=by omega
    have cut:m+1+l ≤ N:=by omega
    let P:=WilsonReceivedReplantedVerseTrail.path R K k e N l (m+1) Y
    let Q:=declared R K k N l (m+1) Y
    obtain ⟨t,C,ht,hC,spent⟩:=grants l (m+1) upper s hs
    have old:Paid R k e l (m+1) P t (C*A):=spent N cut Y well A hA bill
    have prints:=(WilsonReceivedCompactVerseEntrance.original P old.1 ht
      (one_le_mul_of_one_le_of_one_le hC hA) old.2.1).2.2.1
    have common (x:I → Cover)(S:Finset I):Same e (submit P k e x S) (Q x S):=
      fun a ha=>(prints x S a ha).1.trans (ih (m+1) upper N cut Y well s A hs hA bill x S a ha)
    rw [WilsonReceivedReplantedVerseTrail.path,stamped,later]
    exact step R.family.path.levels R.metals.O m N K k common y J

end YM.Integration.WilsonReceivedCoverTrail
