import YM.Integration.WilsonReceivedReplantedVersePeriod

/-! On each genuine receiving date print the entire previously issued independent table.
Every intermediate scalar and connected proper subword enters the next ordinary Wick program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedReplantedVerseTrail
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

def path (K k:I → ℕ)(e N:ℕ):ℕ → ℕ → Outerm G h → Outerm G h
  | 0,_,Y=>Y
  | l+1,m,Y=>lower R K k e N (m+1) m (path K k e N l (m+1) Y)

def Paid (k:I → ℕ)(e l m:ℕ)(Y:Outerm G h)(σ A:ℝ):Prop:=
  Wellness k Y ∧ CoverBill Y e σ A ∧ (0<l → ∀p:ℕ,PairedAt e Y (R.family.side m p) σ A ∧
    Charge Y k e (R.family.side m p) σ A)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(K k:I→ℕ)(e:ℕ):
    ∀ᶠf:ℕ in atTop,∀ l m,f ≤ m → ∀s:ℝ,0<s → ∃σ C:ℝ,0<σ ∧ 1 ≤ C ∧
      ∀N,m+l ≤ N → ∀Y:Outerm G h,Wellness k Y → ∀A:ℝ,1 ≤ A → CoverBill Y e s A →
        Paid R k e l m (path R K k e N l m Y) σ (C*A):=by
  obtain ⟨lo,allDates⟩:=eventually_atTop.mp (WilsonReceivedReplantedVerseCourse.original (h:=h) R simple quiet price funded K k e)
  refine eventually_atTop.mpr ⟨lo,?_⟩
  intro f hf l
  induction l with
  | zero =>
    intro m _ s hs
    refine ⟨s,1,hs,le_rfl,?_⟩
    intro N _ Y well A _ bill
    simpa only [Paid,path,one_mul] using And.intro well (And.intro bill (by intro impossible; omega :
      0<0 → ∀p:ℕ,PairedAt e Y (R.family.side m p) s A ∧ Charge Y k e (R.family.side m p) s A))
  | succ l ih =>
    intro m hm s hs
    obtain ⟨t,B,ht,hB,first⟩:=ih (m+1) (hm.trans (Nat.le_succ _)) s hs
    obtain ⟨σ,C,hσ,hC,next,_⟩:=allDates m (hf.trans hm) (m+1) (Nat.le_succ _) t ht
    refine ⟨σ,C*B,hσ,one_le_mul_of_one_le_of_one_le hC hB,?_⟩
    intro N cut Y well A hA bill
    let P:=path R K k e N l (m+1) Y
    have old:Paid R k e l (m+1) P t (B*A):=first N (by omega) Y well A hA bill
    have valid:1 ≤ B*A:=one_le_mul_of_one_le_of_one_le hB hA
    have signed:Wellness k (submit P k e):=(WilsonReceivedCompactVerseEntrance.original P old.1 ht valid old.2.1).2.1
    let U:=path R K k e N (l+1) m Y
    have lawful:Wellness k U:=Cog R.family.path.levels R.metals.O (by omega : m+1 ≤ N) _
      signed simple R.alloy.B.ratio (Nat.le_succ m)
    have budget:1 ≤ C*B*A:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hB) hA
    have fees (p:ℕ):PairedAt e U (R.family.side m p) σ (C*B*A):=by
      rw [mul_assoc]
      exact next N (by omega) p P old.1 (B*A) valid old.2.1
    exact ⟨lawful,fun y J a ha r=>(fees 0 y J a ha r).access, fun _ p=>
      ⟨fees p,WilsonReceivedReplantedVersePeriod.original lawful hσ budget (fees p)⟩⟩

theorem ordinary (simple:G.Simple)(price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)
    (u:G.ColorIndex)(tags:∀j n,(Flat.primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (K:I → ℕ)(N l m:ℕ)(live:m+1 ≤ N)(Y:Outerm G h){s A:ℝ}(hs:0<s)(hA:1 ≤ A)
    (previous:Paid R k e l (m+1) (path R K k e N l (m+1) Y) s A)
    (x:I → Cover)(S:Finset I)(f:Pen h S →L[ℝ] ℝ)(n:Side):
    let P:=path R K k e N l (m+1) Y
    (tuftV f (levelsO (path R K k e N (l+1) m Y x) S)).1 n=
      WilsonMarkedFiniteIndependentHistory.moments R u tags N K (submit P k e) 1 m x S f n:=by
  intro P
  simpa only [path,P,Nat.add_sub_cancel_left] using WilsonReceivedReplantedVerseCourse.ordinary R simple price funded u tags K N
    (m+1) m live (Nat.le_succ _) P previous.1 hs hA previous.2.1 x S f n

end YM.Integration.WilsonReceivedReplantedVerseTrail
