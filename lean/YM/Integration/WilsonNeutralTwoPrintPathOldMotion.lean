import YM.Integration.WilsonNeutralTwoPrintPathInheritedMotion
import YM.Integration.WilsonNeutralTwoPrintPathInheritedCalendar

/-! Translation covariance of the original fixed-digit source at every issued
age, and invariance of the independently recentered previous connected print. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonNeutralTwoPrintPathOldMotion
open Function Finset Filter Lattice RG Laurent Wilson
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonNeutralTwoPrintPathInherited (atom)
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open private translated from YM.Integration.WilsonPointChildCenteredSeat
open private center from YM.Integration.WilsonNeutralTwoPrintPathInherited
open scoped Classical BigOperators

open Precision Tree Exterior Bloch Work.F08
open WilsonCoeffUV.Wheel.Motion (steppedC raised0 ramble alongShift)
open WilsonNeutralTwoPrintPathRebadge (table)
open WilsonReceivedFixedDigitIntake (next)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}


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
open WilsonCoeffUV.Wheel.Motion (shiftedSum)
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Mosaic.Near
open WilsonReceivedCanonicalVerseRegister (start offer)
open WilsonReceivedFixedDigitHistory (itinerary Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds IndependentSourcePathFamily
open private dark from YM.Integration.IndependentSourcePathFamily
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonReceivedDatedVerseReprint (printed)
open WilsonNeutralTwoPrintPathInherited (atom)
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered)

theorem birth (R:Run G)(k:I→ℕ)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:(i:I)→Choice R k i)(w:Cover):
    ramble w (start R k κ pt q):=by
  intro y
  funext S
  change independent (offer R k κ pt q) (steppedC w y) S=shifted (independent (offer R k κ pt q) y S) w
  by_cases active:∃i,S={i}
  · obtain ⟨i,rfl⟩:=active
    rw [IndependentSourcePathFamily.singleton,IndependentSourcePathFamily.singleton]
    unfold single
    rw [shiftedSum]
    apply Finset.sum_congr rfl
    intro b _
    exact shifted_add _ w (y i)
  · have away:∀i,S≠{i}:=fun i h=>active ⟨i,h⟩
    rw [dark _ _ _ away,dark _ _ _ away]
    rfl

omit [Fintype I] in
theorem step (L:Levels G)(O:ChartRatio G)(j N:ℕ)(live:j<N)(simple:G.Simple)(rat:LocalRatio O)
    (M:Outerm G D)(well:Wellness k M)(covariant:∀v,ramble v M)(digit:I→Site (loose L j).L)
    (w:Cover):ramble w (next L O j N k M digit):=by
  intro y
  change logO L O j N (M (chartIn (loose L j) (steppedC w y) digit)) k=
    raised0 w (logO L O j N (M (chartIn (loose L j) y digit)) k)
  have moved:chartIn (loose L j) (steppedC w y) digit=
      steppedC ((L.S.block j).val • w) (chartIn (loose L j) y digit):=by
    funext i
    change (L.S.block j).val • (w+y i)+_=(L.S.block j).val • w+((L.S.block j).val • y i+_)
    rw [nsmul_add,add_assoc]
  rw [moved]
  exact alongShift (A:=L) (Ñ:=O) well live simple rat (covariant _) _

omit [Fintype I] in
theorem history (L:Levels G)(O:ChartRatio G)(N:ℕ)(cells:Digits L I)(simple:G.Simple)(rat:LocalRatio O)
    (M:Outerm G D)(well:Wellness k M)(covariant:∀v,ramble v M)(days j:ℕ)(cut:j+days≤N):
    ∀w,ramble w (itinerary L O k N cells days j M):=by
  induction days generalizing j with
  | zero=>exact covariant
  | succ d ih=>
    exact step L O j N (by omega) simple rat _
      (WilsonReceivedFixedDigitHistory.sound L O k N cells simple rat M well d (j+1) (by omega))
      (ih (j+1) (by omega)) (cells j)

theorem original (R:Run G)(k:I→ℕ)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(simple:G.Simple)
    (N b j:ℕ)(before:j≤b)(dep:b≤N)(cells:Digits R.family.path.levels I)(q:(i:I)→Choice R k i):
    ∀w,ramble w (fixed R k κ pt N b j cells q):=by
  obtain ⟨_,_,enrolled⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt 0 zero_lt_one
  exact history R.family.path.levels R.metals.O N cells simple R.alloy.B.ratio _ (enrolled q).1
    (birth R k κ pt q) _ _ (by omega)

omit [Fintype I] [DecidableEq I] in
theorem printed_at (M:Outerm G D)(covariant:∀v,ramble v M)(e:ℕ)(y:I → Cover)(w:Cover)(S:Finset I):
    (submit M k e) (steppedC w y) S=shifted ((submit M k e) y S) w:=by
  by_cases active:S.Nonempty
  · simp only [submit,dif_pos active,printed,sphere]
    rw [show M (steppedC w y) S=shifted (M y S) w from congrFun (covariant w y) S,←shifted_add]
    have anchor:-(steppedC w y active.choose)+w=-(y active.choose):=by change -(w+_)+w=_;abel
    rw [anchor]
    exact shifted_add _ w _
  · simp only [submit,dif_neg active]
    rfl

omit [Fintype I] [DecidableEq I] in
theorem atom_at (M:Outerm G D)(covariant:∀v,ramble v M)(e:ℕ)(y:I → Cover)(w:Cover)(S:Finset I)
    (c:I){h:ℕ}(read:Pen D S →L[ℝ] Vote h):
    atom M k e (steppedC w y) S c read=atom M k e y S c read:=by
  unfold atom
  rw [printed_at M covariant,←shifted_add]
  have early:-(steppedC w y c)+w=-(y c):=by change -(w+_)+w=_;abel
  rw [early]

end YM.Integration.WilsonNeutralTwoPrintPathOldMotion
end
