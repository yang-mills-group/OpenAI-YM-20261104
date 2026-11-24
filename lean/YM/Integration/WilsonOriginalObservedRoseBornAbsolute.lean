import YM.Integration.WilsonOriginalObservedRoseBornMeter
import YM.Integration.WilsonOriginalObservedRoseJoint
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
import YM.Integration.WilsonMeasuredPublicEntranceCellWords

/-! The original Wilson expectation and the independent stopped ordinary rows on the actual signed position cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornAbsolute
open Finset RG Lattice Wilson Source Labels Extra.Histories
open PhysicalNext PhysicalNext.Repeat.Legato Maxwell XSpace FVA2 FVA2.Register
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open WilsonOriginalObservedRoseBornPosition (Balance)
open WilsonOlderFreshSoftSocketStationPortfolio (reading)
open WilsonPositionThermometerConnected (value)
open WilsonAddressedPhysicalCells WilsonThermometerReflectedTrajectory
open XSpace.Rose XSpace.Structure1 XSpace.Cirrus XSpace.Normalize FVA2.Scale MS MS.WilsonBridge.Coupling
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(Z:WilsonPrescription G)(Φ:Test 3)(r:ℝ)(d:Fin 3→ℕ)(b N per:ℕ)
local notation "Y" => cells R Φ r (b,per)
local notation "μ" => WilsonCenteredCompactBooking.mass R Φ r (b,per)
local notation "g" => Pert.Asymptotics.regulatorRun R.family
local notation "J" => Stock.census (Fin 3)
variable (names:∀_:Y,∀i,(R.family).label (d i))(turn:Y→Fin 3→Motion)
def face (d:Fin 3→ℕ)(N:ℕ)(names:Y→∀i,(R.family).label (d i))(turn:Y→Fin 3→Motion)
    (y:Y)(s:Finset (Fin 3)):ℂ:=by
  exact (R.family).omega N per (WilsonMeasuredPublicEntranceCellWords.physical R d
    (names y) (turn y) y.val (⟨s,Finset.mem_univ _⟩:(J).Mode))
def cell (y:Y):Sample 3:= WilsonOriginalObservedRoseJoint.lowerSite R b r (b,per) (le_refl b) y.val

theorem original (upper:Y→Finset (Fin 3)→ℂ) (α:ℝ)(positive:0≤α)(stopped:Y→Finset (Fin 3)→ℂ)(earned:ℝ)
    (sold:α^14*‖signed R Φ r (b,per) (fun y=>value (upper y)-value (stopped y))‖≤earned):
    Balance Z (fun y:Y=>μ y.val) α (cell R Φ r b per) (g N per) N stopped
      ((α:ℂ)^14*signed R Φ r (b,per) (fun y=>value (upper y))) earned:=by
  apply WilsonOriginalObservedRoseBornPosition.original
  let z:ℂ:=(α:ℂ)^14
  let read:=fun y:Y=>value (upper y)
  have eq:z*signed R Φ r (b,per) read-reading (fun y:Y=>μ y.val) z stopped=
      z*signed R Φ r (b,per) (fun y=>read y-value (stopped y)):=by
    unfold signed reading
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _=>by ring)
  change ‖z*signed R Φ r (b,per) read-reading (fun y:Y=>μ y.val) z stopped‖≤earned
  rw [eq,norm_mul]
  have unit:‖z‖=α^14:=by simp only [z,norm_pow,Complex.norm_real,Real.norm_of_nonneg positive]
  rwa [unit]

end YM.Integration.WilsonOriginalObservedRoseBornAbsolute
