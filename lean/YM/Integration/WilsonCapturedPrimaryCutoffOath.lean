import YM.Integration.WilsonReceivedCloseHistory
import YM.Integration.WilsonThermometerCourseHearing
import YM.Integration.WilsonSeparatedOriginalSlabHeldProxy

/-! Each fired face of the single-cutoff thermometer has the literal
canonical Wilson credit at every earlier reception. The engineering power is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCutoffOath
open Filter Function Finset MeasureTheory Lattice Wilson Labels RG RG16.Literal
open Source Marker LocalComparison FVA1 Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress
open MergeProof MergeProof.East MergeProof.Accent QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseIntake WilsonThermometerCourseHearing WilsonPositionThermometerGradedReading
open WilsonReceivedCloseHistory
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
  {N per b i : ℕ} (top : b<N) (o : Positions (Fin 3) (R.family.side N per))
local notation "J" => Stock.census (Fin 3)
local notation "head" => offered R A simple top o
local notation "read" i:max ib:max => history (N:=N) R disks head i ib
local notation "upper" => R.family.path.rep N per N

def word (s : (J).Mode) (U : Config G (R.family.side N per)) : ℂ :=
  ∏ v ∈s.val,R.family.O N per
    (A.station.wheel.atCut (N,per) (index A (grade v)) (vector A (Finset.univ : Finset (Fin 3)) v)) (o.origin v) U

include simple in
theorem inlet (ib : i ≤ b) :
    (read i ib) fired = incoming R A simple (by omega) o := by
  induction ib using Nat.decreasingInduction with
  | self => rw [WilsonReceivedCloseHistory.head];exact fired_input R A simple top o
  | of_succ j jb ih =>
    rw [← congrFun (WilsonReceivedCloseHistory.adjacent (N:=N) R disks head jb) fired,ih]
    exact WilsonThermometerCourseIntake.step R A simple ((Nat.succ_le_of_lt jb).trans_lt top) o

theorem credit_at (ib : i ≤ b) (ref : ∀v,R.family.ref (grade v) ≤ N) (d : ℕ) (s : (J).Mode)
    (U : Config G (R.family.side i per)) :
    credit R.family N per d (word R A o s) i (by omega) U =
      ((R.family.S.a i:ℂ)^d)*(actualPush R.family N per i ((read i ib) fired) U).part s := by
  rw [inlet,WilsonThermometerCourseIntake.step]
  have raw := WilsonPositionThermometerDepositedFaces.deposited R simple N per A.station
    (fun v : Fin 3=>index A (grade v)) (vector A (Finset.univ : Finset (Fin 3))) o ref (by omega : i ≤ N) s U
  change (incoming R A simple (by omega) o U).part s =
    (R.family.path.rep N per i).eval U • actualTransport R.family (N:=N) (word R A o s) (by omega) U at raw
  rw [raw,← WilsonSeparatedOriginalSlabHeldProxy.normalized R (by omega : i ≤ N) (word R A o s) U,
    Complex.real_smul]
  have positive := Multi.AxisShift.chosen_positive R.makes.wilson (show i ≤ N by omega) U
  have nonzero : (((R.family.path.rep N per i).eval U:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have cancel : (((R.family.path.rep N per i).eval U:ℝ):ℂ) *
      (credit R.family N per 0 (word R A o s) i (by omega) U/((R.family.path.rep N per i).eval U:ℂ)) =
      credit R.family N per 0 (word R A o s) i (by omega) U := by field_simp
  rw [cancel]
  simp [credit]

end YM.Integration.WilsonCapturedPrimaryCutoffOath
