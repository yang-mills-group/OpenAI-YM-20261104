import YM.Integration.WilsonAddressedWeakFixedRank
import YM.Integration.WilsonThermometerWeakDisplacedCross

/-! The cover lifts used by the actual fixed-residue Gram meet the physical
two-cell reporter's coordinate budget before all regulator limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakRankCovers
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Next.Rank Edition Baler Value Glyph Thirst Alarm
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonAddressedWeakPointCells
open scoped Classical BigOperators Topology

open WilsonAddressedWeakCalibration WilsonThermometerWeakMovedCovers
variable {G:Gauge} (R:Run G) {k N p:ℕ}
local notation "S" => R.family.S

theorem coordinates (hk:k≤N) (ρ:ℝ) (hr:0<ρ) (x:Points 2):
    ∀i j, |(S).gridPoint k ((lifts R (p:=p) hk ρ hr x) i) j-ρ*x i j| ≤ 16*(S).a k:=by
  intro i j
  let b:=lifts R (p:=p) hk ρ hr x
  let y:=projected R (p:=p) hk ρ hr x
  have close:dist y x≤16*((S).a k/ρ):=(actual R (p:=p) hk ρ hr x).2
  have fixed:|(y i j)-(x i j)|≤dist y x:=
    (show |y i j-x i j|≤dist (y i) (x i) by exact (PiLp.dist_apply_le (y i) (x i) j)).trans (PiLp.dist_apply_le y x i)
  have pos:=hr.le
  have coord : y i j=ρ⁻¹*((S).gridPoint k (b i) j):=rfl
  rw [coord] at fixed
  change |(S).gridPoint k (b i) j-ρ*x i j|≤_
  calc
    _ = ρ*|(ρ⁻¹*((S).gridPoint k (b i) j))-x i j|:=by rw [←abs_of_nonneg pos,←abs_mul,abs_of_nonneg pos,mul_sub,←mul_assoc,mul_inv_cancel₀ hr.ne',one_mul]
    _ ≤ ρ*(16*((S).a k/ρ)):=mul_le_mul_of_nonneg_left (fixed.trans close) pos
    _ = _:=by field_simp

theorem sites (hk:k≤N) (ρ:ℝ) (hr:0<ρ) (x:Points 2) (z:Fin 2→Site (R.family.side N p)):
    ∀i, move (S) p hk (z i) (wrap _ (lifts R (p:=p) hk ρ hr x i))=
      WilsonAddressedWeakFixedChild.slide R hk (z i)
        (((S).toDepth hk p).parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i)):=by
  intro i
  rw [←(actual R (p:=p) hk ρ hr x).1 i]
  rfl

end YM.Integration.WilsonThermometerWeakRankCovers
end
