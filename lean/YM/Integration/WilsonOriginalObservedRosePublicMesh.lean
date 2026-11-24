import YM.Integration.WilsonOriginalObservedRosePublicCurrency
import YM.Integration.WilsonAddressedCollarWindow
import YM.Integration.WilsonOlderFreshSoftSocketStationScale
import YM.Integration.WilsonSeparatedPrefixKineticGeometry

/-! The actual first planting cell of a physical station covers the public radius with a fixed exponent chosen before the optical stop and the Taylor order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePublicMesh
open Function Filter Lattice Wilson RG Real Next.Rank PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonInvariantActionPosition (berth arrival)
open scoped Topology Classical

variable {G:Gauge}(R:Run G)
local notation "P" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale

def aperture (width:ℕ):ℕ:=2*(width+2)+1

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(width L:ℕ):
    ∀ᶠv:ℕ in atTop,∀j:ℕ,v≤j → ∀b:ℝ,b≤Perch.y (H j) → ∀N per:ℕ,
      let K:=berth R width j
      K≤N → σ K-σ v≤L*Real.log (H v) →
      Station.gap (P) b j/(a K)≤((regulatorRun R.family N per v)⁻¹)^(aperture width):=by
  have geometry:=(WilsonAddressedCollarWindow.original R simple slow width (η:=1) (by norm_num)).and
    (WilsonOlderFreshSoftSocketStationScale.extent R simple (η:=1) (by norm_num))
  obtain ⟨start,bought⟩:=eventually_atTop.mp geometry
  filter_upwards [eventually_ge_atTop start,WilsonOriginalObservedRosePublicCurrency.clock R simple L (width+2),
    WilsonSeparatedPrefixKineticGeometry.spend R simple ((4:ℝ)^(width+2)) 0] with v late clock wallet
  intro j vj b paid N per K kn span
  let z:=(regulatorRun R.family N per v)⁻¹
  have jk:j≤K:=(arrival R width j).1.le
  have vn: v≤N:=(vj.trans jk).trans kn
  have zp:0≤z:=(inv_pos.mpr (ActualRunKernelPackets.regulator_pos R N per v vn)).le
  obtain ⟨fine,mag⟩:=bought j (late.trans vj)
  have first:(a j)/(a K)≤(H j)^(width+1):=by simpa only [Real.rpow_one,pow_succ] using fine.2.2
  have shape:Station.mag (P) b j≤H j:=by simpa only [Real.rpow_one] using mag b paid
  have hj:0≤H j:=zero_le_one.trans ((P).fits.delayed j).le
  have reserve:(4:ℝ)^(width+2)≤z:=by simpa only [pow_zero,mul_one] using wallet N per vn
  calc
    Station.gap (P) b j/(a K)=(a j)/(a K)*Station.mag (P) b j:=by unfold Station.gap;ring
    _≤(H j)^(width+1)*(H j):=mul_le_mul first shape (Station.mag_pos ..).le (pow_nonneg hj _)
    _=(H j)^(width+2):=(pow_succ ..).symm
    _≤(H K)^(width+2):=pow_le_pow_left₀ hj (WilsonReflectedOpticalStock.monotone R simple jk) _
    _≤(4:ℝ)^(width+2)*z^(2*(width+2)):=clock N per K (vj.trans jk) kn span
    _≤z*z^(2*(width+2)):=mul_le_mul_of_nonneg_right reserve (pow_nonneg zp _)
    _=z^(aperture width):=by rw [aperture,pow_succ,mul_comm]

end YM.Integration.WilsonOriginalObservedRosePublicMesh
end
