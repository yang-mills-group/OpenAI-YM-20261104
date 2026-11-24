import YM.Integration.WilsonGraphCenteredPhysicalPairTriangle
import YM.Integration.WilsonGraphCenteredFarNearClockBilinear

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredPhysicalReturn

open YangMills
universe u

/-- For each appointed period and compact set of separated centered pairs, the
two original physical readings have their independently returned near-clock prices. -/
theorem pairedAtNearClock (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ)
    (strict : StrictMono periods) (h p : ℕ) (K : Set (YangMills.Points 2))
    (compact : IsCompact K) (safe : K ⊆ YM.conf 2) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    PairAtNearClock.{u} g hg periods strict h p K safe C B := by
  exact combine.{u} g hg periods strict h p K compact safe hC hB
    (AppointedNearClockBilinear.onCompact.{u} g hg periods strict h p K compact safe hC hB)

end YM.FVA2.GradedFar.AppointedCenteredPhysicalReturn

