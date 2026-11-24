import YangMills.WilsonProof.NativeSupport.IssuedRuns.FinalWilsonData
import YangMills.WilsonProof.NativeSupport.WilsonTrajectory

set_option autoImplicit false

namespace IssuedRuns.OriginalTrajectory

open Filter YangMills YangMills.Wilson
open scoped Topology
noncomputable section

variable {g : GaugeGroup}

private theorem block (C : YM.Family g.core) (m : ℕ) :
    wilsonBlock (wilsonFamily C) m = (C.S.block m).val := by
  change (C.S.denominator m * C.S.block m).val / (C.S.denominator m).val = _
  rw [PNat.mul_coe]
  exact Nat.mul_div_cancel_left (C.S.block m).val (C.S.denominator m).property

theorem original (C : YM.Family g.core) (h : C.Makes) (hg : g.IsSimple)
    (B : Maxwell.Reference g) : WilsonTrajectory B (wilsonFamily C) where
  denominatorZero := rfl
  divides m := ⟨(C.S.block m).val, rfl⟩
  blockOdd m := by rw [block]; exact C.S.block_odd m
  blockLarge m := by rw [block]; exact C.S.block_large m
  periodFour p := C.S.period_four p
  gentle := by
    have signal : wilsonLogStep (wilsonFamily C) =
        fun m => Real.log ((C.S.block m).val : ℝ) / C.S.scale m := by
      funext m
      rw [wilsonLogStep, block]
      simp only [YM.Schedule.scale, YM.Schedule.a, inv_inv]
      rfl
    rw [signal]
    exact C.path.levels.fits.mesh
  bare := by
    refine ⟨C.path.levels.clock.bar, C.path.levels.clock.bar_pos, fun p => h.wilson.reaches 0 p, ?_⟩
    intro N p
    have center : wilsonBareCenter B (wilsonFamily C) C.path.levels.clock.bar N =
        C.path.levels.clock.hatBeta N := by
      unfold wilsonBareCenter YM.RG.Calendar.hatBeta
      rw [IssuedBank.WilsonSlope.original B hg]
      simp only [YM.Schedule.scale, YM.Schedule.a, inv_inv]
      rfl
    rw [center]
    exact (h.wilson.represents N p N le_rfl).band

theorem funded (C : YM.Family g.core) (h : C.Makes) (hg : g.IsSimple) (B : Maxwell.Reference g) :
    WilsonTrajectory B (wilsonFamily C) ∧ Nonempty (WilsonData B (wilsonFamily C)) :=
  ⟨original C h hg B, ⟨IssuedRuns.FinalWilsonData.original C h hg B⟩⟩


end
end IssuedRuns.OriginalTrajectory
