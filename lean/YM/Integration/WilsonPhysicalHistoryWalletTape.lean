import YM.Integration.WilsonPhysicalHistoryWalletExperiment
import YM.Integration.FVA1Physical.Wilson.ActualSeed

/-! The original orbit of the measured signed wallet, evaluated on the actual
microscopic field, coincides with the full physical Wilson posterior on every
interior stage of that same cutoff. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletTape
open Function Filter MeasureTheory Lattice RG Wilson OPE OPE.Therm
open WilsonCoeffUV PhysicalNext.Repeat.Legato WilsonReportForwardTransfer
open FVA1Physical.Wilson FVA1Physical.Marked
open scoped Classical
variable {G : Gauge}

/-- Every entry in the original source wallet uses the very same positive
disintegration as the independently tested physical coefficient. -/
theorem carried (R : Run G) {N per j u : ℕ} (ju : j ≤ u) (top : u ≤ N)
    (φ : Config G (R.family.side u per) → ℝ) :
    (fun W=>(↑(haarTape R N per u φ j ju W):ℂ)) =
      exterior (C:=R.family) (N:=N) ju (fun U=>(φ U:ℂ)) := by
  induction ju using Nat.decreasingInduction with
  | self =>
      rw [haarTape_top]
      funext V
      unfold exterior
      rw [Push.GridApprox.pushTo_self]
      unfold weighted
      have pos := dose_positive R.makes.wilson top V
      have den : (↑(dose (H:=R.family.path) (p:=per) u V N):ℂ) ≠ 0 := by exact_mod_cast pos.ne'
      field_simp
  | of_succ j hj ih =>
      funext V
      calc
        _ = (↑(MSbar.Bulk.expect (R.family.path.levels.clock.op j per) (R.family.path.rep N per (j+1)) V
          (haarTape R N per u φ (j+1) hj)):ℂ) := by rw [haarTape_step R φ hj]
        _ = exterior (C:=R.family) (N:=N) j.le_succ (fun W=>(↑(haarTape R N per u φ (j+1) hj W):ℂ)) V :=
          (congrFun (WilsonPhysicalHistoryWalletReceiver.step R (hj.trans_le top) _) V).symm
        _ = exterior (C:=R.family) (N:=N) j.le_succ (exterior (C:=R.family) (N:=N) hj (fun U=>(φ U:ℂ))) V :=
          congrArg (fun f=>exterior (C:=R.family) (N:=N) j.le_succ f V) ih
        _ = _ := congrFun (WilsonPhysicalHistoryPositiveTower.cascade R j.le_succ hj top _) V

theorem born (R : Run G) {N per j u : ℕ} (ju : j ≤ u) (live : u<N)
    (φ : Config G (R.family.side (u+1) per) → ℝ) :
    (fun W=>(↑(haarTape R N per u (fun V=>MSbar.Bulk.expect (R.family.path.levels.clock.op u per)
      (R.family.path.rep N per (u+1)) V φ) j ju W):ℂ)) =
    exterior (C:=R.family) (N:=N) (ju.trans u.le_succ) (fun U=>(φ U:ℂ)) := by
  apply (carried R ju live.le _).trans
  rw [← WilsonPhysicalHistoryWalletReceiver.step R live φ]
  exact WilsonPhysicalHistoryPositiveTower.cascade R ju u.le_succ live _

end YM.Integration.WilsonPhysicalHistoryWalletTape

