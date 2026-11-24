import YM.QuadraticLocal.Fk.Window
import YM.Comparison.RG02.Cumulants.Parents
import YM.Progress.CLASSICAL_KIN_RECURSION.Plume

/-! Leading inherited marker vertices at the true finite Wilson Gaussian.
The linearized fine gauge chart is forced by the declared engineering grade. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision Marker Multi
open Comparison.RG02 Comparison.RG02.Assembly Progress.ClassicalKin
open scoped Topology Classical ContDiff BigOperators

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)
    {I : Type} [DecidableEq I] {R : Census I}
local notation "E" => Bulk.Joint S F (G:=G)
local notation "X" => ℝ × fieldDir G f 1

def fineLogChart (y : E) : X := (y.1, Work.F03.axisLog F y.2)
def fineVelocity : E →L[ℝ] X := fderiv ℝ (fineLogChart (G:=G) F) 0

theorem fineVelocity_time (y : E) : (fineVelocity F (G:=G) y).1=y.1 := by
  let h := fun z:E=>Work.F03.axisLog F z.2
  have sh : ContDiffAt ℝ ω h 0 := (Work.F03.inclusion_smooth F).snd.comp (f:=Prod.snd) (0:E) contDiffAt_snd
  have hf := (hasFDerivAt_fst (𝕜:=ℝ) (p:=(0:E))).prodMk (sh.differentiableAt (by simp)).hasFDerivAt
  rw [fineVelocity, show fderiv ℝ (fineLogChart F (G:=G)) 0 = _ from hf.fderiv]
  rfl

private theorem engineering_jet (V : ℝ → Config G f → ℂ) {k : ℕ}
    (h : GradeAt k (Bulk.projected V)) (y : E) :
    jet (Bulk.posed S F V) k y = jet (Bulk.projected V) k (fineVelocity F y) := by
  let T:= fineLogChart F (G:=G)
  have zero : T 0=0 := by
    exact congrArg (fun a:Work.F03.Logs G c f=>((0:ℝ),a.2)) (Work.F03.inclusion_zero F)
  have smooth : ContDiffAt ℝ ω T 0 := contDiffAt_fst.prodMk
    ((Work.F03.inclusion_smooth F).snd.comp (f:=Prod.snd) (0:E) contDiffAt_snd)
  have equal : Bulk.posed S F V =ᶠ[𝓝 0] Bulk.projected V ∘ T := by
    filter_upwards [(continuous_snd.tendsto (0:E)).eventually (Work.F03.inclusion_works F)] with u hu
    exact congrArg (V u.1) hu.symm
  unfold Assembly.jet
  rw [(equal.iteratedFDeriv ℝ k).eq_of_nhds,wakes (Bulk.projected V) T (h.smooth.of_le le_top)
    (smooth.of_le le_top) zero h.vanish]
  rfl

theorem leading_painter (W : Bulk.Colors R G f) (hw : Bulk.Well W) (i : Hot R)
    (y : E) (clock : y.1=1) :
    markLetter W.power (Bulk.markFn S F W) i y 0 =
      (QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F y).2).part i.val := by
  rw [QuadraticLocal.Earn.Air.discharge,part_lit _ i,markLetter,Nat.add_zero,Bulk.markFn,engineering_jet F _ (hw.suppose_mark i)]
  congr 1
  exact Prod.ext ((fineVelocity_time F y).trans clock) rfl

end YM.Integration.FVA1Physical.Wilson
