import YM.Comparison.RG02.Affinity.Metric
import YM.Comparison.RG02.Affinity.Pull
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Thermal
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open Affinity Gaussian Bulk RG Wilson Exterior YM.Work.F05
variable {c f : Side} {S : StepData c f} {P : PathData G} {p : Clip} {O : ChartRatio G}

namespace Fix
variable (K : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
local notation "I'"=> Precision.Key F G
local notation "X"=> fieldDir G c 1
local notation "Y"=> AxisChart G F
local notation "M"=> Matrix I' I' ℝ
local notation "b"=> K.b F

def stiffness (v : X) : M := hessian F t p P v (b v)
private lemma Asym : ContDiffAt ℝ ω (stiffness K F t) 0 := by
   have h:= (K.critical F).2.2 t |>.1
   let A := (tested F t p P)
   have he : ContDiffAt ℝ ω (fun x : X × Y=> fderiv ℝ (fderiv ℝ (A x.1)) x.2) 0 := curve_partial (F:=fun x=>fderiv ℝ (A x)) (curve_partial h)
   have hy := (contDiffAt_id (x:=(0:X))).prodMk (K.critical F).2.1
   have hh : ContDiffAt ℝ ω (fun x : X=> fderiv ℝ (fderiv ℝ (A x)) (b x)) 0 := by
      have ht : ((0:X),b 0)=0 := Prod.ext rfl (K.critical F).1
      exact (ht.symm ▸ he : ContDiffAt ℝ ω (fun x:X×Y=> fderiv ℝ (fderiv ℝ (A x.1)) x.2) ((0:X),b 0)).comp (f:=fun x:X=> (x,b x)) 0 hy
   apply YM.Push.Loops.matrix_diff; intro i j; unfold stiffness hessian; dsimp only [Matrix.of_apply]; simp_rw [iteratedFDeriv_two_apply]; exact (hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const
private lemma Apos : (stiffness K F t 0).PosDef := (by unfold stiffness; rw [(K.critical F).1]; exact K.hessian_pos F t)
private lemma Asymm : ∀ᶠ x in 𝓝 0,(stiffness K F t x).IsSymm := by
   have he:= (crit_home (K.critical F)).eventually (((K.critical F).2.2 t).1.eventually (by simp)); filter_upwards [he] with x hx
   have ht := (hold_jet hx).isSymmSndFDerivAt_of_omega
   ext i j; simp [stiffness,hessian,Matrix.transpose_apply]; exact ht.iteratedFDeriv_cons -- implicit

-- witness lets us whiten exactly in real germ. no estimate on these variable roots.
def sway := MetricFix.blanker (Asym K F t) (Apos K F t)
lemma sway_zero : sway K F t 0=1:= MetricFix.blanked ..
lemma sway_budget : ContDiffAt ℝ ω (sway K F t) 0 := MetricFix.blank_smooth ..
lemma sway_home : ∀ᶠ x in 𝓝 0, (sway K F t x).transpose*stiffness K F t x*sway K F t x=stiffness K F t 0 := MetricFix.blank_cost _ _ (Asymm K F t)
lemma paired_log : (fun x : X=> Real.log (sway K F t x).det) =ᶠ[𝓝 0] (fun x=> (Real.log (stiffness K F t 0).det - Real.log (stiffness K F t x).det)/2):= by
    let B:= sway K F t; let A:= stiffness K F t
    have ht : 0<(B 0).det := by unfold B; rw [sway_zero,Matrix.det_one]; exact zero_lt_one
    have he : 0<(A 0).det := (Apos ..).det_pos
    filter_upwards [sway_home K F t,(YM.Push.Loops.det_contDiff.contDiffAt.comp 0 (sway_budget K F t)).continuousAt.eventually (lt_mem_nhds ht),(YM.Push.Loops.det_contDiff.contDiffAt.comp 0 (Asym K F t)).continuousAt.eventually (lt_mem_nhds he)] with v hv hu ha
    change 0<(A v).det at ha; change 0< (B v).det at hu
    change (B v).transpose*(A v)*(B v)=_ at hv; change Real.log (B v).det=(Real.log (stiffness K F t 0).det-Real.log (A v).det)/2
    rw [← hv,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Real.log_mul (mul_pos hu ha).ne' hu.ne', Real.log_mul hu.ne' ha.ne']; ring

def note (x : X) := gaugeCount.symm (b x - fderiv ℝ b 0 x)
lemma tune : GradeAt 2 (note K F) := by
   let f : X→ Y:= b - ⇑(fderiv ℝ b 0)
   have he : GradeAt 2 f := by
       have hh:=(K.critical F).2.1
       apply Buy.deuce f (hh.sub (fderiv ℝ b 0).contDiff.contDiffAt)
       · unfold f; rw [Pi.sub_apply,(K.critical F).1,map_zero,sub_zero]
       unfold f; rw [fderiv_sub (hh.differentiableAt (by simp)) (ContinuousLinearMap.differentiableAt _), ContinuousLinearMap.fderiv, sub_self]
   exact GradeAt.linear_contact (ContinuousLinearEquiv.toContinuousLinearMap gaugeCount.symm) he

def vibe : Vibe (fieldDir G c 1) (Precision.Key F G) :=
    { m:=fun x=>note K F x.2
      B:=fun x=>sway K F t x.2
      identity:= sway_zero ..
      roots := (tune K F).coarse contDiffAt_snd rfl
      smooth := ContDiffAt.comp _ (sway_budget K F t) contDiffAt_snd }
lemma plot (x:House X I') : Pull.stands K F ((vibe K F t).effect x)=
    (x.1,x.2.1,b x.2.1 + tape (sway K F t x.2.1 *ᵥ x.2.2)) := by
    change (x.1,x.2.1,fderiv ℝ b 0 x.2.1 + gaugeCount (note K F x.2.1+ sway K F t x.2.1 *ᵥ x.2.2))= _
    rw [_root_.map_add, note,gaugeCount.apply_symm_apply]; rw [← _root_.add_assoc,add_sub_cancel]; rfl
end Fix
end YM.Comparison.RG02.Thermal
