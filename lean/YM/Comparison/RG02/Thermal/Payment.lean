import YM.Comparison.RG02.Thermal.Fix
import YM.Comparison.RG02.Assembly.Bi
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
namespace Payment
variable (K : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (W : Colors R G f)
local notation "I'"=> Precision.Key F G
local notation "X"=> fieldDir G c 1
local notation "Λ'"=> Precision.Key F G→ℝ
local notation "Z"=> House X (Precision.Key F G)
local notation "Y"=> AxisChart G F
local notation "E"=> X × (Precision.Key F G →ℝ)
local notation "b"=> K.b F
local notation "T"=> Fix.vibe K F t
local notation "q"=> Fix.sway K F t
local notation "dα"=> fderiv ℝ (K.b F) 0

private def swing (x : X) : (Λ') →L[ℝ] AxisChart G F := ContinuousLinearMap.comp gaugeCount.toContinuousLinearMap (q x).mulVecLin.toContinuousLinearMap
-- beware notation Λ'→L expansion (`I→ℝ→L`), parentheses

def cutter (v : E): Bulk.Joint S F (G:=G) := Pull.stands K F ((T).effect (0,v))
private lemma clean (x:E): cutter K F t x=(0,x.1,b x.1+swing K F t x.1 x.2):= Fix.plot ..

def cover (v:E) := stone F t K (cutter K F t v)
def heat (v:E) := officer F K (cutter K F t v) - Real.log ((q v.1).det)
def supplement (v:Z) := Bulk.supplement S F W (Pull.stands K F ((T).effect v))
lemma summarizes (x:Z) : Pull.blown K F t T W x= cover K F t x.2 + x.1^2 * heat K F t x.2 + Payment.supplement K F t W x := by
   let y := x.2
   have he : (Pull.stands K F ((Fix.vibe K F t).effect x)).2=(cutter K F t y).2:= by rw [Fix.plot,clean]; rfl
   have ht := Fix.plot K F t x
   unfold Pull.blown Vibe.price; rw [Pi.sub_apply]; dsimp only [Function.comp_apply]; unfold geometric fee pillar stone Payment.supplement Vibe.logDet cover heat officer
   unfold stone
   simp_rw [he,ht]; unfold y; rw [show (T).B (x.1,x.2.1)=q x.2.1 from rfl]; ring
private lemma smooth : ContDiffAt ℝ ω (cutter K F t) 0 := (Pull.stands K F).contDiff.contDiffAt.comp (f:=fun u:E=> (T).effect (0,u)) 0 ((T).no_jets.2.comp 0 (f:=fun u:E=> ((0:ℝ),u)) (contDiffAt_const.prodMk contDiffAt_id))
private lemma hcut : cutter K F t 0=0 := by unfold cutter; erw [Vibe.base]; exact _root_.map_zero _
lemma cover_service : ContDiffAt ℝ ω (cover K F t) 0 := ((hcut ..).symm ▸ stone_smooth K F t : ContDiffAt ℝ ω _ (cutter K F t 0)).comp _ (smooth K F t)
lemma heat_service : ContDiffAt ℝ ω (heat K F t) 0 := by
   have ht : ContDiffAt ℝ ω (fun x : X => Real.log (q x).det) 0 := YM.Push.Loops.logdet_contDiff (Fix.sway_budget ..) (by rw [Fix.sway_zero,Matrix.det_one]; exact isUnit_one)
   exact (((hcut ..).symm ▸ (officer_known K F).smooth : ContDiffAt ℝ ω _ (cutter K F t 0)).comp _ (smooth K F t)).sub (ht.comp (f:=Prod.fst) _ contDiffAt_fst)

variable (hW : W.Standard)
include hW in
lemma remains : GradeAt 5 (supplement K F t W) := by
   let A := Pull.stands K F
   have hp : Assembly.GradeAt 5 (Bulk.supplement S F W) := joint_receipt S F hW.2
   exact hp.coarse (A.contDiff.contDiffAt.comp (f:=(T).effect) _ (Vibe.no_jets ..).2) (show (A ∘ (T).effect) 0=0 by rw [Function.comp_apply, Vibe.base]; exact A.map_zero)

-- true conditional x in no-hole body. Derivatives along ALL tangent. Use α conventions.
lemma formula (x:E) : cover K F t x=tested F t p P x.1 (b x.1+ swing K F t x.1 x.2):= by rw [cover,clean]; rfl
lemma center (x:X) : cover K F t (x,0)=tested F t p P x (b x) := by rw [formula]; dsimp only; rw [_root_.map_zero, add_zero]
lemma thermal_amount : (fun x:X=> heat K F t (x,0)) =ᶠ[𝓝 0] (fun x=> thermal F t p P b O x - (1 / 2:ℝ) * Real.log (Fix.stiffness K F t 0).det):= by
   filter_upwards [Fix.paired_log K F t] with x hx
   unfold heat; rw [clean]; change Precision.loop P _ - Real.log _ - _= _
   unfold Precision.thermal
   dsimp only; simp_rw [_root_.map_zero,add_zero,hx]; rw [show Work.F03.live F (x,b x)=lifting F (represent x) (b x) from rfl]; unfold Fix.stiffness; ring

private def centerLine (x:X) := fun v : Λ'=> b x + swing K F t x v
private lemma along (x:X) (v : Λ') : fderiv ℝ (centerLine K F t x) 0 v=swing K F t x v := by
   unfold centerLine; rw [fderiv_const_add _, ContinuousLinearMap.fderiv]
lemma plumb (v : Λ') : Clipper.cylinder (cover K F t) v 1 0 := by
  filter_upwards [Clipper.vertical_one (cover K F t) v (cover_service ..),(K.critical F).2.2 t|>.2] with x hx hp
  let g:= centerLine K F t x
  have hg : g 0=b x:= by unfold g centerLine; rw [map_zero,add_zero]
  have hh : HasFDerivAt g (swing K F t x) 0 := (swing K F t x).hasFDerivAt.const_add (b x)
  have ha := (hg.symm ▸ hp : HasFDerivAt (tested F t p P x) 0 (g 0)).comp 0 hh
  rw [hx,show (fun y:Λ'=> cover K F t (x,y))= tested F t p P x ∘ g from funext fun y=> formula .., ha.fderiv]; simp
set_option maxHeartbeats 500000 in
lemma shifted (v:Λ') : Clipper.cylinder (cover K F t) v 2 (Gaussian.force (K.covariance F t) v) := by
  have hu:= (crit_home (K.critical F)).eventually (((K.critical F).2.2 t).1.eventually (by simp))
  filter_upwards [Clipper.vertical_two (cover K F t) v (cover_service ..), (K.critical F).2.2 t|>.2, hu, Fix.sway_home K F t] with x hv hp hc hj
  let g:= centerLine K F t x
  let L:= swing K F t x
  have hl:g 0=b x := by unfold g centerLine; rw [_root_.map_zero,add_zero]
  have hz:= hl.symm ▸ hold_jet hc
  let C:= Fix.stiffness K F t
  rw [hv, show (fun y:Λ' => cover K F t (x,y))=tested F t p P x ∘ g from funext fun y=> formula ..,bend_comp_stationary (show ContDiffAt ℝ ω (tested F t p P x) (g 0) from hz) (contDiffAt_const.add L.contDiff.contDiffAt) (hl.symm ▸ hp.fderiv),LinearMap.compl₁₂_apply]; dsimp only [ContinuousLinearMap.coe_coe];
  rw [hl]; unfold g; rw [along]
  change bend (tested F t p P x) (b x) (tape ((q x) *ᵥ v)) (tape (q x *ᵥ v)) =Gaussian.force _ _
  rw [tape_price S F]; calc
    _ = (q x*ᵥ v) ⬝ᵥ (C x *ᵥ (q x *ᵥ v)) := by unfold C Fix.stiffness; rw [hessian_eq]; exact (dotProduct_toMatrix₂_mulVec _ _ _ (q x *ᵥ v) (q x *ᵥ v)).symm
    _ = v ⬝ᵥ (C 0 *ᵥ v) := by rw [show C 0 = (q x).transpose*C x*q x from hj.symm,←mulVec_mulVec,←mulVec_mulVec,dotProduct_comm (q x *ᵥ v)]; exact (Matrix.dotProduct_transpose_mulVec (q x) v (C x *ᵥ (q x *ᵥ v))).symm
    _ = _ := by unfold C Fix.stiffness Gaussian.force Kernel.covariance; rw [(K.critical F).1,Matrix.nonsing_inv_nonsing_inv _ (IsUnit.mk0 _ (K.hessian_pos F t).det_pos.ne')]
end Payment
end YM.Comparison.RG02.Thermal
