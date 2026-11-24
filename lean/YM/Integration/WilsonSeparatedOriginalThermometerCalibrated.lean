import YM.Integration.WilsonPositionThermometerReading
import YM.Integration.WilsonSeparatedOriginalSlabTaylorCubic
import YM.XSpace.Carnation

/-! The independent linear coefficient with the true three physical Rose
inputs and original signed profile. Every proper Maxwell zeroth vanishes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalThermometerCalibrated
open Function Filter Finset Set MeasureTheory Lattice Wilson RG OPE RG17 PhysMS
open FVA2 XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Graph3 XSpace.Structure1 XSpace.Photo
open WilsonSeparatedOriginalSlabTaylorCubic (one)
open WilsonPositionThermometerReading (leg)
open scoped Classical BigOperators Topology
variable {G:Gauge}(C:Family G)(hG:G.Simple)(W:XSpace.Initialize G)(V:Normalize.Store G)(Y:Rose.Pick V)

def leader (x:Points 3)(M:Rose.Badge):ℂ:=PhysMS.WickGoal (C:=C) (d:=fun _:Fin 3=>6) (leg C M) x
def first (x:Points 3)(M:Rose.Badge):ℂ:=checked1 W V 6 x (Rose.missing (Rose.tag G) M)

include hG
theorem occupied {x:Points 3}(hx:x∈conf 3)(row:Rose.Badge→ℂ):one (leader C x) row=row univ:=by
  simp [one,leader,WilsonPositionThermometerReading.free C hG hx _ (by decide:( {0,1}:Rose.Badge).Nonempty),
    WilsonPositionThermometerReading.free C hG hx _ (by decide:({0,2}:Rose.Badge).Nonempty),
    WilsonPositionThermometerReading.free C hG hx _ (by decide:({1,2}:Rose.Badge).Nonempty),
    WilsonPositionThermometerReading.free C hG hx _ (by decide:({0}:Rose.Badge).Nonempty),
    WilsonPositionThermometerReading.free C hG hx _ (by decide:({1}:Rose.Badge).Nonempty),
    WilsonPositionThermometerReading.free C hG hx _ (by decide:({2}:Rose.Badge).Nonempty)]

theorem calibrated:(Rose.test Y).applyTo (fun x=>one (leader C x) (first W V x))=((Rose.c_T Y:ℝ):ℂ):=by
  unfold Test.applyTo c_T cT
  rw [←integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun x=>?_)
  simp only [Rose.tests]
  by_cases hx:x∈tsupport Y.image
  · rw [occupied C hG (beyond_conf _ (Y.segment hx).1)]
    unfold first
    rw [Rose.full,Rose.on_stage W hG V Y.grants Y.manages (Y.segment hx).1]
    exact (Complex.ofReal_mul ..).symm
  · simp only [image_eq_zero_of_notMem_tsupport hx,Complex.ofReal_zero,zero_mul]

theorem nonzero:(Rose.test Y).applyTo (fun x=>one (leader C x) (first W V x))≠0:=by
  rw [calibrated C hG W V Y]
  exact Complex.ofReal_ne_zero.mpr Y.fresh.ne

end YM.Integration.WilsonSeparatedOriginalThermometerCalibrated
end
