import YM.Integration.WilsonPositionScaleLawGuardWindow
import YM.Integration.WilsonPositionScaleLawGuardLift

/-! A uniform numerical price for undoing the original engineering dilation on
the retained Maxwell space, in its actual transported field norm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardTurning
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawNative (positive)
open WilsonPositionScaleLawGrade (grade)
open scoped Topology Classical BigOperators
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus MS MS.Book.Program
open FVA2 FVA2.Scale FVA2.Register FVA2.Arrival PowerSeries
open WilsonPositionScaleLawDressedGear (engine cap capPositive)
open WilsonPositionScaleLawGuardLift (act)
open WilsonPositionScaleLawGuardStock (Stock)
variable {G:Gauge}(C:Family G){d:ℕ}
set_option quotPrecheck false
local notation "E"=>(Bel C.book).Field

theorem piece (t:Ratio)(i:Fin (d+1))(v:E d):‖grade C i (engine C d t v)‖≤(2:ℝ)^i.val*‖grade C i‖*‖v‖:=by
  change ‖grade C i (Pert.Scale.gear C.labels d t.val v)‖≤_
  rw [WilsonPositionScaleLawFixed.engineering,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive t),mul_assoc]
  exact mul_le_mul (pow_le_pow_left₀ (positive t).le (t.property.2.trans (by norm_num)) i.val)
    ((grade C i).le_opNorm _) (norm_nonneg _) (by positivity)

theorem forward (t:Ratio):‖engine C d t‖≤cap C d:=by
  apply ContinuousLinearMap.opNorm_le_bound _ (capPositive C)
  intro v
  calc
    _=‖∑i:Fin (d+1),grade C i (engine C d t v)‖:=by rw [WilsonPositionScaleLawWhole.sumAll]
    _≤∑i:Fin (d+1),‖grade C i (engine C d t v)‖:=norm_sum_le ..
    _≤∑i:Fin (d+1),(2:ℝ)^i.val*‖grade C i‖*‖v‖:=Finset.sum_le_sum fun i _=>piece C t i v
    _=_:=by rw [cap,Finset.sum_mul]

theorem original (t:Ratio)(a:FieldEnd G d):
    ‖act C d (Level.turner (WilsonPositionScaleLawIndependent.time t) a)‖≤cap C d*‖act C d a‖*cap C d:=by
  letI :NormedAddCommGroup (E d→L[ℂ]E d):=ContinuousLinearMap.toNormedAddCommGroup
  have h:=capPositive (d:=d) C
  apply ContinuousLinearMap.opNorm_le_bound (act C d (Level.turner (WilsonPositionScaleLawIndependent.time t) a))
    (mul_nonneg (mul_nonneg h (norm_nonneg (act C d a))) h)
  intro v
  have e:engine C d t (act C d (Level.turner (WilsonPositionScaleLawIndependent.time t) a) v)=act C d a (engine C d t v):=
    DFunLike.congr_fun (WilsonPositionScaleLawGuardLift.transfer C t a).symm v
  have g:‖engine C d t v‖≤cap C d*‖v‖:=((engine C d t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (forward C t) (norm_nonneg _))
  calc
    _≤cap C d*‖engine C d t (act C d (Level.turner (WilsonPositionScaleLawIndependent.time t) a) v)‖:=WilsonPositionScaleLawDressedGear.inverse C t _
    _≤cap C d*(‖act C d a‖*(cap C d*‖v‖)):=by
      rw [e];exact mul_le_mul_of_nonneg_left (((act C d a).le_opNorm _).trans (mul_le_mul_of_nonneg_left g (norm_nonneg _))) h
    _=_:=by ring

theorem printed (q:ℕ)(a:Guard G d):Stock (fun t:Ratio=>trunc (q+1) (WilsonPositionScaleLawGuardLift.pack C (convertT (WilsonPositionScaleLawIndependent.time t) a))):=by
  letI :NormedAddCommGroup (E d→L[ℂ]E d):=ContinuousLinearMap.toNormedAddCommGroup
  let K:=∑k∈Finset.Iic q,‖act C d (coeff k a)‖
  have pos:0≤K:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have h:=capPositive (d:=d) C
  apply WilsonPositionScaleLawGuardStock.printed q _ (C:=cap C d*K*cap C d) (mul_nonneg (mul_nonneg h pos) h)
  intro t k hk
  rw [WilsonPositionScaleLawGuardLift.coefficient,convertT,coeff_mk]
  exact (original C t (coeff k a)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _=>norm_nonneg (act C d (coeff j a))) (Finset.mem_Iic.mpr hk)) h) h)

end YM.Integration.WilsonPositionScaleLawGuardTurning
