import YM.Integration.WilsonPositionScaleLawGuardLittle
import YM.Integration.WilsonPositionScaleLawWholeHome

/-! Exact engineering at the actual homogeneous homes and the summed grade norm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardOrbit
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawGrade (grade)
open scoped Topology Classical BigOperators
variable {G:Gauge}{d:ℕ}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

theorem step (r:ℝ)(t:Ratio)(i:Fin (d+1))(O:S.Field d):
    grade R.family i (dressed Z F J d r t (physical F J Z d (t.val*r) O))=
      (t.val:ℂ)^(d-i.val) • grade R.family i (physical F J Z d r O):=by
  let T:=WilsonPositionHomogeneousFrame.homogeneous F J Z
  let U:=dressed Z F J d r t
  let P:=grade R.family i
  let v:=(T (t.val*r) d).symm O
  have home:(T r d).symm O=Pert.Scale.gear R.family.labels d t.val (U v):=by
    apply (T r d).injective
    change T r d ((T r d).symm O)=T r d (Pert.Scale.gear R.family.labels d t.val (Frame.cocycle d T r t.val (WilsonPositionScaleLawNative.positive t) v))
    rw [Frame.cocycle_value,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change P (U (((↑(t.val*r):ℂ)^d) • v))=(t.val:ℂ)^(d-i.val) • P (((r:ℂ)^d) • (T r d).symm O)
  rw [U.map_smul,P.map_smul,P.map_smul,home,WilsonPositionScaleLawFixed.engineering,smul_smul,smul_smul]
  congr 1
  have power:(t.val:ℂ)^(d-i.val)*(t.val:ℂ)^i.val=(t.val:ℂ)^d:=by
    rw [←pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)]
  rw [Complex.ofReal_mul,mul_pow,←power]
  ring

def size (C:Family G){d:ℕ}(x:(Bel C.book).Field d):ℝ:=∑i:Fin (d+1),‖grade C i x‖
def charge (C:Family G)(d:ℕ):ℝ:=∑i:Fin (d+1),‖grade C i‖

theorem sizePos (C:Family G)(x:(Bel C.book).Field d):0≤ size C x:=Finset.sum_nonneg fun _ _=>norm_nonneg _
theorem chargePos (C:Family G)(d:ℕ):0≤ charge C d:=by
  let X:=(Bel C.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  exact Finset.sum_nonneg fun _ _=>norm_nonneg _

theorem total (C:Family G)(x:(Bel C.book).Field d):‖x‖≤ size C x:=by
  calc _=‖∑i:Fin (d+1),grade C i x‖:=by rw [WilsonPositionScaleLawWhole.sumAll]
       _≤_:=norm_sum_le _ _

theorem original (r:ℝ)(t:Ratio)(O:S.Field d):
    let y:=physical F J Z d (t.val*r) O
    let x:=physical F J Z d r O
    let U:=dressed Z F J d r t
    size R.family y≤ size R.family x+charge R.family d*‖U-ContinuousLinearMap.id ℂ (E d)‖*size R.family y:=by
  intro y x U
  let I:=ContinuousLinearMap.id ℂ (E d)
  have ht:=WilsonPositionScaleLawNative.positive t
  have row(i:Fin (d+1)):‖grade R.family i y‖≤‖grade R.family i x‖+‖grade R.family i‖*(‖U-I‖*size R.family y):=by
    let P:=grade R.family i
    have eq:P y=P (U y)+P ((I-U) y):=by rw [_root_.sub_apply,show I y=y from rfl,P.map_sub];abel
    have actual:P (U y)=(t.val:ℂ)^(d-i.val) • P x:=step F J Z r t i O
    calc
      ‖P y‖≤‖P (U y)‖+‖P ((I-U) y)‖ :=(congrArg norm eq).trans_le (norm_add_le _ _)
      _≤‖P x‖+‖P‖*(‖U-I‖*size R.family y):=by
        rw [actual,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
        apply add_le_add (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.le t.property.2))
        have b:=((I-U).le_opNorm y).trans (mul_le_mul_of_nonneg_left (total R.family y) (norm_nonneg (I-U)))
        rw [norm_sub_rev I U] at b
        exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left b (norm_nonneg _))
  calc
    size R.family y≤∑i:Fin (d+1),(‖grade R.family i x‖+‖grade R.family i‖*(‖U-I‖*size R.family y)):=Finset.sum_le_sum fun i _=>row i
    _=_:=by rw [Finset.sum_add_distrib,←Finset.sum_mul];change size R.family x+charge R.family d*(‖U-I‖*size R.family y)=_;ring

theorem absorb {a b c:ℝ}(ha:0≤a)(hc:0≤c)(small:c≤1/2)(purchase:a≤b+c*a):a≤(1+2*c)*b:=by
  have h:=mul_le_mul_of_nonneg_right small ha
  have cap:a≤2*b:=by linarith
  calc _≤b+c*a:=purchase
       _≤b+c*(2*b):=add_le_add_right (mul_le_mul_of_nonneg_left cap hc) _
       _=_:=by ring

end YM.Integration.WilsonPositionScaleLawGuardOrbit
