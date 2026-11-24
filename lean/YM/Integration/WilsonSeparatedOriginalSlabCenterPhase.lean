import YM.Integration.WilsonSeparatedOriginalReplicaRegularity

/-! The common centre character on the original Wilson subcell census. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabCenterPhase
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native
open RG05Readout.Flatten
open private location from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped BigOperators Classical Topology
variable {I:Type}[Fintype I]

def mode (v:Axis→ℝ)(z:E4):ℂ:=Complex.exp ((∑ d,v d*z d:ℝ)*Complex.I)

theorem unit (v:Axis→ℝ)(z:E4):‖mode v z‖=1:=by
  simp [mode,Complex.norm_exp]

theorem regular (v:Axis→ℝ):Continuous (mode v):=by
  unfold mode
  fun_prop

private theorem right (v:Axis→ℝ)(x y:E4):mode v (x+y)=mode v x*mode v y:=by
  unfold mode
  simp only [PiLp.add_apply,mul_add,Finset.sum_add_distrib,Complex.ofReal_add,add_mul,Complex.exp_add]

private theorem left (v w:Axis→ℝ)(z:E4):mode (v+w) z=mode v z*mode w z:=by
  unfold mode
  simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib,Complex.ofReal_add,Complex.exp_add]

private theorem turn (v:Axis→ℝ)(z:E4):mode v (-z)=mode (-v) z:=by
  simp [mode,PiLp.neg_apply]

omit [Fintype I] in
private theorem folded (v:I→Axis→ℝ)(z:E4)(S:Finset I):
    (∏i∈S,mode (v i) (-z))=mode (-(∑i∈S,v i)) z:=by
  induction S using Finset.induction_on with
  | empty=>simp [mode]
  | @insert i S hi ih=>rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,neg_add,left,turn]

def center (v:I→Axis→ℝ)(z:E4):ℂ:=mode (-(∑i,v i)) z

theorem chart (z:E4)(hz:z∈Native.box):
    (fun i:Axis=>z i)∈Metric.closedBall (0:Axis→ℝ) (1/2):=by
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num: 0≤(1/2:ℝ))).mpr fun i=>by
    simpa only [Real.norm_eq_abs] using hz i

variable {G:Gauge}{C:Family G}{b N per:ℕ}(o:I→Site (C.side b per))(h:b≤N)
local notation "A"=>C.S.toDepth h per

omit [Fintype I] in
theorem positions (r:ℝ)(hr:0<r)(t:I→Site (A).count)(z:E4)(i:I):
    (r/C.S.a b) • location o h r t z i=
      ((C.S.a b)⁻¹ • C.S.place (o i)+placeR A (t i))+(-z):=by
  ext d
  simp only [location,Pi.add_apply,Pi.smul_apply,PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,
    PiLp.neg_apply,smul_eq_mul]
  field_simp [hr.ne', (C.S.a_pos b).ne']; ring

theorem original (v:I→Axis→ℝ)(r:ℝ)(hr:0<r)(t:I→Site (A).count)(z:E4):
    (∏i,mode (v i) ((r/C.S.a b) • location o h r t z i))=
      (∏i,mode (v i) ((C.S.a b)⁻¹ • C.S.place (o i))) *
        (∏i,mode (v i) (placeR A (t i))) * center v z:=by
  simp_rw [positions o h r hr t z,right]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,folded]
  rfl

end YM.Integration.WilsonSeparatedOriginalSlabCenterPhase
