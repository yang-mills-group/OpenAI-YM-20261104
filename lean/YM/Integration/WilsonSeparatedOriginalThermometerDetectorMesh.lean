import YM.Integration.WilsonMeasuredWindow
import YM.Integration.ActualOriginalFiniteCoefficients
import YM.Integration.WilsonSeparatedOriginalThermometerCalibrated

/-! Calibrate the independent detector on the physical reporting torus, with
period and microscopic cutoff chosen after the radius. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalThermometerDetectorMesh
open Function Filter Set Lattice PhysicalNext.Repeat.Legato XSpace XSpace.Cirrus XSpace.Normalize
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)

def chart (k per:ℕ)(h:ℝ)(positive:0<h):Mesh:=
  ⟨⟨R.family.side k per,(ActualOriginalFiniteCoefficients.side_admissible R k per).2,
    (ActualOriginalFiniteCoefficients.side_admissible R k per).1⟩,h,positive⟩

theorem reporting {A:Type*}(l:Filter A)(f:Extraction.Order)(U:Filter (ℕ×ℕ))(hu:U≤f.fuse)
    (k:A→ℕ)(h:A→ℝ)(hp:∀r,0<h r)(fine:Tendsto h l (𝓝 0)):
    Tendsto (fun z:A×(ℕ×ℕ)=>chart R (k z.1) z.2.2 (h z.1) (hp z.1)) (l.curry U) Front:=by
  have period:Tendsto (@Prod.snd ℕ ℕ) f.fuse atTop:=tendsto_atTop.mpr fun t=>by
    rw [Extraction.Order.fused,Extraction.Order.late]
    filter_upwards [f.per.cofinal.eventually_ge_atTop t] with p late
    exact Eventually.of_forall fun _=>late
  apply Cirrus.goesFront
  constructor
  · apply Tendsto.comp fine
    exact tendsto_def.mpr fun a ha=>eventually_curry_iff.mpr ((show ∀ᶠ j in l,j∈a from ha).mono fun _ hx=>Eventually.of_forall fun _=>hx)
  · intro d
    apply tendsto_atTop.mpr
    intro M
    apply eventually_curry_iff.mpr
    apply Eventually.of_forall
    intro r
    have side:Tendsto (fun z:ℕ×ℕ=>(R.family.side (k r) z.2).val) U atTop:=
      tendsto_atTop_mono (fun z=>(R.family.S.period_strict.id_le z.2).trans (Nat.le_mul_of_pos_right _ (R.family.S.denominator _).pos))
        (period.mono_left hu)
    exact ((tendsto_natCast_atTop_atTop.comp side).const_mul_atTop (pow_pos (hp r) d)).eventually_ge_atTop M

variable (hG:G.Simple)(K:ℕ)
local notation "A"=>R.family.path.levels
local notation "m"=>WilsonMeasuredWindow.stop (A) hG K
def spacing (r:ℝ):ℝ:=if 0<r then R.family.S.a (m r)/r else 1

theorem positive (r:ℝ):0<spacing R hG K r:=by
  unfold spacing
  split_ifs with hr
  · exact div_pos (R.family.S.a_pos _) hr
  · exact zero_lt_one

theorem shrinking (hK:0<K):Tendsto (spacing R hG K) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  have growth:=WilsonMeasuredWindow.stop_tendsto (A) hG K hK
  have mass:Tendsto (fun r=>WilsonMeasuredAdmission.mast (A) (m r)) (𝓝[>] (0:ℝ)) atTop:=
    tendsto_atTop_mono (fun r=>show WilsonAdmissionScale.logarithm (A) (m r) ≤ 2+WilsonAdmissionScale.logarithm (A) (m r) from le_add_of_nonneg_left (by norm_num)) ((WilsonAdmissionScale.logarithm_tendsto (A) hG).comp growth)
  apply squeeze_zero' (Eventually.of_forall fun r=>(positive R hG K r).le) _ (tendsto_inv_atTop_zero.comp
    ((tendsto_pow_atTop hK.ne').comp mass))
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr':0<r:=hr
  rw [spacing,if_pos hr']
  change R.family.S.a (m r)/r≤(WilsonMeasuredAdmission.mast (A) (m r)^K)⁻¹
  rw [div_le_iff₀ hr',mul_comm,←div_eq_mul_inv,le_div_iff₀ (pow_pos (WilsonMeasuredAdmission.mast_pos (A) _) K)]
  exact WilsonMeasuredWindow.stop_spec (A) hG K hr'

theorem actual (hK:0<K)(f:Extraction.Order)(U:Filter (ℕ×ℕ))(hu:U≤f.fuse)
    (W:Initialize G){V:Normalize.Store G}(Y:Rose.Pick V):
    Tendsto (fun z:ℝ×(ℕ×ℕ)=>PowerSeries.coeff 1 (Rose.Detector W Y
      (chart R (m z.1) z.2.2 (spacing R hG K z.1) (positive R hG K z.1))))
      ((𝓝[>] (0:ℝ)).curry U) (𝓝 ((Rose.c_T Y:ℝ):ℂ)):=
  (Rose.diagnosed W Y hG).comp (reporting R _ f U hu (m) _ (positive R hG K) (shrinking R hG K hK))

end YM.Integration.WilsonSeparatedOriginalThermometerDetectorMesh
end
