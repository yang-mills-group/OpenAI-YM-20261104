import YM.Integration.WilsonMeasuredSignedActionOwnedIncome
import YM.Integration.WilsonPositionScaleLawCompactNative

/-! The original physical stress trace is common to the two radii. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonMeasuredSignedActionTraceRatio
open Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS
open Lattice RG Wilson Extra.Histories Trace Trace.Physical Trace.Terrace Trace.Pilot
open Function Next.UVStress Work.A01 Maxwell UVNext.FreeStress Spin StressFlux TraceExtension MergeProof.East Next.Rank
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (bothHomes)
open scoped Topology
variable [Win:RangeSpec] {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S){b g:ℝ→ℝ}

omit Win in
theorem negative (simple:G.Simple)(cal:TendC F (fun r=>J r 4) b)(heat:Coupling G g):
    ∀ᶠ r in trail,b r<0:=by
  let β:ℝ:=11*G.casimir/(48*Real.pi^2)
  have hb:0<β:=by dsimp [β];have hs:=Gauge.casimir_pos simple;positivity
  have limit:Tendsto (fun r=>b r/g r^2) trail (𝓝 (-β/2)):=cal.measures g heat
  have lower:-β/2<0:=by linarith
  filter_upwards [limit.eventually (Iio_mem_nhds lower)] with r hr
  change b r/g r^2<0 at hr
  by_contra! h
  exact (not_lt_of_ge (div_nonneg h (sq_nonneg (g r)))) hr

omit Win in
private theorem factor {c:ℂ}{r:ℝ}(neg:b r<0)
    (eqn:r^4 • center F=(4*b r) • J r 4 (stepField C)+r^4 • (c • S.unit 4)):
    J r 4 (stepField C)=(r^4/(4*b r)) • (center F-c • S.unit 4):=by
  have nz:4*b r≠0:=mul_ne_zero (by norm_num) neg.ne
  have eq':(4*b r) • J r 4 (stepField C)=r^4 • (center F-c • S.unit 4):=by
    rw [smul_sub]
    exact eq_sub_of_add_eq eqn.symm
  calc
    J r 4 (stepField C)=(4*b r)⁻¹ • ((4*b r) • J r 4 (stepField C)):=by
      rw [smul_smul,inv_mul_cancel₀ nz,one_smul]
    _=(r^4/(4*b r)) • (center F-c • S.unit 4):=by
      rw [eq',smul_smul]
      congr 1
      ring

theorem original (simple:G.Simple)(cal:TendC F (fun r=>J r 4) b)(heat:Coupling G g):
    ∀ᶠ z:ℝ×Ratio in sweep,0<b z.1/b (z.2.val*z.1) ∧
       J (z.2.val*z.1) 4 (stepField C)=
         (z.2.val^4*(b z.1/b (z.2.val*z.1))) • J z.1 4 (stepField C):=by
  obtain ⟨c,trace⟩:=cal.centered
  have rows : ∀ᶠ r in trail, b r<0 ∧ J r 4 (stepField C)=
      (r^4/(4*b r)) • (center F-c • S.unit 4):=by
    filter_upwards [negative F J simple cal heat,trace] with r neg row
    exact ⟨neg,factor F J neg row⟩
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually rows,
    bothHomes.eventually rows] with z old new
  refine ⟨div_pos_of_neg_of_neg old.1 new.1,?_⟩
  rw [new.2,old.2,smul_smul]
  congr 1
  field_simp [old.1.ne,new.1.ne]

end YM.Integration.WilsonMeasuredSignedActionTraceRatio
end
