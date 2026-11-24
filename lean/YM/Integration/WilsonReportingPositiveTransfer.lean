import YM.Integration.WilsonReportingScalarRoute

/-! The unsigned majorant for a signed field follows the genuine positive
Wilson transition, with the full physical vacuum at the incoming and
outgoing dates. The bound holds at each fixed coarse configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPositiveTransfer
open Function Filter Finset MeasureTheory Lattice Wilson RG Source RG05Readout Address Native
open Extra.Histories MergeProof Accent
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {N per m d:ℕ}

theorem single (h:C.Makes) (live:m<N) (F:Goods G (C.side (m+1) per)) (b:ℝ)
    (paid:∀ U, ‖F U‖ ≤ b*(C.path.rep N per (m+1)).eval U) (V:Config G (C.side m per)) :
    ‖(C.path.levels.clock.op m per).push (C.path.β N per (m+1)) F V‖ ≤ b*(C.path.rep N per m).eval V := by
  let S:=C.path.levels.clock.op m per
  let β:=C.path.β N per (m+1)
  let w:=(C.path.rep N per (m+1)).eval
  let μ:=prior G (C.side (m+1) per)
  have kernel:S.IsKernel β G:=C.path.levels.transition_mass m per β
  have hw:Integrable w μ:=((C.path.rep N per (m+1)).envelope (h.wilson.represents N per (m+1) live).good).integrable _
  have weight:Integrable (fun U=>S.density β U V*w U) μ:=StepData.push_slice kernel V w hw
  have total:(∫ U,S.density β U V*w U ∂μ)=(C.path.rep N per m).eval V:=
    (congrFun (h.wilson.steps N per m live).1 V).symm
  rw [←total,←integral_const_mul]
  apply norm_integral_le_of_norm_le (weight.const_mul b)
  filter_upwards with U
  change ‖S.density β U V • F U‖ ≤ b*(S.density β U V*w U)
  rw [norm_smul,Real.norm_of_nonneg (kernel.positive U V)]
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (paid U) (kernel.positive U V)

theorem sector (h:C.Makes) (live:m<N) (F:Goods G (C.side (m+1) per)) (b:ℝ)
    (paid:∀ U, ‖F U‖ ≤ b*(C.path.rep N per (m+1)).eval U) (V:Config G (C.side m per)) :
    ‖blast C.path N per m d F V‖ ≤ (C.S.block m).val^d*(b*(C.path.rep N per m).eval V) := by
  change ‖(((C.S.block m).val:ℂ)^d) • ((C.path.levels.clock.op m per).push _ F V)‖ ≤ _
  rw [norm_smul,norm_pow,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (single h live F b paid V) (by positivity)

end YM.Integration.WilsonReportingPositiveTransfer
