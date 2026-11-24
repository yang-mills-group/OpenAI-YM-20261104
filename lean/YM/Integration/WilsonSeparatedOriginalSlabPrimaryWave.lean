import YM.Integration.WilsonReportingTerminalPrimaryStencil
import YM.Integration.WilsonReportHarvestReadmittedSource

/-! The original returned primary differentiates none of the external test slots. Its signed normalization is the original zeroth Fourier probe in each slot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabPrimaryWave
open Function Set Tensor RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse
open WilsonReportingUnitOrbit
open scoped ContDiff BigOperators Classical
variable {I:Type}[Fintype I][DecidableEq I]

def inkSum (d:ℕ):ℂ:=∑u∈paint (primary d),ink (primary d) u

theorem single {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (d:ℕ)(f:Complexion E)(direction:E4→E):
    lat (primary d) direction f=inkSum d • f:=by
  change (∑u∈paint (primary d),ink (primary d) u • tires (direction u) 0) f=_
  simp only [tires,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.id_apply]
  rw [inkSum,Finset.sum_smul]

theorem price (d:ℕ):inkSum d=phase⁻¹:=by
  let g:=Native.line Suede.pip
  have matchProbe: (lat (primary d) id g).val 0=readJ (primary d) 0 g:=(values (primary d) id g 0).trans (sample (primary d) 0 g).symm
  have probe:readJ (primary d) 0 g=1:=by change readJ Suede.pip 0 (Native.line Suede.pip)=1;rw [headC,if_pos rfl]
  rw [single] at matchProbe
  have result:inkSum d*phase=1:=matchProbe.trans probe
  apply (eq_div_iff (Suede.pitch_pos _)).mpr at result
  change inkSum d=((Native.line Suede.pip).val 0)⁻¹
  simpa only [one_div] using result

theorem run (s:I→ℕ)(names:List I)(Φ:Wave I):
    machine s (fun i=>primary (s i)) names Φ=(phase⁻¹)^names.length • Φ:=by
  induction names generalizing Φ with
  | nil=>simp only [machine,LinearMap.id_apply,List.length_nil,pow_zero,one_smul]
  | cons z l ih=>
    change machine s (fun i=>primary (s i)) l (lat (primary (s z)) _ Φ)=_
    rw [single,price,map_smul,ih,smul_smul,List.length_cons,pow_succ,mul_comm]

theorem waveform (s:I→ℕ)(Φ:Wave I):perform s (fun i=>primary (s i)) Φ=(phase⁻¹)^(Fintype.card I) • Φ:=by
  rw [perform,run];simp

end YM.Integration.WilsonSeparatedOriginalSlabPrimaryWave
