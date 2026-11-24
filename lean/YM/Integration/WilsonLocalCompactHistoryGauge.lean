import YM.Integration.WilsonMeasuredInheritedGauge
import YM.Integration.WilsonCoherentEarlier

/-! The complete signed real Wilson observable retains its gauge invariance
at every held configuration of each earlier date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactHistoryGauge
open Function Filter Set Finset MeasureTheory Lattice RG Wilson
open scoped Classical Topology
variable {G:Gauge} (C:Family G) (makes:C.Makes) {N per j b:ℕ}

private theorem cast_one (h:Config G (C.side (j+1) per)→ℝ) (V:Config G (C.side j per)):
    actualAverage C (N:=N) (fun U=>(h U:ℂ)) V=Complex.ofReal (actualAverage C (N:=N) h V):=by
  let q:=actualConditionalDensity C N per j V
  have atU (U):q U • (h U:ℂ)=((q U • h U:ℝ):ℂ):=(Complex.ofRealCLM.map_smul (q U) (h U)).symm
  change (∫U,q U • (h U:ℂ) ∂prior G _)=(↑(∫U,q U • h U ∂prior G _):ℂ)
  simp_rw [atU]
  exact integral_ofReal

include makes in
theorem original (top:b≤N) (live:j≤b) (H:Config G (C.side b per)→ℝ) (eh:Envelope H) (gh:GaugeInvariant H):
    let Z:=actualTransport C (N:=N) H live
    Envelope Z ∧ GaugeInvariant Z:=by
  intro Z
  let Y:=fun U=>(H U:ℂ)
  have ey:Envelope Y:=⟨Complex.continuous_ofReal.measurable.comp eh.meas,eh.cost.choose,fun U=>by simpa only [Y,Complex.norm_real] using eh.cost.choose_spec U⟩
  have gy:GaugeInvariant Y:=fun a U=>congrArg Complex.ofReal (gh a U)
  have same (i:ℕ) (hi:i≤b):actualTransport C (N:=N) Y hi=fun U=>Complex.ofReal (actualTransport C (N:=N) H hi U):=by
    induction hi using Nat.decreasingInduction with
    | self=>rw [actualTransport_base C makes top,actualTransport_base C makes top]
    | of_succ t ht ih=>
      rw [actualTransport_step C makes top Y ht,actualTransport_step C makes top H ht,ih]
      exact funext (cast_one C _)
  have enrolled:=(WilsonMeasuredInheritedGauge.original C makes top live Y ey gy).2
  rw [same j live] at enrolled
  exact ⟨WilsonCoherentEarlier.envelope C makes top eh live,fun a U=>Complex.ofReal_injective (enrolled a U)⟩

end YM.Integration.WilsonLocalCompactHistoryGauge
