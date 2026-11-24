import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerHorizon
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerKinetic
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

theorem original {I:Type*}{l:Filter I}[NeBot l]{s:ℝ}{t g:I→ℝ}
    (ratio:Tendsto t l (𝓝 s))(income:∀ᶠ i in l,1/8≤g i ∧ g i≤12):
    ∃ lc:Filter I,NeBot lc ∧ lc≤l ∧ ∃b:ℝ,1/8≤b ∧ b≤12 ∧
      ∀d q:ℕ,Tendsto (fun i=>(t i)^d*(g i)^q) lc (𝓝 (b^q*s^d)):=by
  have roof:∀ᶠ i in l,‖g i‖≤12:=by
    filter_upwards [income] with i entry
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith only [entry.1])]
    exact entry.2
  obtain ⟨lc,sub,live,b,conv⟩:=Next.UVStress.finite_extract g 12 roof
  letI:=live
  have paid:=income.filter_mono sub
  refine ⟨lc,live,sub,b,ge_of_tendsto conv (paid.mono fun _ h=>h.1),
    le_of_tendsto conv (paid.mono fun _ h=>h.2),fun d q=>?_⟩
  simpa only [mul_comm (b^q)] using ((ratio.mono_left sub).pow d).mul (conv.pow q)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerKinetic
end
