import YM.Integration.WilsonSurveyedColorVacuumJoint
import YM.Integration.WilsonSurveyedColorVacuumTests

/-! The actual color substitution and the open-rank extraction on the MS
bulk and marked equations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumComponents
open Function Set Filter MS Plane Koszul Heat Flux Arts Pilot Spin Arc Wire Rock Path Oceans
open Landau Alps Garment Shine Hem Mell Pearl Train Dock
open WilsonSurveyedColorQuotient WilsonSurveyedColorPilot WilsonSurveyedColorSubtraction
open WilsonSurveyedColorVacuumTests WilsonSurveyedColorVacuumJoint
open scoped Classical BigOperators Topology
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)

def color : Action G where
  read := allDims U
  scale := dilation U
  hol := forest U
  tends := limit U
  diff {F H s} h m l := by
    let V := Centre (Legs (Shore G m))
    have each (T : Rack G m → ℂ) (ht : T∈V) :
        HasDerivAt (fun t => T (F t m)) (T (H m)) s := by
      refine Submodule.span_induction
        (p:=fun T _ => HasDerivAt (fun t => T (F t m)) (T (H m)) s) ?_
        (hasDerivAt_const ..) (fun _ _ _ _ ha hb => ha.add hb)
        (fun c _ _ hx => hx.const_mul c) ht
      rintro _ ⟨i,rfl⟩
      exact h m i
    change HasDerivAt (fun t => turn U (F t m) l) (turn U (H m) l) s
    simpa only [emits] using each _ ((pilot U).sense.reaches l)

def rank (k : ℤ) : Action G where
  read := spot k
  hol := fun h => spot_hol h k
  scale a t F := by
    funext m l
    by_cases h : (l.length:ℤ)=k
    · rw [spotted h]; unfold plow
      rw [spotted (by simpa [sr] using h : ((sr t l).length:ℤ)=k)]
    · rw [spotsOff h]; unfold plow
      rw [spotsOff (by simpa [sr] using h : ((sr t l).length:ℤ)≠k),mul_zero]
  tends {F H} h m l := by
    by_cases e : (l.length:ℤ)=k
    · simpa only [spotted e] using h m l
    · simp only [spotsOff e]; exact tendsto_const_nhds
  diff {F H s} h m l := by
    by_cases e : (l.length:ℤ)=k
    · simpa only [spotted e] using h m l
    · simp only [spotsOff e]; exact hasDerivAt_const ..

end YM.Integration.WilsonSurveyedColorVacuumComponents
end
