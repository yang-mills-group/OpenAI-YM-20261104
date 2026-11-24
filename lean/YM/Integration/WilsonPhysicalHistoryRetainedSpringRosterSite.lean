import YM.Integration.WilsonPhysicalHistoryRetainedSpringRoster
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRosterMoment

/-! Sum the errors of the actual dated action terms before integrating or
bounding any of their external partners. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {Ω : Type*} [MeasurableSpace Ω]

theorem roster_site_moment (μ : Measure Ω) (U : Ω → Config G n) (z : Ω → Dir G n)
    (path : PathData G) (Z : SeriesA G) (w b c : ℝ) (x : Site n) (K l M : ℕ) (g : ℝ)
    (limit : Z.length≤M) {fee : ℝ} (positive : 0≤fee)
    (row : ∀ a∈Z,
      let E:=fun y=>((b*c^(a.grade-a.rise):ℝ):ℂ)*
        ((sitePacket a.cells x (U y):ℂ)-siteTaylor a.cells x (z y) (a.rise+K+1) g)
      Integrable E μ ∧ Integrable (fun y=>‖E y‖^(l+1)) μ ∧ (∫ y,‖E y‖^(l+1) ∂μ)≤fee^(l+1))
    (extra :
      let E:=fun y=>(w:ℂ)*((interactionAt path x (U y):ℂ)-
        interactionTaylor path x (z y) (fun i=>if i then K+3 else K+2) g)
      Integrable E μ ∧ Integrable (fun y=>‖E y‖^(l+1)) μ ∧ (∫ y,‖E y‖^(l+1) ∂μ)≤fee^(l+1))
    (bare : Bool) :
    let E:=fun y=>rosterSource path Z w b c bare x (U y)-rosterTaylor path Z w b c bare x (z y) K g
    Integrable E μ ∧ Integrable (fun y=>‖E y‖^(l+1)) μ ∧
      (∫ y,‖E y‖^(l+1) ∂μ)≤(((M:ℝ)+1)*fee)^(l+1) := by
  intro E
  let a:=fun (i : Fin Z.length) y=>((b*c^((Z.get i).grade-(Z.get i).rise):ℝ):ℂ)*
    ((sitePacket (Z.get i).cells x (U y):ℂ)-siteTaylor (Z.get i).cells x (z y) ((Z.get i).rise+K+1) g)
  let h:=fun y=>if bare then (w:ℂ)*((interactionAt path x (U y):ℂ)-
    interactionTaylor path x (z y) (fun i=>if i then K+3 else K+2) g) else 0
  have low : Integrable h μ ∧ Integrable (fun y=>‖h y‖^(l+1)) μ ∧ (∫ y,‖h y‖^(l+1) ∂μ)≤fee^(l+1):=by
    cases bare
    · simpa [h] using pow_nonneg positive (l+1)
    · exact extra
  have same : E=fun y=>h y+∑ i,a i y:=by
    funext y
    exact roster_difference path Z w b c bare x (U y) (z y) K g
  rw [same]
  exact roster_moment μ limit l positive a h (fun i=>row _ (List.get_mem Z i)) low

end YM.Integration.OriginalMarkedRunAction
