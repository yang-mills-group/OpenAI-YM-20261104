import YM.Integration.WilsonNeutralAppointedChildPupil
import YM.Integration.WilsonOriginalFiledCopiedStep

/-! The real tested direction at the located parent and independence of
the marked pupil read from the silent layout slot on this held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralReportedLinkChart
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Push.Uniform AllOrder AllOrder.Floe AllOrder.Floe.Step Comparison QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Sunrise Comparison.RG02.Bulk
open Comparison.RG02 Comparison.RG02.Assembly Marker Multi
open FVA1Physical.TwoReset PertExtension.Series Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Classical BigOperators ContDiff

def located (G:Gauge)(n:Side)(y:Site n):Stationary.Link G n →ₗ[ℝ] (wire G n→ℝ) where
  toFun B:=FreeResolvent.flatten (Stationary.arm G n 1 B) ∘ Lotus.tint y
  map_add' B C:=by
    funext v
    simp [Function.comp_apply,Stationary.arm,FreeResolvent.flatten]
  map_smul' t B:=by
    funext v
    simp [Function.comp_apply,Stationary.arm,FreeResolvent.flatten]

theorem layout {G:Gauge}{V ι X:Type}[DecidableEq V][Fintype V]{c n:Side}
    {J:Earn.Passport n V}{R:Census V}(h:n.val∣c.val)(M:ι→Row J R G X)(w:V→ℕ)(L₁ L₂:Layout G)(T:Finset Age)
    (x:X)(j:ℕ)(B:Stationary.Link G c)(s:Multi.Hot R){a:ℝ}{k:ℕ}(staff:Air.Staff M (fun j=>(M j).paint x) w a k):
    (peek h M w L₁ T x j B).part s.val=(peek h M w L₂ T x j B).part s.val  := by
  exact congrArg (fun A:Poly R=>A.part s.val) ((total_peek h M w L₁ T x B j staff).unique
    (total_peek h M w L₂ T x B j staff))

end YM.Integration.WilsonNeutralReportedLinkChart
end
