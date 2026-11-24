import YM.Integration.WilsonPhysicalHistoryRetainedSpring

/-! The true old group input can be rough. Only the optional identification
with its no-flags model uses the original flag condition. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice Wilson RG Precision Exterior IterationFour IterationFour.Vacuum PhysicalNext.Repeat.Legato
open LocalComparison Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open scoped BigOperators Classical
variable {G : Gauge} {N per r : ℕ}

theorem spring_field (R : Run G) (P : Plan R.family N per r) (m : ℕ)
    {g : ℝ} (hg : g≠0) (U : Config G (R.family.side m per)) :
    let K:=(R.family.path.rep N per m).path
    let B:=(R.family.path.levels.params m).clip
    let α:=P.alpha m
    let p:=ActualAnalyticPlanVacuum.radicand R P m g
    let c:=ActualAnalyticPlanVacuum.coupling R P m g
    Integral.temperature g * ActualAnalyticPlanVacuum.vacuum R P m g U - α*secondTerm B K U =
      (P.poly m g-α)*mainTerm B K U + α*interaction K U+
      (Integral.temperature g*p)*
        ((P.layers m).map (fun a=>c^(a.power+2-a.rank)*unmaskedPayload a.packet U)).sum := by
  dsimp only
  rw [←curvature_pair (R.family.path.levels.params m).clip]
  simp only [ActualAnalyticPlanVacuum.vacuum,ActualAnalyticPlanVacuum.kinetic,
    ActualGradedVacuum.restored,Integral.temperature]
  field_simp [hg]
  ring

theorem spring_model (R : Run G) (P : Plan R.family N per r) (m : ℕ)
    {point : BudgetPoint} {cap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point r cap width budget)
    {g : ℝ} (hg : 0<g) (hb : 0<(g^2)⁻¹+P.poly m g) (U : Config G (R.family.side m per))
    (healthy : flags (R.family.path.levels.budget m).threshold U=∅) :
    let K:=(R.family.path.rep N per m).path
    let B:=(R.family.path.levels.params m).clip
    let α:=P.alpha m
    let p:=ActualAnalyticPlanVacuum.radicand R P m g
    let c:=ActualAnalyticPlanVacuum.coupling R P m g
    modelAction P m g U-(Integral.temperature g*mainTerm B K U+Precision.loop K U+α*secondTerm B K U) =
      (P.poly m g-α)*mainTerm B K U+α*interaction K U+
      (Integral.temperature g*p)*
        ((P.layers m).map (fun a=>c^(a.power+2-a.rank)*unmaskedPayload a.packet U)).sum := by
  dsimp only
  rw [←ActualAnalyticPlanVacuum.model_action R P m H hg hb U healthy,←spring_field R P m hg.ne' U]
  ring

end YM.Integration.OriginalMarkedRunAction
