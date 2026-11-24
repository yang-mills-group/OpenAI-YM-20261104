import YM.Integration.WilsonThermometerOriginalCoveredRows
import YM.Integration.WilsonThermometerOriginalClockSlope
import YM.Integration.WilsonPositionProgramDeclaredForest

/-! Signed occupied and vacuum coefficients on the unreplicated finite chronological program. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalFilmRows
open Function Filter MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Order Comparison.RG02.Order.First Comparison.RG02.Symmetry Comparison.RG02.Adjacent
open Comparison.RG02.Assembly YM.Primitives.GCC.Anchor WilsonThermometerOriginalCoveredRows
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (t:S.Choices) {V:Type} [Fintype V] [DecidableEq V]
  {R:Census V} (W:Bulk.Colors R G f) (r:ℕ) (live:0<r) (s:R.Mode) (x:fieldDir G c 1)

local notation "m" a:max=> base K F t W a
local notation "h" a:max=> first K F t W a
include live

/-- Each of the marked faces is read after applying the same quiet normalization. -/
theorem occupied : Orbit.words K F t W r s 0 x=(Extra.Trajectories.connected (m x)).part s ∧
    Orbit.words K F t W r s 1 x=(h x * inverseMass (m x) - Poly.bead R ((h x).part R.quiet)).part s := by
  obtain ⟨h₀,h₁⟩:=signed K F t W x r live
  exact ⟨congrArg (fun z:Poly R=>z.part s) h₀,congrArg (fun z:Poly R=>z.part s) h₁⟩

/-- The affine classical price is paid once. The first vacuum face is the full signed numerator. -/
theorem quiet : Orbit.ground K F t W r 0 x=Symmetry.price K F t x ∧
    Orbit.ground K F t W r 1 x=(h x).part R.quiet := by
  refine ⟨Adjacent.LocalScript.precedence K F t W r x,?_⟩
  simp only [Orbit.ground,if_neg one_ne_zero,add_zero]
  change Second.lit 1 (logVac _) = _
  rw [Second.offset_one (Bulk.fk_sym ..) (Bulk.fk_unit ..) live]
  exact congrArg (fun z:Poly R=>z.part R.quiet) (joint K F t W x r live).2

theorem markedReset (clock:UnitCost) (flat:HasDerivAt clock.rating 0 0)
    (D:BudgetPoint) (legal:Bulk.Well W) :
    born (Orbit.words K F t W r s) clock 0 r 0 x=(Extra.Trajectories.connected (m x)).part s ∧
    born (Orbit.words K F t W r s) clock 0 r 1 x=
      (h x*inverseMass (m x)-Poly.bead R ((h x).part R.quiet)).part s := by
  have aa:=Orbit.colored K D F t W r s legal
  have ⟨zero,one⟩:=occupied K F t W r live s x
  exact ⟨(WilsonThermometerOriginalClockSlope.zeroth _ clock r x).trans zero,
    (WilsonThermometerOriginalClockSlope.first _ clock flat r live
      (fun j hj=>(aa.known j hj).differentiable (by simp)) x).trans one⟩

theorem quietReset (clock:UnitCost) (flat:HasDerivAt clock.rating 0 0)
    (D:BudgetPoint) (legal:Bulk.Well W) :
    born (Orbit.ground K F t W r) clock 0 r 0 x=Symmetry.price K F t x ∧
    born (Orbit.ground K F t W r) clock 0 r 1 x=(h x).part R.quiet := by
  have aa:=Orbit.bed K D F t W r legal
  have ⟨zero,one⟩:=quiet K F t W r live x
  exact ⟨(WilsonThermometerOriginalClockSlope.zeroth _ clock r x).trans zero,
    (WilsonThermometerOriginalClockSlope.first _ clock flat r live
      (fun j hj=>(aa.known j hj).differentiable (by simp)) x).trans one⟩

end YM.Integration.WilsonThermometerOriginalFilmRows
