import YM.Integration.NativeWilsonColoredMeasure

/-! The original startup path has identically zero loop action. The native
colors therefore give the complete first Wilson model on every field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCompensatedOpening
open Function Lattice Wilson RG Precision Exterior Marker Multi
open PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Assembly
open Next.SectorChange PertExtension.Series
open RegulatorIR.FVAAlt2
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (m p : ℕ)

def correction (t : ℝ) (U : Config G (R.family.side (m+1) p)) : ℝ := t^2*Precision.loop (R.family.path.rep (m+1) p (m+1)).path U

theorem dormant (t : ℝ) (U : Config G (R.family.side (m+1) p)) : correction R m p t U=0 := by
  rw [correction,Boot.kept0 R.family.path (RunFormalChain.fromRun R) (m+1) p U,mul_zero]

theorem all_orders (j : ℕ) : GradeAt j (Bulk.projected (correction R m p)) := by
  have zero : correction R m p=(0:ℝ → Config G (R.family.side (m+1) p) → ℝ) :=
    funext fun t=>funext fun U=>dormant R m p t U
  rw [zero]
  exact GradeAt.grade_zero j

variable {V : Type} [DecidableEq V] {Γ : Census V} (W : Bulk.Colors Γ G (R.family.side (m+1) p))

theorem weight (t : ℝ) (U : Config G (R.family.side (m+1) p)) :
    Integral.weight t 0 U (NativeWilsonColoredMeasure.colors R m p W) (R.family.path.rep (m+1) p (m+1)).clip (R.family.path.rep (m+1) p (m+1)).path=Wilson.bare (Integral.temperature t) U := by
  apply congrArg Real.exp
  change 0-(Integral.temperature t)*(mainTerm (R.family.path.rep (m+1) p (m+1)).clip (R.family.path.rep (m+1) p (m+1)).path U+
    (Wilson.energy U-mainTerm (R.family.path.rep (m+1) p (m+1)).clip (R.family.path.rep (m+1) p (m+1)).path U))-Precision.loop (R.family.path.rep (m+1) p (m+1)).path U=
      -(Integral.temperature t)*Wilson.energy U
  rw [Boot.kept0 R.family.path (RunFormalChain.fromRun R) (m+1) p U]
  ring

theorem marks (t : ℝ) (U : Config G (R.family.side (m+1) p)) :
    Integral.markedLog t U (NativeWilsonColoredMeasure.colors R m p W)=Integral.markedLog t U W := rfl

variable [Fintype V] in
theorem model {nc : Side} {S : StepData nc (R.family.side (m+1) p)} {O : ChartRatio G}
    (K : Bulk.Kernel S (R.family.path.rep (m+1) p (m+1)).clip (R.family.path.rep (m+1) p (m+1)).path O) (t : ℝ) :
    Integral.model t 0 (NativeWilsonColoredMeasure.colors R m p W) K=Bare.top W t := by
  funext U
  change (Integral.weight t 0 U (NativeWilsonColoredMeasure.colors R m p W) (R.family.path.rep (m+1) p (m+1)).clip (R.family.path.rep (m+1) p (m+1)).path:ℂ) • Poly.pass (Integral.markedLog t U (NativeWilsonColoredMeasure.colors R m p W))=_
  rw [weight R m p W t U,marks R m p W t U]
  rfl

end YM.Integration.WilsonCompensatedOpening
end
