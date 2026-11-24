import YM.MergeProof.Plaza
import YM.Comparison.RG02.Actual.Charge

/-! Componentwise and vector-valued Wilson transport of the original finite
signed marked menu, including its full physical forced teams. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMenuIntegration
open Finset Lattice RG RG.Patch Marker MeasureTheory Pressure Pressure.Tube
open ConnectedActivityE6 Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open Merge MergeProof Palette Push.SectorMeasure Wilson
open Comparison.RG02 Comparison.RG02.Actual
open scoped Topology BigOperators Classical
variable {G:Gauge} {c f L:Side} {S:StepData c f} {P:Teller G} {T:Tube G S} {R:Rep G f}
  {W x μ C:ℝ} {Q:Target G P} {o:Target.Order G W}
  (H:Cash W x μ L Q o C T R) {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι]
  {Γ:Census V} (M:ι→Menu.Hat Γ R) (w:V→ℝ)

include H in
theorem integrable : Integrable (Menu.Expense M w S) (prior G f) := by
  unfold Menu.Expense Merge.Photo.given
  apply integrable_finsetSum
  intro i _
  let leaf (j:ι) := (M j).M
  let p := team (S:=S) leaf i
  let scal:ℝ := ∏j∈i.val,Menu.sumFee (M j) w
  let ink:Marker.Poly Γ := ∏j∈i.val,Menu.sing (M j) w
  have hs:Envelope p.cicada := (p.sells H.laws.intake.cap).1
  have hp:Integrable p.cicada (prior G f) := hs.integrable (prior G f)
  have hq:Integrable (fun U => p.cicada U * scal) (prior G f) := hp.mul_const scal
  exact Function.const ℕ (hq.ofReal.smul_const ink) (Fintype.card V)

include H in
theorem integrated (y:Config G c) :
    Actual.Push S R.beta (Menu.Expense M w S) y=S.push R.beta (Menu.Expense M w S) y := by
  let Z:=Menu.Expense M w S
  have ht:S.IsKernel R.beta G:=S.isKernel (funds_branch H.laws.intake.ready) _
  have hI:=StepData.push_slice ht y Z (integrable H M w)
  apply Marker.Poly.ext
  intro s
  let A:Poly Γ→L[ℝ] ℂ:=(Marker.Poly.get s).restrictScalars ℝ
  calc
    _ = S.push R.beta (fun U=>(Z U).part s) y := congrFun (Actual.grades (D:=Z) y R.beta) s
    _ = ∫U,A (S.density R.beta U y • Z U) ∂prior G f := by
      unfold StepData.push
      exact integral_congr_ae (ae_of_all _ fun U=>(A.map_smul _ _).symm)
    _ = A (∫U,S.density R.beta U y • Z U ∂prior G f) := A.integral_comp_comm hI
    _ = _ := rfl

end YM.Integration.ManuscriptQLocalMenuIntegration
