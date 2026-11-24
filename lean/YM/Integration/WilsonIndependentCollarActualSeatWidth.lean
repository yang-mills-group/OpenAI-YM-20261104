import YM.Integration.WilsonIndependentCollarActualTeacher

/-! Fit the positive original physical teacher in the absolute printed
width, including the arity loss at every finite connected face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarActualSeatWidth
open Function Finset Lattice Wilson RG Precision RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Next.Scheduling Extra.Iteration Song ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Next.Foundations
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor WilsonCoeffUV WilsonOriginalCollarTeacher WilsonIndependentCollarRootedWidth
open scoped Classical BigOperators
variable {G:Gauge}

theorem original (request:Request G)(R:Run G)(simple:G.Simple)(ψ:ℕ→ℕ)(k x n:ℕ)
    (working:1≤k)(seats:n≤k)(u:ℝ)(wide:teacherWidth request R.metals.p.kernel x≤u):
    let D:=WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
    32*Poetry.Agenda.seed D ψ k x≤rooted n u:=by
  intro D
  let q:=Poetry.Agenda.seed D ψ k x
  have hq:0<q:=div_pos (lt_min (Poetry.Agenda.belt_p ..) (Poetry.Agenda.belt_p ..)) (by positivity)
  have bill:32*((n:ℝ)+1)*q≤u:=(WilsonIndependentCollarActualTeacher.original request R simple ψ k x n working seats).trans wide
  by_cases few:n≤3
  · rw [WilsonIndependentCollarRootedWidth.rooted,if_pos few]
    have room:32*(1:ℝ)≤32*((n:ℝ)+1):=by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have part:32*q≤32*((n:ℝ)+1)*q:=by simpa only [mul_one] using mul_le_mul_of_nonneg_right room hq.le
    exact part.trans bill
  · rw [WilsonIndependentCollarRootedWidth.rooted,if_neg few,le_div_iff₀ (by positivity)]
    calc
      _=32*((n:ℝ)+1)*q:=by change 32*q*((n:ℝ)+1)=_;ring
      _≤_:=bill

end YM.Integration.WilsonIndependentCollarActualSeatWidth
end
