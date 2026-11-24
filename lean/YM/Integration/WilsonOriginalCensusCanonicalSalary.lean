import YM.Integration.WilsonOriginalCensusCanonicalRows
import YM.Integration.WilsonIndependentCollarActualTeacher

/-! Uniform cost of the finitely many canonical top stencils, at the teacher
actually elected on the original hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalSalary
open Finset Filter Lattice Wilson RG Source Labels Marker QuadraticLocal PhysicalNext PhysicalNext.Repeat.Legato
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Next.Foundations
open WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords WilsonOriginalCensusCanonicalRows
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open WilsonOriginalCollarTeacher
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem strip (request:Request G)(K:KernelChoices)(x:ℕ):teacherWidth request K x≤1:=by
  let zero:Entries x:=(0,0,0,0,0)
  have le:=Finset.inf'_le (s:=(univ:Finset (Entries x)))
    (fun a:Entries x=>atStages request K a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) (mem_univ zero)
  exact le.trans (by simp [zero,atStages])

theorem actual (request:Request G)(R:Run G)(simple:G.Simple)(ψ:ℕ→ℕ)(k x:ℕ)(working:1≤k):
    let D:=WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
    Poetry.Agenda.seed D ψ k x≤1:=by
  intro D
  have le:32*((0:ℝ)+1)*Poetry.Agenda.seed D ψ k x≤1:=
    by simpa only [Nat.cast_zero] using (WilsonIndependentCollarActualTeacher.original request R simple ψ k x 0 working (Nat.zero_le _)).trans (strip ..)
  linarith only [le]

variable {V:Type}[Fintype V][DecidableEq V](R:Run G)(d:V→ℕ)
omit [Fintype V] [DecidableEq V] in
theorem monotone (j:V)(c:Choice R d j){σ τ:ℝ}(h:σ≤τ):price R d σ j c≤price R d τ j c:=by
  let a:=raw R d (entry R d j c)
  have leg:Real.exp (σ*a.length)≤Real.exp (τ*a.length):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))
  have mag:0≤a.magnitude:=sum_nonneg (fun _ _=>abs_nonneg _)
  have atom:a.budget σ≤a.budget τ:=mul_le_mul_of_nonneg_left leg mag
  change (1+(1+a.budget σ))*Real.exp (σ*a.length)≤(1+(1+a.budget τ))*Real.exp (τ*a.length)
  exact mul_le_mul (by linarith only [atom]) leg (Real.exp_nonneg _)
    (by linarith only [WilsonOriginalProjectedCurvatureSalary.amount a τ])

omit [DecidableEq V] in
theorem bound (q:(j:V)→Choice R d j){σ:ℝ}(narrow:σ≤1):
    max 1 (WilsonOriginalCensusCanonicalRows.charge R d q σ (fun _=>1)) ≤ max 1 (WilsonOriginalCensusCanonicalRows.ceiling R d 1):=by
  refine max_le_max le_rfl ((WilsonOriginalCensusCanonicalRows.one R d q σ).trans (sum_le_sum (fun j _=>?_)))
  exact sum_le_sum (fun c _=>monotone R d j c narrow)

omit [DecidableEq V] in
theorem original (request:Request G)(simple:G.Simple)(ψ:ℕ→ℕ):
    let D:=WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
    ∀ᶠ i:ℕ in atTop,∀(k x:ℕ),1≤k→∀q:(j:V)→Choice R d j,
      max 1 (WilsonOriginalCensusCanonicalRows.charge R d q (Poetry.Agenda.seed D ψ k x) (fun _=>1))≤R.family.path.levels.clock.hatBeta i:=by
  intro D
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (max 1 (WilsonOriginalCensusCanonicalRows.ceiling R d 1))]
    with i opened k x live q
  exact (bound R d q (actual request R simple ψ k x live)).trans opened

end YM.Integration.WilsonOriginalCensusCanonicalSalary
end
