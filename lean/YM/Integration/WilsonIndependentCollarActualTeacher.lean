import YM.Integration.WilsonIndependentCollarMovingInk

/-! The actual planted Wilson teacher already reserves the whole finite
roster in its native lease. This is on the same selected original roots. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarActualTeacher
open Function Finset Lattice Wilson RG Precision RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Next.Scheduling Extra.Iteration Song ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Next.Foundations
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor WilsonCoeffUV WilsonOriginalCollarTeacher
open private leased from YM.Integration.WilsonOlderFreshGraphStrip
open scoped Classical BigOperators
variable {G:Gauge}

theorem lease (a:ℝ)(non:0≤a)(k:ℕ):
    32*((k:ℝ)+1)*leaseF a (k+2) ≤ a:=by
  have denom:0<(128:ℝ)*(k+6)^2:=by positivity
  have ratio:leaseF a (k+2)=a/(128*((k:ℝ)+6)^2):=by
    unfold leaseF AllOrder.Ker.small_a Iron.breath Push.Uniform.weaker
    push_cast
    field_simp
    ring
  rw [ratio,←mul_div_assoc,div_le_iff₀ denom]
  have budget:32*((k:ℝ)+1)≤128*((k:ℝ)+6)^2:=by nlinarith [sq_nonneg (k:ℝ),Nat.cast_nonneg (α:=ℝ) k]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right budget non

theorem seed {A:ℕ→Stage}{p:MapPrices}{K:KernelChoices}(D:Roots (G:=G) A p K)(ψ:ℕ→ℕ)
    (k x:ℕ)(a:Age)(seen:a∈Step.tape (k+2)):
    32*((k:ℝ)+1)*Poetry.Agenda.seed D ψ k x≤D.pre k x a:=by
  let τ:=Poetry.Agenda.stipend D k x
  have stock:=(Poetry.Agenda.receives D k x).choose_spec
  have hp:0<τ:=stock.1
  have edge:τ≤leaseF (D.pre k x a) (k+2):=stock.2.2 a seen
  have c₀:0≤Poetry.Agenda.poll D k x:=(AllOrder.Ink.Money.soprano _ hp _).le
  have c₁:Poetry.Agenda.poll D k x≤τ:=AllOrder.Ink.Money.gestate _ hp (Nat.zero_le _)
  have size:1≤(Poetry.Agenda.burden (k+4):ℝ):=by
    unfold Poetry.Agenda.burden
    exact_mod_cast (show 1≤(8*(k+4)+1)*((k+4+1)*2) by nlinarith)
  have waist:Poetry.Agenda.waist D k x≤Poetry.Agenda.poll D k x:=div_le_self c₀ (one_le_pow₀ size)
  have next:Poetry.Agenda.seed D ψ k x≤leaseF (D.pre k x a) (k+2):=
    (div_le_self (le_min (Poetry.Agenda.belt_p D k x).le (Poetry.Agenda.belt_p D k (x+1)).le)
      (by exact_mod_cast (show 1≤ψ k+1 by omega))).trans ((min_le_left ..).trans (waist.trans (c₁.trans edge)))
  exact (mul_le_mul_of_nonneg_left next (by positivity)).trans (lease _ ((D.shape k).pos x a).le k)

theorem original (request:Request G)(R:Run G)(simple:G.Simple)(ψ:ℕ→ℕ)(k x n:ℕ)
    (working:1≤k)(seats:n≤k):
    let D:=WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
    32*((n:ℝ)+1)*Poetry.Agenda.seed D ψ k x≤teacherWidth request R.metals.p.kernel x:=by
  intro D
  let a:Age:=⟨0,0,by omega⟩
  have seen:a∈Step.tape (k+2):=Age.in_scope.mpr (by change 0+3≤k+2;omega)
  let M:=menu request
  let H:=R.metals.p
  let B:=R.metals.K
  have raw:D.pre k x a≤M.width H.profile B H.kernel k x/(16*M.shell k):=
    (leased simple H.profile B H.kernel (M.width H.profile B H.kernel) M.shell
      (M.positive H.profile B H.kernel) M.cost).choose_spec k x a
  have positive:0<Poetry.Agenda.seed D ψ k x:=div_pos (lt_min (Poetry.Agenda.belt_p ..) (Poetry.Agenda.belt_p ..)) (by positivity)
  have card:(n:ℝ)≤k:=by exact_mod_cast seats
  have first:=seed D ψ k x a seen
  calc
    _ ≤ 32*((k:ℝ)+1)*Poetry.Agenda.seed D ψ k x:=mul_le_mul_of_nonneg_right (by linarith only [card]) positive.le
    _ ≤ _:=first
    _ ≤ _:=raw
    _ ≤ M.width H.profile B H.kernel k x:=div_le_self (M.positive ..).le (by norm_num [M,menu])
    _ ≤ _:=min_le_right ..

end YM.Integration.WilsonIndependentCollarActualTeacher
end
