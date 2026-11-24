import YM.Integration.WilsonWindowBookPurchase

/-! A pre-block choice of the one school, including the prescribed graph's spatial strip. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphStrip

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Extra.Histories Source JointLoad JointLoad.Heir JointLoad.Heir.Suite
open JointLoad.Psalm Clockwork AnalyticBridge VerifiedReset Collection Quotes
open Next.Scheduling Extra.Iteration Song Geo ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Time
open Next.Foundations UVNext.CouplingReset Cub Circlet Graces Roost Pressure
open AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonFundedWindowCompany
open scoped Topology BigOperators Classical


open AllOrder AllOrder.Floe AllOrder.Iron Push.Uniform
variable {G:Gauge} (hG:G.Simple) (A:ℕ→Stage) (rate:MapPrices) (K:KernelChoices)
  (ρ:ℕ→ℕ→ℝ) (shell:ℕ→ℝ) (hρ:∀k x,0<ρ k x) (hshell:∀k,0<shell k)

include hG hρ hshell in
private theorem leased : ∃ F:Roots (G:=G) A rate K, ∀k x i,
    F.pre k x i ≤ ρ k x/(16*shell k) := by
  let cap (k x : ℕ) (_ : Age) := min 1 (ρ k x/(16*shell k))
  have hp (k x : ℕ) (i : Age) : 0<cap k x i:=lt_min one_pos (div_pos (hρ k x) (mul_pos (by norm_num) (hshell k)))
  choose S paid using fun k=>PlanV.lease hG A rate (cap k) (arms A rate K G k) (k+2) (hp k) (fun x=>arms_p ..)
  let F:Roots (G:=G) A rate K:=⟨S,fun k=>⟨(paid k).pos,(paid k).crossing,(paid k).use,
    fun x i=>((paid k).top x i).trans (min_le_left ..)⟩⟩
  exact ⟨F,fun k x i=>((paid k).top x i).trans (min_le_right ..)⟩

def roots : Roots (G:=G) A rate K:=(leased hG A rate K ρ shell hρ hshell).choose

private theorem age_fee {a:ℝ} (h : 0≤a) (k : ℕ) : leaseF a k≤a := by
  unfold leaseF AllOrder.Ker.small_a Iron.breath Push.Uniform.weaker
  have hk : 0≤((k+3:ℕ):ℝ):=by positivity
  exact (div_le_self (by positivity) (by norm_num)).trans ((div_le_self (by positivity) (by push_cast at *; linarith only [hk])).trans
    (div_le_self h (by push_cast at *; linarith only [hk])))

private theorem leaves {D:Roots (G:=G) A rate K} (ψ:ℕ→ℕ) (k x:ℕ) (a:Age) (fee:a∈Step.tape (k+2)) :
    Poetry.Agenda.seed D ψ k x≤ D.pre k x a := by
  let τ:=Poetry.Agenda.stipend D k x
  have stock:= (Poetry.Agenda.receives D k x).choose_spec
  have hp:0<τ:=stock.1
  have edge : τ≤leaseF (D.pre k x a) (k+2) := stock.2.2 a fee
  have c₀ : 0≤Poetry.Agenda.poll D k x:=(AllOrder.Ink.Money.soprano _ hp _).le
  have c₁ : Poetry.Agenda.poll D k x≤τ:=AllOrder.Ink.Money.gestate _ hp (Nat.zero_le _)
  have size : 1≤(Poetry.Agenda.burden (k+4):ℝ):=by
    unfold Poetry.Agenda.burden
    exact_mod_cast (show 1≤(8*(k+4)+1)*((k+4+1)*2) by nlinarith)
  have w : Poetry.Agenda.waist D k x≤Poetry.Agenda.poll D k x:=
    div_le_self c₀ (one_le_pow₀ size)
  exact (div_le_self (le_min (Poetry.Agenda.belt_p D k x).le (Poetry.Agenda.belt_p D k (x+1)).le)
    (by exact_mod_cast (show 1≤ψ k+1 by omega))).trans ((min_le_left ..).trans (w.trans (c₁.trans
      (edge.trans (age_fee ((D.shape k).pos x a).le _)))))

include hρ hshell in
theorem narrow (ψ:ℕ→ℕ) (k x:ℕ) (working:1≤k) :
    Poetry.Agenda.seed (roots hG A rate K ρ shell hρ hshell) ψ k x ≤ ρ k x/(16*shell k) := by
  let a:Age:=⟨0,0,by omega⟩
  have seen : a∈Step.tape (k+2) := Age.in_scope.mpr (by change 0+3≤k+2;omega)
  exact (leaves A rate K ψ k x a seen).trans ((leased hG A rate K ρ shell hρ hshell).choose_spec k x a)

end YM.Integration.WilsonOlderFreshGraphStrip
end
