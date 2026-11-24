import YM.Integration.WilsonOriginalOccupiedReentry

/-! The original quiet allowance, all incoming ordinary rows and complete hard bank on one physical post. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedSalary
open Function Finset Lattice Wilson RG Source Marker QuadraticLocal Ac
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per m k t:ℕ} {V:Type} [DecidableEq V] {J:Marker.Census V}
variable (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {X I:Type} {o:V → Site (R.family.side t per)}
local notation "κ" => LocalComparison.forcedDivisor R.family t

def debit (E H:ℝ):ℝ:=max 1 (max E (2*H))

include course in
theorem original (mt:m ≤ t)(top:t ≤ N)(A:Gallery X I o (Ψ t) J)(w:V → ℝ)(wp:∀v,0<w v)
    (E H:ℝ)(small:κ ≤ 1/2)(earned:A.E.Paid w (Ψ t).p.B (Ψ t).p.supportExponent E)
    (old:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (H*κ)):
    let r:=debit E H
    let v:=Stoop.radius w r
    (∀j,0<v j) ∧ A.E.Paid v (Ψ t).p.B (Ψ t).p.supportExponent 1 ∧
    A.K.Paid v (Ψ t).p.B (Ψ t).p.supportExponent κ ∧
    (∀s:J.Mode, Poly.toll w s=r^s.val.card*Poly.toll v s):=by
  let r:=debit E H
  have rp:1 ≤ r:=le_max_left ..;have rpos:0<r:=zero_lt_one.trans_le rp
  have qh:2*H ≤ r:=(le_max_right ..).trans (le_max_right ..)
  have re:E ≤ r:=(le_max_left ..).trans (le_max_right ..)
  have born:= (course.1.walk t mt top).truep.valid.labels
  have rent:Hard.Rent (Ψ t).activities.forced (Ψ t).activities.K (Ψ t).p (Ψ t).p.supportExponent (κ^2):=by
    rw [show κ^2=R.family.path.levels.clock.forcedAllowance t from Real.sq_sqrt (Real.exp_pos _).le]
    exact Hard.rentValid born.forced born.boundK
  have hr:=WilsonOriginalOccupiedReentry.original A.K w wp r κ H rp qh (Real.sqrt_nonneg _) small rent old
  have hw:r⁻¹*E ≤ 1:=(inv_mul_le_one₀ rpos).2 re
  have soft:=Lamps.loan_monotone _ (Stoop.tighten w A.E wp rp earned) hw
  refine ⟨fun j=>div_pos (wp j) rpos,soft,hr,?_⟩
  intro s
  change (∏i∈s.val,w i)=r^s.val.card*∏i∈s.val,(w i/r)
  rw [prod_div_distrib];simp only [prod_const];field_simp

end YM.Integration.WilsonOriginalOccupiedSalary
