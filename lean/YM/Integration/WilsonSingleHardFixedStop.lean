import YM.Integration.WilsonSingleHardStops

/-! One fixed early filing is sufficient for every accuracy. The only small
factor in the numerical bound is the original compulsory allowance at birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSingleHardRadius
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple)

def first : ℕ := start R simple 0 (by norm_num : 0<(1:ℝ))

theorem half {j:ℕ} (ready:first R simple ≤ j) : LocalComparison.forcedDivisor R.family j ≤ 1/2 :=
  (cash R simple 0 (by norm_num : 0<(1:ℝ)) ready).1

variable {N per m k b:ℕ} (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q)
   (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
   (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   {T:Type} [Nonempty T] {J:Census (Fin 1)} (o:Fin 1→Site (R.family.side b per))
   (K:Hard T (Ψ b).p (Ψ b).activities.forced (Ψ b).activities.K o J)
local notation "β" j:max => R.alloy.B.a.clock.hatBeta j
local notation "vac" j:max U:max => (R.family.path.rep N per j).eval U
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j
local notation "head" t:max => (fun U=>((gallery K).density t U).part (J.fire 0))
local notation "profile" t:max => (fun U=>(vac b U)⁻¹ • ((head t) U))

include way ticket course in
theorem retained (top:b ≤ N) {u:ℕ} (floor:m ≤ u) (ub:u ≤ b) (enrolled:first R simple ≤ u)
    {w:ℝ} (wp:0<w) (bill:K.Paid (fun _=>w) (Ψ b).p.B (Ψ b).p.supportExponent (κ b))
    {i:ℕ} (ui:u ≤ i) (ib:i ≤ b) (t:T) :
    ‖actualTransport R.family (N:=N) (profile t) ib 1‖ ≤ 2*(β b)*(κ b)/w := by
  have dp:0<κ b:=Real.sqrt_pos.2 (Real.exp_pos _)
  have cap:κ b ≤ 1:=(half R simple (enrolled.trans ub)).trans (by norm_num)
  have realBill:=raised K bill wp dp cap
  have offer (j:ℕ) (uj:u ≤ j) (jb:j<b) :
      Time.quoteHard R.alloy.B.a j R.kit.book (Ψ (j+1)).beta ≤ 1/2 := by
    have funded:=Advent.force_bill R way π Γ Ψ course (floor.trans uj) (jb.trans_le top)
      (q:=0) (Nat.zero_le _)
    have quiet : Time.quoteHard R.alloy.B.a j R.kit.book (Ψ (j+1)).beta ≤ κ j := by simpa using funded
    exact quiet.trans (half R simple (enrolled.trans uj))
  obtain ⟨w',Z,wp',_,invoice⟩:=descent R way D Q ticket π Γ Ψ course o K (div_pos wp dp)
    realBill top (floor.trans ub) simple u floor offer ib ui
  have cost:=invoice t (1:Config G _)
  simp only [flat Z t,smul_zero,sub_zero] at cost
  have raw : (fun U=>(vac b U) • ((profile t) U))=(head t) := by
    funext U
    have pos : (vac b U)≠0 := (Multi.AxisShift.chosen_positive R.makes.wilson top U).ne'
    rw [smul_smul,mul_inv_cancel₀ pos,one_smul]
  rw [actualTransport,raw]
  have bp : 0 ≤ β b:=((R.alloy.B.a.fits.delayed b).trans' (by norm_num : (0:ℝ)<1)).le
  have good : 0 ≤ 2*(β b)/w' := by positivity
  have final:2*(β b)/(w/(κ b))=2*(β b)*(κ b)/w:=by simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
  rw [←final]
  linarith only [cost,good]

end YM.Integration.WilsonSingleHardRadius
