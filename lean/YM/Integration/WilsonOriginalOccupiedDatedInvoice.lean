import YM.Integration.WilsonOriginalOccupiedOptical
import YM.Integration.WilsonOriginalOccupiedDateShare
import YM.Integration.WilsonMeasuredProtectedSectionRate

/-! Signed optical withdrawal of the entire original Hκ bank with a summable allowance at the common earlier physical coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedDatedInvoice
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

open private YM.Integration.WilsonOriginalOccupiedRate.allowance from YM.Integration.WilsonOriginalOccupiedRate
include simple in
theorem original (n d a p:ℕ) (np:0<n) (load:∀s:marks.Mode,s.val.card ≤ n)
    (C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀ᶠ f:ℕ in atTop,∀ (N per m k b:ℕ) (_top:f+1 ≤ N) (bt:b ≤ f+1),start ≤ b → m ≤ b →
    ((f+1-b:ℕ):ℝ) ≤ C*(1+Real.log (H (f+1)))^d →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(X I:Type) [Countable I] [Nonempty X] (o:V → Site (R.family.side (f+1) per))
    (A:Gallery X I o (Ψ (f+1)) marks) (w:V → ℝ), (∀v,0<w v) →
    ∀ E B:ℝ, A.E.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent E →
    A.K.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent (B*κ (f+1)) →
    ∀(x:X)(s:marks.Mode)(W:Config G (R.family.side b per)),flags (Ψ b).p.threshold W=∅ →
    let gain:=(H (f+1))^a*Poly.toll w s/(WilsonOriginalOccupiedSalary.debit E B)^s.val.card
    let value:=‖(((Ψ b).eval W:ℂ)⁻¹)*((gust R.family.path N per (f+1) (A.density x) b bt W).part s-
      (gust R.family.path N per (f+1) (fun U=>((Ψ (f+1)).eval U:ℂ) • Poly.pass (A.E.log x U)) b bt W).part s)‖
    let budget:=(e*(regulatorRun R.family N per b)^p)*(shards marks s).card/WilsonOriginalOccupiedDateShare.weight (f+1-b)
    gain*value ≤ budget ∧ (1 ≤ gain → value ≤ budget):=by
  let v:=e/(2:ℝ)^p
  have vp:0<v:=div_pos ep (by positivity)
  obtain ⟨start,period⟩:=WilsonOriginalOccupiedOptical.original R simple marks n d (a+2*(d+1)) p np load C v cp vp
  have rise:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  have tiny:=(tendsto_add_atTop_nat 1).eventually (YM.Integration.WilsonOriginalOccupiedRate.allowance R simple 0 0 (e:=1/2) (by norm_num))
  refine ⟨start,?_⟩
  filter_upwards [period,tiny,rise.eventually_ge_atTop (C*2^d+2)] with
    f paid narrow clock N per m k b top bt sb mb span way D Q π Γ Ψ course ticket X I hc hx o A w wp E B re ha x s W clear
  let h:=H (f+1)
  let l:=f+1-b
  let r:=WilsonOriginalOccupiedSalary.debit E B
  let wr:=Stoop.radius w r
  let g:=regulatorRun R.family N per (f+1)
  let gb:=regulatorRun R.family N per b
  let val:=‖(((Ψ b).eval W:ℂ)⁻¹)*((gust R.family.path N per (f+1) (A.density x) b bt W).part s-
    (gust R.family.path N per (f+1) (fun U=>((Ψ (f+1)).eval U:ℂ) • Poly.pass (A.E.log x U)) b bt W).part s)‖
  let num:ℝ:=(shards marks s).card
  let cut:=WilsonOriginalOccupiedDateShare.weight l
  have incl:0<cut:=by dsimp [cut,WilsonOriginalOccupiedDateShare.weight];positivity
  have h1:1 ≤ h:=(R.family.path.levels.fits.delayed _).le
  have h0:0 ≤ h:=zero_le_one.trans h1
  have r1:1 ≤ r:=le_max_left ..;have rp:0<r:=zero_lt_one.trans_le r1
  have shallow:κ (f+1) ≤ 1/2:=by simpa using narrow N per top
  obtain ⟨wrp,reg,forced,restore⟩:=WilsonOriginalOccupiedSalary.original R π Γ Ψ course (mb.trans bt) top A w wp E B shallow re ha
  have price:=(paid N per m k b top bt sb mb span way D Q π Γ Ψ course ticket X I o A wr wrp reg forced x s W clear).1
  change (h^(a+2*(d+1))*Poly.toll wr s)*val ≤ v*g^p*num at price
  have lower:g ≤ 2*gb:=WilsonMeasuredProtectedSectionRate.band R simple bt top
  have senior:v*g^p ≤ e*gb^p:=by
    calc _ ≤ v*(2*gb)^p:=mul_le_mul_of_nonneg_left
           (pow_le_pow_left₀ (ActualRunKernelPackets.regulator_pos R N per (f+1) top).le lower _) vp.le
         _ = _:=by dsimp [v];rw [mul_pow];field_simp
  have cap:cut ≤ h^(2*(d+1)):=WilsonOriginalOccupiedDateShare.hot d l h1 cp clock span
  have val0:0 ≤ val:=norm_nonneg _
  have wage:0 ≤ Poly.toll wr s:=(Poly.worth wrp s).le
  have fix:h^a*Poly.toll w s/r^s.val.card=h^a*Poly.toll wr s:=by
    rw [restore s];change h^a*(r^s.val.card*Poly.toll wr s)/r^s.val.card=h^a*Poly.toll wr s;field_simp
  have fee:(h^a*Poly.toll wr s)*val ≤ e*gb^p*num/cut:=by
    apply (le_div_iff₀ incl).2
    calc _=(h^a*Poly.toll wr s*val)*cut:=rfl
         _ ≤ (h^a*Poly.toll wr s*val)*h^(2*(d+1)):=mul_le_mul_of_nonneg_left cap
           (mul_nonneg (mul_nonneg (pow_nonneg h0 _) wage) val0)
         _ = (h^(a+2*(d+1))*Poly.toll wr s)*val:=by rw [pow_add];ring
         _ ≤ _:=price.trans (mul_le_mul_of_nonneg_right senior (Nat.cast_nonneg _))
  change h^a*Poly.toll w s/r^s.val.card*val ≤ _ ∧ (1 ≤ h^a*Poly.toll w s/r^s.val.card → _)
  rw [fix];exact ⟨fee,fun enough=>(le_mul_of_one_le_left val0 enough).trans fee⟩

end YM.Integration.WilsonOriginalOccupiedDatedInvoice
