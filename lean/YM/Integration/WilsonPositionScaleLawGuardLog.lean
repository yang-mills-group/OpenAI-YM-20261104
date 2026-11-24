import YM.Integration.WilsonPositionScaleLawGuardGrowth
import YM.Integration.WilsonPositionScaleLawGuardBarrier

/-! Dyadic iteration on the full genuine homogeneous frame with its measured beta coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardLog
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawGuardOrbit (size charge)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field
local notation "gθ"=>kinetic Z F J
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawWholeGrowth (weight)
open WilsonPositionScaleLawGuardOrbit (sizePos)
variable (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:WilsonPositionScaleLawGuardLittle.scale F J Z M ν d 2)(r:ℝ)(hr:0<r)

include H funded law hr in
theorem budgets:∃A:ℝ,0≤A ∧ ∀ᶠn:ℕ in atTop,∀t:Ratio,∀O:S.Field d,
    size R.family (physical F J Z d (t.val*radius r n) O)≤(1+A/((n:ℝ)+1))*size R.family (physical F J Z d (radius r n) O):=by
  obtain ⟨K,hK,rates⟩:=WilsonPositionScaleLawGuardGrowth.original Z M H ν F J d funded law
  let c:ℝ:=(2*Trace.Over.b0 G*Real.log 2)⁻¹
  let cap:=|c|+1
  have hc:0≤cap:=by dsimp only [cap];positivity
  have up:c<cap:=lt_of_le_of_lt (le_abs_self _) (lt_add_one _)
  have paid:∀ᶠn:ℕ in atTop,((n:ℝ)+1)*(gθ (radius r n))^2<cap:=(tendsto_order.mp (WilsonPositionScaleLawClock.rate funded r hr)).2 _ up
  refine ⟨K*cap,mul_nonneg hK hc,?_⟩
  filter_upwards [paid,(WilsonPositionScaleLawClock.falls r hr).eventually rates] with n h raw t O
  have growing:(gθ (radius r n))^2≤cap/((n:ℝ)+1):=(le_div_iff₀ (by positivity)).mpr ((mul_comm _ _).trans_le h.le)
  have fee:K*(gθ (radius r n))^2≤K*cap/((n:ℝ)+1):=(mul_le_mul_of_nonneg_left growing hK).trans_eq (mul_div_assoc ..).symm
  exact (raw t O).trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) fee) (sizePos R.family _))

include H funded law hr in
theorem dyadic:∃K p:ℕ,∀n,K≤n→∀O:S.Field d,
    size R.family (physical F J Z d (radius r n) O)≤weight p n*size R.family (physical F J Z d (radius r K) O):=by
  obtain ⟨A,hA,date⟩:=budgets Z M H ν F J d funded law r hr
  apply WilsonPositionScaleLawGuardBarrier.original (fun n O=>size R.family (physical F J Z d (radius r n) O)) hA (fun _ _=>sizePos R.family _)
  filter_upwards [date] with n paid O
  have price:=paid WilsonPositionScaleLawGrade.half O
  rw [WilsonPositionScaleLawWholeGrowth.next] at price
  exact price

def Controlled:Prop:=∃p:ℕ,∃ρ:ℝ,0<ρ ∧ ∀O:S.Field d,∃B:ℝ,0≤B ∧ ∀u:ℝ,0<u→u≤ρ→
    size R.family (physical F J Z d u O)≤B*(1+Real.log (r/u)/Real.log 2)^p

include H funded law hr in
theorem original:Controlled Z F J d r:=by
  obtain ⟨N,p,all⟩:=dyadic Z M H ν F J d funded law r hr
  obtain ⟨A,hA,later⟩:=budgets Z M H ν F J d funded law r hr
  obtain ⟨M0,date⟩:=eventually_atTop.mp later
  let K:=max N M0
  refine ⟨p,radius r K,show 0<r*(1/2:ℝ)^K by positivity,?_⟩
  intro O
  let v:=size R.family (physical F J Z d (radius r N) O)
  have v0:0≤v:=sizePos R.family _
  refine ⟨(1+A)*v,mul_nonneg (by linarith) v0,?_⟩
  intro u hu small
  obtain ⟨n,hn,t,link,days⟩:=WilsonPositionScaleLawContinuum.band r hr K u hu small
  have step:=date n ((le_max_right N M0).trans hn) t O
  rw [link] at step
  have price:1+A/((n:ℝ)+1)≤1+A:=add_le_add (le_refl 1) (div_le_self hA (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have head:=all n ((le_max_left N M0).trans hn) O
  have age:weight p n≤(1+Real.log (r/u)/Real.log 2)^p:=by
    change ((n:ℝ)+1)^p≤_
    exact pow_le_pow_left₀ (by positivity) (by linarith only [days]) p
  calc
    _≤(1+A/((n:ℝ)+1))*size R.family (physical F J Z d (radius r n) O):=step
    _≤(1+A)*(weight p n*v):=mul_le_mul price head (sizePos R.family _) (by linarith)
    _=((1+A)*v)*weight p n:=by ring
    _≤_:=mul_le_mul_of_nonneg_left age (mul_nonneg (by linarith) v0)

end YM.Integration.WilsonPositionScaleLawGuardLog
