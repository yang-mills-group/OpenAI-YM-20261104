import YM.Integration.WilsonInvariantActionMixedMaterial
import YM.Integration.WilsonMatrixTicketLanesRegulatorReturn
import YM.Integration.WilsonRegisteredLogFare

/-! The allowance for a complete previously deposited physical regular field
is absorbed by a finite increase in the independent conditional degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPreviousQTariff
open Filter Function Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open OPE Table SharpGram.Lenses Pier.Lair OPE.Orbits Trace.Pilot PhysicalNext.Repeat.Legato
open PertExtension Pert.Asymptotics RG16 Overlay WilsonInvariantActionMixedMaterial
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedPrepaid
open WilsonMatrixTicketLanesRegulatorCoupon
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels

theorem funds (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (q e:ℕ) {C ε:ℝ} (good:0≤1+C) (hp:0<ε):
    let K:=q+2*(e+1)+1
    ∀ᶠ m:ℕ in atTop,∀N p, m+1≤N→∀(v:R.family.label 4)(M:ℝ),0≤M→
      (R.family.S.a (m+1)^4)⁻¹*Next.UVStress.quota R.family 4 (m+1) N p v≤
        (A).clock.hatBeta (m+1)^e*M→
      2*budget v (m+1) N p*(2*(1+C)*(regulatorRun R.family N p (m+1))^K)≤
        ε*(regulatorRun R.family N p (m+1))^q*M:=by
  intro K
  have late:∀ᶠm:ℕ in atTop,∀b N p,b≤ m+1→m+1≤N→
    (8*(1+C))*(A).clock.hatBeta (m+1)^e*((regulatorRun R.family N p (m+1))^K*
      (2+Real.log ((A).clock.hatBeta b)))≤ε*(regulatorRun R.family N p (m+1))^q:=
    (tendsto_add_atTop_nat 1).eventually
      (WilsonMatrixTicketLanesReportedAccuracy.coupon R simple q e (8*(1+C)) ε (by positivity) hp)
  filter_upwards [late,WilsonRegisteredLogFare.column R simple slow] with m purchased columns N p live v M mp actual
  let B:=(A).clock.hatBeta (m+1)
  let g:=regulatorRun R.family N p (m+1)
  have bp:0≤B:=zero_le_one.trans ((A).fits.delayed (m+1)).le
  have gp:0≤g:=(inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))).le
  have cp:0≤((A).params (m+1)).columns:=zero_le_one.trans ((A).params (m+1)).columns_ge
  have sell:=purchased (m+1) N p le_rfl live
  change 8*(1+C)*B^e*(g^K*(2+Real.log B))≤ε*g^q at sell
  have cols:((A).params (m+1)).columns≤2*(2+Real.log B):=by
    change ((A).params (m+1)).columns≤2*Real.log B at columns
    linarith only [columns]
  change 2*(((A).params (m+1)).columns*_)*(2*(1+C)*g^K)≤ε*g^q*M
  change _≤B^e*M at actual
  calc
    _≤2*(2*(2+Real.log B)*(B^e*M))*(2*(1+C)*g^K):=by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left actual cp).trans
        (mul_le_mul_of_nonneg_right cols (mul_nonneg (pow_nonneg bp _) mp))) (by norm_num)
    _=(8*(1+C)*B^e*(g^K*(2+Real.log B)))*M:=by ring
    _≤_:=mul_le_mul_of_nonneg_right sell mp

variable {f:Extraction.Order} {S:Table R.family.book} (F:Spec.Final R.family f S) (L:Layout F)
    (E:Services R.family f S)

include E in
theorem reported (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (q h H:ℕ) {C ε:ℝ} (good:0≤1+C) (hp:0<ε):
    let K:=q+2*(h+H*(4+1)+1)+1
    ∀ᶠm:ℕ in atTop,∀r N p, L.level r≤ m+1→m+1≤N→R.family.ref 4 ≤ L.level r→
      R.family.S.a (L.level r)/R.family.S.a (m+1)≤(A).clock.hatBeta (m+1)^H→
      ∀(w:R.family.label 4) (M:ℝ),0≤M→
      mass R.family 4 (L.shift 4 r w)≤(A).clock.hatBeta (L.level r)^h*M→
      2*budget (atRef L 4 r (N,p) w) (m+1) N p*(2*(1+C)*regulatorRun R.family N p (m+1)^K)≤
        ε*regulatorRun R.family N p (m+1)^q*M:=by
  intro K
  filter_upwards [funds R simple slow q (h+H*(4+1)) good hp] with m cash r N p later live age room w M mp shift
  exact cash N p live _ M mp (WilsonMatrixTicketLanesRegulatorReturn.charge R F L E simple 4 h H r w M
    mp shift (m+1) N p age later live room)

end YM.Integration.WilsonInvariantActionPreviousQTariff
