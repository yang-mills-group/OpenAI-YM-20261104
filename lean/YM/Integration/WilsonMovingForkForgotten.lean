import YM.Integration.WilsonMovingForkAbsoluteHousing
import YM.Integration.WilsonOriginalTwoFlatPublicHeard

set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMovingForkForgotten
open Function Filter Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal
open Push.Local Push.AbsoluteSums Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Classical BigOperators Topology

open MeasureTheory MergeProof Ribbons Accent OPE Bid WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatTelescope (entrance interval)
open WilsonOriginalTwoFlatGridScaling (gap)
variable {G:Gauge}(R:Run G){N per c u v K:ℕ}
local notation "C" => R.family
local notation "rep" => (C).path.rep N per c
local notation "Sec" => (C).localSection 0
local notation "μ" => price G (max (rep).p.order (rep).p.power)
local notation "κ" => LocalComparison.forcedDivisor C c
local notation "v₀" => R.alloy.B.a.clock.forcedAllowance c
local notation "Q" j:max => Config G ((C).side j per)

open WilsonOriginalTwoFlatPublicStops (debt)

/-- The true compensated terminal factor in the original optical units. -/
theorem transmission (P D:ℕ){g Λ A:ℝ}(gp:0≤g)
    (reach:(C).S.a c/(C).S.a v≤(g^(4*(P+D)))^2)(pay:|A| *g^D≤Λ):
    A*Real.exp (-((C).S.scale c-(C).S.scale v)/8)≤Λ*g^P:=by
  have dated (j:ℕ):Real.exp (-(C).S.scale j)=(C).S.a j:=by
    simp [Schedule.scale,Real.log_inv,Real.exp_log ((C).S.a_pos _)]
  have eighth:(Real.exp (-((C).S.scale c-(C).S.scale v)/8))^8=(C).S.a c/(C).S.a v:=by
    rw [← Real.exp_nat_mul,←dated c,←dated v,←Real.exp_sub]
    congr 1
    push_cast
    ring
  have gain:Real.exp (-((C).S.scale c-(C).S.scale v)/8)≤g^(P+D):=by
    apply le_of_pow_le_pow_left₀ (n:=8) (by decide) (pow_nonneg gp _)
    rw [eighth]
    apply reach.trans_eq
    rw [←pow_mul,←pow_mul]
    congr 1
    omega
  calc
    _≤|A| *Real.exp (-((C).S.scale c-(C).S.scale v)/8):=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _≤|A| *g^(P+D):=mul_le_mul_of_nonneg_left gain (abs_nonneg _)
    _=(|A| *g^D)*g^P:=by rw [pow_add];ring
    _≤_:=mul_le_mul_of_nonneg_right pay (pow_nonneg gp _)

set_option linter.unusedVariables false in
theorem original (simple:G.Simple)(N per u:ℕ)(Y:Cut C N per)(A:ℝ)
    (heard:WilsonOriginalTwoFlatPublicHeard.Heard R simple N per u Y A):
  ∀{v c K:ℕ} (uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)(kn:K ≤ N)(cN:c<N)
    (ou:Opened C 0 u per)(ov:Opened C 0 v per)(ready:WilsonCenteredCaptureClock.first R simple ≤ c)
    (M:∀i:ℕ,(Config G ((C).side i per))→ℂ)(paid:∀i,c  ≤  i → i  ≤  K → Integrable (numerator R N per i (M i)) (prior G _))
    {V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    {o:V→Site ((C).side c per)}{p:BudgetPoint}(L:Lamps X ι G p o J)(same:((C).path.rep N per c).p=p)
    (x:X)(s:J.Mode)(Z:Support ((C).side c per))(center:0∈Z)(reside:∀a∈s.val,o a∈Z)
    (rad:ℕ)(near:∀a∈s.val,separation (o a) 0  ≤  rad)(w:V→ℝ)(wp:∀a,0<w a)
    {derivative gross:ℝ}(he:L.Paid w p.B (p.supportExponent+2) derivative)
    (hg:Gross L w p.B (p.supportExponent+2) gross)
    (placed:M c=fun U=>(Poly.pass (bare L x U)).part s),
    let fee:=WilsonPlantedOrdinary.fare ((C).path.rep N per c).p Z w derivative gross rad (Sec) (C).params (price G (max ((C).path.rep N per c).p.order ((C).path.rep N per c).p.power)) (R.alloy.B.a.clock.forcedAllowance c) (LocalComparison.forcedDivisor C c) s
    ∀(P D:ℕ){g Λ:ℝ},0≤g →
      (C).S.a c/(C).S.a v≤(g^(4*(P+D)))^2 → |2*capital C c fee 1| *g^D≤Λ →
      ‖gap R N per v ((vc.trans ck).trans kn) Y‖≤A+debt R Y ((uv.trans vc).trans ck) kn M c+
        Λ*g^P+debt R Y (vc.trans ck) kn M c:=by
  intro v c K uv vc ck kn cN ou ov ready M paid V X ι _ _ _ J o p L same x s Z center
    reside rad near w wp derivative gross he hg placed fee P D g Λ gp reach pay
  have measured:=heard uv vc ck kn cN ou ov ready M paid L same x s Z center reside rad near w wp he hg placed
  exact measured.trans (add_le_add (add_le_add (le_refl _) (transmission R P D gp reach pay)) (le_refl _))

end YM.Integration.WilsonMovingForkForgotten
end
