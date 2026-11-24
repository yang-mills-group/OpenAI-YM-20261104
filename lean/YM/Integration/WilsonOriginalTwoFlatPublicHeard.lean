import YM.Integration.WilsonOriginalTwoFlatPublicStops
/-! Join the issued reflected phase comparison to both older flat reports
of the same actual public numerator. The independent compact is freshly
submitted with its native regular and global wages on the original quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicHeard
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

set_option linter.unusedVariables false in
/-- The fixed physical sample and the moving flat sample of its same Wilson
numerator, with both complete dated ordinary bills taken on that Wilson law. -/
def Heard (simple:G.Simple)(N per u:ℕ)(Y:Cut C N per)(A:ℝ):Prop:=
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
    ‖gap R N per v ((vc.trans ck).trans kn) Y‖   ≤   A+debt R Y ((uv.trans vc).trans ck) kn M c+
      2*capital C c fee 1*Real.exp (-((C).S.scale c-(C).S.scale v)/8)+debt R Y (vc.trans ck) kn M c

theorem earned (simple:G.Simple){u:ℕ}(uN:u ≤ N)(Y:Cut C N per)(hc:Continuous Y){A:ℝ}
    (funded:‖gap R N per u uN Y‖  ≤  A):Heard R simple N per u Y A:=by
  intro v c K uv vc ck kn cN ou ov ready M paid V X ι _ _ _ J o p L same x s Z center
    reside rad near w wp derivative gross he hg placed
  exact WilsonOriginalTwoFlatPublicStops.actual R simple uv vc ck kn cN ou ov ready Y hc A funded M paid
    L same x s Z center reside rad near w wp he hg placed

end YM.Integration.WilsonOriginalTwoFlatPublicHeard
end
