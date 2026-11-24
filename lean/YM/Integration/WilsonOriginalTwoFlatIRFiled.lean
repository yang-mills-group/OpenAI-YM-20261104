import YM.Integration.WilsonOriginalTwoFlatIRHalo
import YM.Integration.WilsonOriginalTwoFlatIRClock
import YM.Integration.WilsonOriginalTwoFlatCompact

/-! The full captured ordinary table of the submitted lamps is filed on the
actual original vacuum. Its capital includes the original wallet once on
each occupied name and an explicit fixed engineering power. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFiled
open Function Filter Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal
open Push.Local Push.AbsoluteSums Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open WilsonOriginalTwoFlatIRHalo (roof power)
open Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "T" => R.family.path.levels
local notation "Sec" => R.family.localSection 0
local notation "Y" => R.family.params

def reserve (roof housing:ℝ):ℝ:=40*(2*(roof*housing)+1)

set_option linter.unusedVariables false in
theorem original (simple:G.Simple)
    (slow:∀m, ((C).S.block m).val ≤ Real.log (Lambda (T) m))
    (ready:WilsonReportLampForecast.Ready (T)):
    ∀ᶠ c:ℕ in atTop,∀N per:ℕ,∀hc:c<N,
    let rep:=(C).path.rep N per c
    let κ:=LocalComparison.forcedDivisor C c
    let η:=R.alloy.B.a.clock.forcedAllowance c
    let μ:=((T).params c).columns
    let x:=3*(regulatorRun C N per c)⁻¹
    ∀{V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    {o:V→Site ((C).side c per)}{p:BudgetPoint}(L:Lamps X ι G p o J)(same:rep.p=p)
    (s:J.Mode)(Z:Support ((C).side c per))(center:0∈Z)(reside:∀a∈s.val,o a∈Z)
    (rad:ℕ)(near:∀a∈s.val,separation (o a) 0≤rad)(inside:rad≤rep.p.B)
    (housed:Z⊆halo rep.p.B {0}){α:ℝ}(strip:rep.p.supportExponent≤α)
    (w:V→ℝ)(wp:∀v,0<w v)(D E:ℕ){K C₀ C₁ H:ℝ}(one:1≤K)(wh:0≤H)
    (wage:(Poly.toll w s)⁻¹≤H*x^E)(h₀:0≤C₀)(h₁:0≤C₁)
    (cost₀:C₀≤K*x^D)(cost₁:C₁≤K*x^D)
    (he:L.Paid w p.B (p.supportExponent+2) C₀)(hg:Gross L w p.B (p.supportExponent+2) C₁),
    let rem:=WilsonPlantedOrdinary.fare rep.p Z w C₀ C₁ rad (Sec) (Y) μ η κ s
    (∀t:X,WilsonCenteredFiledAtoms.Store rep (Sec) (Y) 0 κ rem
      (fun U=>(rep.eval U:ℂ)*(Poly.pass (bare L t U)).part s)) ∧
    2*capital C c rem 1≤reserve (roof J s (Sec) (Y) α K) H*x^(power s.val.card D+E+2):=by
  filter_upwards [WilsonCenteredReporterClock.original R simple slow ready,WilsonOriginalTwoFlatIRClock.adjacent R simple,
    eventually_ge_atTop (R.t 0)] with c opened neighbor commissioned N per hc
  intro rep κ η μ x V X ι _ _ _ J o p L same s Z center reside rad near inside housed α strip
    w wp D E K C₀ C₁ H one wh wage h₀ h₁ cost₀ cost₁ he hg rem
  have actual:=R.makes.wilson.represents N per c hc.le
  have fit:rep.p=(T).budget c:=actual.vac
  have read:Readable (Y) (Sec) rep.p ((C).side c per) μ:=
    (WilsonCapturedPrimarySection.original R commissioned rep fit).1
  obtain ⟨gx,_,motion,col,live,_,positive,enough,divided⟩:=opened N per hc
  have pair:=neighbor N per hc
  have xx:1≤x:=gx.trans pair
  have φ:(regulatorRun C N per (c+1))⁻¹≤x:=pair
  have pm:WilsonReportRetainedAnchor.reprice rep.p rep.p.B≤2*x^2:=by
    rw [fit];exact motion.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans gx) φ _) zero_le_two)
  have cols:μ≤4*x^2:=col.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans gx) φ _) (by norm_num))
  have co:0≤μ:=zero_le_one.trans ((T).params c).columns_ge
  have wallet:=WilsonOriginalTwoFlatIRHalo.original rep.p (Sec) (Y) Z 0 w wp s rad D
    xx inside housed strip live positive (fit ▸ divided) pm co cols one h₀ h₁ cost₀ cost₁
  constructor
  · intro t
    exact WilsonPlantedOrdinary.transferred (P:=rep) L same t s 0 Z center reside rad near w wp he hg
      (OriginalForcedAddresses.actual_keeper R simple N c per hc.le) actual.good live positive (fit ▸ enough) (Sec) (Y) read
  · let T₀:=roof J s (Sec) (Y) α K
    let n:=power s.val.card D
    have Tpos:0≤T₀:=by dsimp [T₀,roof,WilsonOriginalTwoFlatIRHalo.factor₀];positivity
    have xp:=zero_le_one.trans xx
    have cheap:rem≤(T₀*x^n)*(Poly.toll w s)⁻¹:=by
      rw [←div_eq_mul_inv];apply (le_div_iff₀ (Poly.worth wp s)).mpr
      exact (mul_comm ..).trans_le wallet
    have rempay:rem≤(T₀*H)*x^(n+E):=cheap.trans
      ((mul_le_mul_of_nonneg_left wage (mul_nonneg Tpos (pow_nonneg xp _))).trans_eq (by rw [pow_add];ring))
    have xc:1≤x^2:=one_le_pow₀ xx
    have xm:1≤x^(n+E):=one_le_pow₀ xx
    have side:1+μ≤5*x^2:=by linarith
    have house:2*rem+1≤(2*(T₀*H)+1)*x^(n+E):=by linarith
    change 2*(4*(1+μ)*(2*rem+1))≤_
    calc _=8*(1+μ)*(2*rem+1):=by ring
         _≤8*(1+μ)*((2*(T₀*H)+1)*x^(n+E)):=mul_le_mul_of_nonneg_left house (by positivity)
         _≤8*(5*x^2)*((2*(T₀*H)+1)*x^(n+E)):=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left side (by norm_num)) (by positivity)
         _= _:=by change _=reserve T₀ H*x^(n+E+2);rw [pow_add (x) (n+E) 2];unfold reserve;ring

end YM.Integration.WilsonOriginalTwoFlatIRFiled
