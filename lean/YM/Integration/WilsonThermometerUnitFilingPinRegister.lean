import YM.Integration.WilsonThermometerUnitFilingPinSum
import YM.Integration.WilsonThermometerUnitFilingPinBalance

/-! All finite subrosters on one original inversion board, with independently nominated subsets at each pin. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinRegister
open Function Filter Wilson RG Lattice RegulatorIR Spatial Taping Budget Budget.Packet
open Diagram Prim Profiles Halo Ledger Ledger.Sky Oracle Uniform Cluster
open WilsonThermometerUnitFilingCoverRegister
open WilsonThermometerUnitFilingPinBalance
open WilsonThermometerUnitFilingCoverCurrency (gross)
open scoped Classical BigOperators ENNReal Topology

variable {G:Gauge}{W:Type}{steps:W→ℕ}{sides:Page steps→Side}(Z:Circuit steps sides)
  {K:KernelChoices}(scheme:Program K)(branches:∀ P:Patch,P.Branches K G)(units:Page steps→Binding.Scale)
local notation "L" => Z.dialect scheme G branches units
variable (T:Ledger.Sky.Accounts (Z.dialect scheme G branches units))
  {m:Uniform.Meter W}{p b h:ℕ}(P:Ledger.Sky.Primitive (Z.dialect scheme G branches units) m p b)
  (k:Choice steps)(S:W→Submission G)(paid:∀v,(S v).grades ()+1=h)(center:W→Room)
local notation "vac" => k.after.part (L) T P
local notation "z" => pin Z scheme branches units k center

abbrev Portions (S:W→Submission G):=∀ v,Finset (S v).I
def only (s:Portions S)(v:W):Submission G:={ S v with part:=s v }

def part (s:Portions S):(vac).Report h:=
  WilsonThermometerUnitFilingCoverEra.filed (L) T P k
    (shifted Z scheme branches units k (only S s) center)
    (checked Z scheme branches units k (only S s) paid center)

def full:(vac).Report h:=WilsonThermometerUnitFilingPinSum.total (vac) S paid (z)

theorem enrolled (s:Portions S)(v:W):BasisT h h
    (convey ((z) v) (WilsonThermometerUnitFilingCoverAudition.bank (S v).rows (s v) (S v).test (S v).read))
    ((part Z scheme branches units T P k S paid center s).main (Page.opening k.after.spans v)):=
  (WilsonThermometerUnitFilingCoverEra.origin (L) T P k
    (shifted Z scheme branches units k (only S s) center)
    (checked Z scheme branches units k (only S s) paid center) v).1

theorem entry (v:W):Tendsto (fun s=>(part Z scheme branches units T P k S paid center s).point
      (Page.opening k.after.spans v)) atTop
      (𝓝 ((full Z scheme branches units T P k S paid center).point (Page.opening k.after.spans v))):=by
  let leave (s:Finset (S v).I):Portions S:=Function.update (fun _=>∅) v s
  have atV (s:Finset (S v).I):leave s v=s:=Function.update_self ..
  let film:=part Z scheme branches units T P k S paid center
  have elected (s:Finset (S v).I):BasisT h h
      (convey ((z) v) (WilsonThermometerUnitFilingCoverAudition.bank (S v).rows s (S v).test (S v).read))
      ((film (leave s)).main (Page.opening k.after.spans v)):=by
    have actual:=enrolled Z scheme branches units T P k S paid center (leave s) v
    rw [atV] at actual;exact actual
  have hear:=WilsonThermometerUnitFilingPinSum.original (vac) S paid (z) v (fun s=>film (leave s)) elected
  have eval:Tendsto (fun s:Portions S=>s v) atTop atTop:=by
    apply tendsto_atTop.mpr;intro a
    filter_upwards [eventually_ge_atTop (leave a)] with s hs
    exact (atV a) ▸ hs v
  have agrees (s:Portions S): (film (leave (s v))).point (Page.opening k.after.spans v)=
      (film s).point (Page.opening k.after.spans v):=by
    have co:=enrolled Z scheme branches units T P k S paid center s v
    have cover:=certifies (elected (s v)) co ((film (leave (s v))).ceilingM v) ((film s).ceilingM v)
    funext e r;rw [(film (leave (s v))).same,(film s).same,cover]
  exact (hear.comp eval).congr (fun s=>agrees s)

theorem quoted (meter:Uniform.Meter W)(β g cash:W→ℝ)(late:∀v,Real.exp 1 ≤ β v)
    (width:∀v,Real.exp ((S v).σ⁻¹^2) ≤ β v)
    (gp:∀v,0<g v)(cp:∀v,0 ≤ cash v)(heat:∀v,β v*(g v)^2 ≤ 2)
    (d:ℕ)(income:∀v,(S v).cost/((S v).rad ()) ≤ (1+cash v)/(g v)^d)
    (accuracy e r u:ℕ)(wanted:e ≤ accuracy)(select:W→Portions S):
    Claim meter (fun v=>(L).coverQ center u (k.choose v))
      (fun v=>ENNReal.ofReal (2*gross G h u accuracy*(1+cash v)/(g v)^(d+2)) * (2:ℝ≥0∞)^u)
      (fun v=>(part Z scheme branches units T P k S paid center (select v)).main
        (Page.opening k.after.spans v) e r):=
  WilsonThermometerUnitFilingPinBalance.original Z scheme branches units T P k
    (only S (fun v=>select v v)) paid center meter β g cash late width gp cp heat d income accuracy e r u wanted

end YM.Integration.WilsonThermometerUnitFilingPinRegister
