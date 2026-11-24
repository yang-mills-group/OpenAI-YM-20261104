import YM.Integration.WilsonThermometerUnitFilingPinSalary
import YM.Integration.WilsonThermometerUnitFilingPinFiber
import YM.Integration.WilsonThermometerUnitFilingCoverRegister

/-! The full angular opening and the countable signed aperture on the submitted inversion board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinSum
open Function Finset Filter Wilson RG Lattice RegulatorIR Geometry Taping Budget Budget.Packet Budget.Tuple
open Diagram Prim Profiles Halo Ledger Ledger.Sky Cluster
open WilsonThermometerUnitFilingCoverRegister WilsonThermometerUnitFilingCoverAudition
open scoped ENNReal BigOperators Classical Topology

variable {G:Gauge}{h:ℕ}

theorem grade (S:Submission G)(paid:S.grades ()+1=h)(i:S.I):h ≤ (S.rows i).lamp.toll+1:=by
  rw [WilsonThermometerUnitFilingCoverNotice.degree S.rows S.bought i,paid]

def line (S:Submission G)(paid:S.grades ()+1=h)(z:Cover)(i:S.I):Orders (Foot G):=
  WilsonThermometerUnitFilingPinEdition.row S.rows S.test S.read (grade S paid) z i

def complete (S:Submission G)(paid:S.grades ()+1=h)(z:Cover):Orders (Foot G):=
  fun e r u=>∑' i,line S paid z i e r u

theorem ranks (S:Submission G)(paid:S.grades ()+1=h)(z:Cover):Ranks h (complete S paid z):=by
  intro e r nz
  by_contra high
  apply nz
  funext x
  have term (i:S.I):line S paid z i e r x=0:=by
    have rank:=(WilsonThermometerUnitFilingPinEdition.served S.rows S.test S.read (grade S paid) z i).2
    have zero:line S paid z i e r=0:=by
      by_contra live
      exact high (rank e r live)
    rw [zero];rfl
  change (∑' i,line S paid z i e r x)=0
  simp only [term,tsum_zero]

variable {W:Type}{k:W→ℕ}{sides:Page k→Side}{L:Heir sides G}(T:L.Accounts)
  (S:W→Submission G)(paid:∀ v,(S v).grades ()+1=h)(z:W → Cover)

def total:T.Report h:=declaring T (fun v=>complete (S v) (paid v) (z v))
  (fun v=>ranks (S v) (paid v) (z v))

theorem opening (v:W):
    (total T S paid z).main (Page.opening k v)=complete (S v) (paid v) (z v):=rfl

theorem original (v:W)(film:Finset (S v).I→T.Report h)
    (born:∀ s,BasisT h h (convey (z v) (bank (S v).rows s (S v).test (S v).read))
      ((film s).main (Page.opening k v))):
    Tendsto (fun s=>(film s).point (Page.opening k v)) atTop
      (𝓝 ((total T S paid z).point (Page.opening k v))):=by
  let D:=S v
  let p:=Page.opening k v
  let A:=L.maps p
  let β:=max (Real.exp 1) (Real.exp (D.σ⁻¹^2))
  apply tendsto_pi_nhds.mpr
  intro e
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro y
  let f (i:D.I):=line D (paid v) (z v) i e r
  let cost:=WilsonThermometerUnitFilingPinSalary.wage D.rows D.rad D.σ 1 β h e
  have pos:∀ i,0 ≤ cost i:=fun _=>abs_nonneg _
  have cash:Summable cost:=WilsonThermometerUnitFilingPinSalary.summable D.rows D.bought e
  have wage:∀ i,quota (f i) 1 ≤ ENNReal.ofReal (cost i):=fun i=>
    WilsonThermometerUnitFilingPinSalary.original D.rows D.test D.read (grade D (paid v)) (z v) D.bought
      T v D.width zero_lt_one (le_max_left ..) (le_max_right ..) D.short e r i
  have part (s:Finset D.I): (film s).point p e r y=∑ i∈s,A.scroll (f i) y:=by
    rw [(film s).same]
    rw [WilsonThermometerUnitFilingPinEdition.registered D.rows D.test D.read (grade D (paid v))
      (z v) v (film s) s (born s)]
    simp only [Finset.sum_apply]
    exact WilsonThermometerUnitFilingPinFiber.finite A f pos cash wage s y
  change Tendsto (fun s=>(film s).point p e r y) atTop (𝓝 (A.scroll (fun u=>∑' i,f i u) y))
  simp_rw [part]
  exact WilsonThermometerUnitFilingPinFiber.original A f pos cash wage y

end YM.Integration.WilsonThermometerUnitFilingPinSum
