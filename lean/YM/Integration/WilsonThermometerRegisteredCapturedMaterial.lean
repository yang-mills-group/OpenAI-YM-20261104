/- The same paid captured pupil reads every positive coupling with the original finite angular degrees. -/
import YM.Integration.WilsonThermometerRegisteredCapturedUncut
import YM.Integration.WilsonMarkedFixedPoleGross

noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedMaterial
open Finset RG Marker Multi Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push Push.AbsoluteSums Push.Local Planned.GuardedAtom Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02
open WilsonThermometerRegisteredCapturedPace WilsonThermometerRegisteredCapturedUncut
open WilsonThermometerRegisteredCapturedSector WilsonThermometerRegisteredCapturedLedger
open WilsonThermometerCenteredAlgebra WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
local notation "J"=>Stock.census (Fin 3)
local notation "D"=>Stock.census Unit
variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {α ι:Type}
variable {B:Earn.Passport n Unit} (X:ι→Earn.Row P J G α) (r:ℝ) (hr:0<r)
variable {σ C:ℝ} {ord seats shelf:ℕ} (ages:Fin 3→ℕ) (w:Fin 3→ℝ)
variable (sold:Scene.Armada X w ages σ C ord seats shelf) (spent:∑v:Fin 3,ages v≤14)
variable (paths:Fin 3→Walk) (S:Earn.Binder B D) (t:α) (Q:Poly J) (A:Unit→Set ℂ)
local notation "X'"=> (fun z=>returned r hr (X z))
local notation "sold'"=>WilsonThermometerRegisteredCapturedPace.original r hr X w ages sold
local notation "M"=>submitted X r hr ages w sold spent paths S t Q A

include sold spent in
theorem price (b:BudgetPoint) {g cap a ξ:ℝ} (fund:Invoice.Supports b cap a g σ ξ)
    (y:ℝ) (hy:0<y):
    ∃c:ℝ,Gross (rendered X b y) w b.B a c:=by
  have gp:=fund.1
  let d:=y/g
  have hd:0<d:=div_pos hy gp
  have eqn:d*g=y:=div_mul_cancel₀ _ gp.ne'
  have res:=WilsonThermometerRegisteredCapturedPace.original d hd X w ages sold
  have scope(s:(J).Mode):(∑v∈s.val,ages v)+1≤15:=by
    have hs:(∑v∈s.val,ages v)≤∑v:Fin 3,ages v:=sum_le_sum_of_subset (subset_univ _)
    omega
  have account:=WilsonMarkedFixedPoleGross.landed (fun z=>returned d hd (X z)) w ages b res fund 15 scope
  obtain ⟨f,pos,at_test,paid⟩:=account
  refine ⟨_,f,pos,?_,paid⟩
  intro z x U
  have tested:=at_test z x U
  change ‖(returned d hd (X z)).nominal g x U‖≤f z at tested
  rwa [evaluated,eqn] at tested

theorem original (b:BudgetPoint) {g cap a ξ:ℝ} (fund:Invoice.Supports b cap a g σ ξ)
    (K:ℕ) (reach:∀v,(paths v).length≤K) (incidence:∀v,stop S.center (paths v)=P.origin v)
    (test:Affinity.Wallet A)(unit:∀x,‖amplitude A x‖≤1)
    {capacity horizon work:ℕ}(hc:1≤capacity)(hh:21≤horizon)(hw:3*ord≤work):
    let fee:=total (ord:=ord) (σ:=σ) (C:=(bound r)^(ord+shelf+1)*C) w S (weights Q) K
    0≤fee ∧ Scene.Armada M (fun _=>1) (fun _=>21) σ fee work capacity horizon ∧
      Tableau (fun _:Unit=>(⊥:Submodule ℝ ℂ)) A M ∧
      ∀y:ℝ,0<y→∀(x:Affinity.Wallet A)(U:Config G n),
        Spill.Foundry.uncut M y x U=Poly.send ((D).fire ())
          (amplitude A x*((Poly.pass (bare (rendered X b (r*y)) t U))*Q).part full):=by
  obtain ⟨ha,xi,wide⟩:=fund.2.2.2.2.2
  have pos:0<σ:=by nlinarith only [xi,wide,mul_nonneg ha (inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) b.B))]
  have stock:=WilsonThermometerRegisteredCapturedLedger.original X' ages w sold' spent paths S t
    (weights Q) (amplitude A) K pos.le reach test incidence unit hc hh
  have bigger:Scene.Armada M (fun _=>1) (fun _=>21) σ (total (ord:=ord) (σ:=σ) (C:=(bound r)^(ord+shelf+1)*C) w S (weights Q) K) work capacity horizon:=by
    refine ⟨stock.toMinistry,stock.positive,stock.suggests,⟨stock.purchases.spend,
      fun u=>⟨((stock.purchases.usable u).1).trans hw,(stock.purchases.usable u).2⟩⟩,stock.honor⟩
  refine ⟨budget_nonneg (stock.suggests (0:Site n)),bigger,?_,?_⟩
  · exact WilsonThermometerRegisteredCapturedSector.original X' ages w sold' spent paths S t (weights Q) A
  · intro y hy x U
    obtain ⟨c,paid⟩:=price X ages w sold spent b fund (r*y) (mul_pos hr hy)
    exact WilsonThermometerRegisteredCapturedUncut.original X r hr ages w sold spent paths S t Q A
      y hy.ne' x U incidence unit b ha paid
end YM.Integration.WilsonThermometerRegisteredCapturedMaterial
