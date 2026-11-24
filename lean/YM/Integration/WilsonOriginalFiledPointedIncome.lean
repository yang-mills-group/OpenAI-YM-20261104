import YM.Integration.WilsonCapturedMountedColorIncome
import YM.Integration.WilsonCapturedClockedDeckBinding

/-! A real angular filing of a whole pointed roster at the original radius. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalFiledPointedIncome
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Comparison.RG02 Comparison.RG02.Adjacent Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonCapturedPinnedGroupClock WilsonCapturedPinnedClockIncome
open WilsonCapturedCoveredSourceWage WilsonCapturedPinnedColorFile WilsonOriginalLinkedAngularPage
open WilsonOriginalCenteredSeamSalary WilsonCapturedRootedAngularSlots WilsonCapturedClockRankProjection
open WilsonOriginalPolarizedAngularPage WilsonOriginalCompactDeckRead
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open scoped Classical BigOperators
variable {G:Gauge}{n N:Side}{V X ι:Type}[DecidableEq V]{o:Passport n V}{J:Census V}
    (h:n.val∣N.val)(M:ι→Row o J G X)(t:X)(s:J.Mode)(v:s.val)
    {w:V→ℝ}{grades:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf)(hs:0<σ)
    (b:PagesOf n N)(clock:UnitCost)(pole:ℕ)(quiet:ℝ → Config G N → ℝ)

private theorem fullGroup : group h (crop M (fun _=>True)) t s v b=group h M t s v b:=by
  funext θ U
  let all : {i:ι//True}≃ι :={
    toFun:=Subtype.val
    invFun:=fun i=>⟨i,True.intro⟩
    left_inv:=fun i=>by cases i;rfl
    right_inv:=fun _=>rfl }
  let term (i:ι) : ℂ:=∑p:PagesOf n N,if (M i).mode=s ∧ WilsonOriginalPaidWalkCover.index h (M i) p v.val=b then
    (M i).paint t*Complex.ofReal (Loan.letter (WilsonOriginalPaidWalkCover.row h (M i) p).lamp
      (WilsonOriginalPaidWalkCover.row h (M i) p).atom (WilsonOriginalPaidWalkCover.row h (M i) p).center θ U) else 0
  exact all.tsum_eq term

theorem whole : ink h (crop M (fun _=>True)) t s v b pole quiet=ink h M t s v b pole quiet:=by
  unfold ink
  rw [fullGroup]

local notation "held" => ink h M t s v b pole quiet
local notation "read" => (fun e a=>See.noseC (Stock.census Unit) () clock (held) e (Stationary.arm G N 1 a))

include stock hs in
theorem original (L:ℂ→L[ℝ]ℝ)(sh:LipschitzWith 1 L)(limit e r:ℕ)(hr:0<r):
    let home:=(page h (o.origin v.val) b).val
    let A:=WilsonCapturedRealFiledKernel.entries (fun j=>L ∘ read j)
    Arm.Single clock (channel L (held)) A () limit pole ∧
    Poly.toll w s*(∑x:Fin r→Site N×Loc G 1,Real.exp ((σ/8)*(radius home (sites x):ℝ))*|A e r x|) ≤
      (r.factorial:ℝ)⁻¹*charge clock (-(pole:ℤ)) (pole+e) r (fun j=>fare G j r σ C) ∧
    ∀j a,See.noseC (Stock.census Unit) () clock (channel L (held)) j (Stationary.arm G N 1 a)=(L (read j a):ℂ):=by
  intro home A
  have bought:=WilsonCapturedMountedColorIncome.original h M t s v stock hs (fun _=>True)
    b clock pole quiet L sh e r hr
  have filed:=WilsonCapturedPinnedColorFile.filed h M t s v stock hs (fun _=>True)
    b clock pole quiet L limit
  have displays:=WilsonCapturedPinnedColorFile.seenChannel h M t s v stock hs (fun _=>True)
    b clock pole quiet L
  have rows (j:ℕ) : reportedRow h M t s v (fun _=>True) b clock pole j quiet=read j:=by
    unfold reportedRow
    rw [whole]
  simpa only [A,home,rows,whole] using And.intro filed (And.intro bought.2 displays)

theorem projected (L:ℂ→L[ℝ]ℝ)(root:Site N)(u z:Link G N→ℂ)
    (appeared:board h root (move G) (flat u)=flat z):
    board h root (move G) (flat (fun a=>(L (u a):ℂ)))=flat (fun a=>(L (z a):ℂ)):=by
  funext a
  have seen:=congrFun appeared a
  rw [WilsonOriginalCompactDeckRead.copies] at seen ⊢
  simp only [flat,Pi.sub_apply] at seen ⊢
  let lift:=Complex.ofRealCLM ∘L L
  change (∑v:WilsonOriginalConnectedPeriodPage.Deck h,(lift (u (move G v.val a))-lift (u 0)))=lift (z a)-lift (z 0)
  rw [←map_sub]
  simp only [←map_sub,←map_sum]
  exact congrArg lift seen

end YM.Integration.WilsonOriginalFiledPointedIncome
