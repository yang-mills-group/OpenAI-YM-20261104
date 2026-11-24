import YM.Integration.WilsonCapturedPinnedColorFile
import YM.Integration.WilsonOriginalCompactDeckRead
/-! Reassemble the enrolled marked root orbit at its own registered clock.
Each group ray and the empty group divisor keep their actual material. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedClockedDeckBinding
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Moving.Path Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset AllOrder.Floe
open WilsonOriginalOccupiedFieldLayout WilsonOriginalJointDeckMotion WilsonOriginalPolarizedAngularPage
open WilsonCapturedPinnedGroupClock WilsonCapturedCoveredSourceWage WilsonCapturedPinnedClockIncome
open WilsonOriginalPinnedDeckOrbit WilsonOriginalLinkedAngularPage WilsonOriginalCompactDeckRead
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open scoped Classical BigOperators ContDiff

def whole {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{J:Census V}(Z:Bulk.Colors J G n)(s:Hot J):
    Bulk.Colors (Stock.census Unit) G n where
  vac:=Z.vac
  mark _:=Z.mark s
  power _:=Z.power s

private theorem shifted {G:Gauge}{N:Side}(v:Site N)(θ u:ℝ)(x:Link G N):
    WilsonOriginalJointDeckMotion.motion G v ((WilsonCapturedPinnedGroupClock.basis G N) (u,θ • x))=
      WilsonCapturedPinnedGroupClock.basis G N (u,θ • (move G v x)):=by
  ext1
  · rfl
  · simp [WilsonOriginalJointDeckMotion.motion,WilsonCapturedPinnedGroupClock.basis]

variable {G:Gauge}{n N:Side}{V X ι:Type}[DecidableEq V]{o:Passport n V}{J:Census V}
    (h:n.val∣N.val)(M:ι→Row o J G X)(t:X)
    {w:V→ℝ}{grades:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf)(hs:0<σ)
    (L:Layout G)(T:Finset Age)(s:Hot J)(v:s.val.val)(b:PagesOf n N)
    (clock:UnitCost)(e:ℕ)(root:Site N)
local notation "K" => WilsonOriginalPinnedGradedPeek.bank h M t grades L T
local notation "one" => ink h M t s.val v b ((K).power s) (K).vac
local notation "pinned" => (fun a:Link G N=>See.noseC (Stock.census Unit) () clock (one) e (Stationary.arm G N 1 a))
local notation "entire" => (fun a:Link G N=>See.noseC (Stock.census Unit) () clock (whole (K) s) e (Stationary.arm G N 1 a))

include stock hs in
theorem original : board h root (move G) (pinned) = (entire):=by
  funext x
  let loc(p:PagesOf n N):=(page h (splitter h root) p).val-root
  let realPath(p:PagesOf n N)(θ:ℝ):ℂ:=((clock.rating θ)^((K).power s))⁻¹ •
    localField h M t s.val v b (WilsonCapturedOriginalClockTaylor.ray clock (move G (loc p) x) θ)
  have regular:=WilsonCapturedPinnedGroupClock.regular h M t s.val v stock hs b
  have smooth(p:PagesOf n N):ContDiffAt ℝ ω (realPath p) 0:=
    ((clock.smooth.pow _).inv (by simp [clock.origin])).smul
      (regular.contDiffAt.comp _ (clock.here.prodMk (contDiffAt_id.smul contDiffAt_const)))
  have assembled: (fun θ:ℝ=>∑p:PagesOf n N,realPath p θ)=
      Arm.shineM clock (whole (K) s) () (Stationary.arm G N 1 x):=by
    funext θ
    have test:=congrFun (WilsonOriginalPinnedDeckOrbit.original h M t s.val v stock hs 0 b root)
      ((WilsonCapturedPinnedGroupClock.basis G N) (clock.enter θ,θ • x))
    unfold board at test
    simp only [Finset.sum_apply,Function.comp_apply,shifted] at test
    change (∑p:PagesOf n N,((clock.rating θ)^((K).power s))⁻¹ •
      needle h M t s.val v 0 b ((WilsonCapturedPinnedGroupClock.basis G N) (clock.enter θ,θ • (move G (loc p) x))))=
      _ • (K).mark s (clock.enter θ) (Integral.sample θ (Stationary.arm G N 1 x))
    rw [←Finset.smul_sum,test,draw]
    simp only [shade,pow_zero,Complex.ofReal_one,one_mul]
    exact congrArg (((clock.rating θ)^((K).power s))⁻¹ • ·)
      (WilsonOriginalOccupiedFieldLayout.filed h M t stock hs L T s ((WilsonCapturedPinnedGroupClock.basis G N) (clock.enter θ,θ • x)))
  unfold board
  rw [Finset.sum_apply]
  change (∑p:PagesOf n N,See.noseC (Stock.census Unit) () clock (one) e (Stationary.arm G N 1 (move G (loc p) x)))=_
  calc
    _ = ∑p:PagesOf n N,Comparison.RG02.Moving.Path.motion (realPath p) ((K).power s+e):=by
      apply sum_congr rfl;intro p _
      exact congrFun (WilsonCapturedPinnedGroupClock.clock h M t s.val v clock b _ e (K).vac) (move G (loc p) x)
    _ = Comparison.RG02.Moving.Path.motion (fun θ=>∑p:PagesOf n N,realPath p θ) ((K).power s+e):=
      (Comparison.RG02.Moving.Shift.msum _ _ (fun p _=>smooth p)).symm
    _ = _:=by rw [assembled];rfl

include stock hs in
theorem centered : board h root (move G) (flat (pinned))=flat (entire):=by
  rw [←original h M t stock hs L T s v b clock e root]
  funext y
  rw [WilsonOriginalCompactDeckRead.copies]
  change (∑c:WilsonOriginalConnectedPeriodPage.Deck h,((pinned) (move G c.val y)-(pinned) 0))=_
  rw [Finset.sum_sub_distrib]
  change _ = board h root (move G) (pinned) y - board h root (move G) (pinned) 0
  rw [WilsonOriginalCompactDeckRead.copies,WilsonOriginalCompactDeckRead.copies];simp

end YM.Integration.WilsonCapturedClockedDeckBinding
