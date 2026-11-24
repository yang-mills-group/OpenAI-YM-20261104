import YM.Integration.WilsonCapturedPinnedClockIncome
import YM.Integration.WilsonCapturedRealFiledKernel

/-! The native finite real filing of the actual group-valued marked cohort,
including either real channel of a complex tested source at its appointed clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPinnedColorFile
open Function Lattice RG Wilson Exterior Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Moving.Path Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonCapturedPinnedGroupClock WilsonCapturedPinnedClockIncome
open WilsonCapturedCoveredSourceWage WilsonCapturedOccupiedClockTaylor WilsonOriginalLinkedAngularPage
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open scoped Classical BigOperators ContDiff

def channel {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{J:Census V}
    (L:ℂ→L[ℝ]ℝ)(Z:Bulk.Colors J G n):Bulk.Colors J G n where
  vac:=Z.vac
  power:=Z.power
  mark s t U:=(L (Z.mark s t U):ℂ)

theorem commutes {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{J:Census V}
    (L:ℂ→L[ℝ]ℝ)(Z:Bulk.Colors J G n)(C:UnitCost)(u:V)(a:fieldDir G n 1):
    Arm.shineM C (channel L Z) u a=(Complex.ofRealCLM ∘L L) ∘ Arm.shineM C Z u a:=by
  funext θ
  let z:=Z.mark (Arm.pub u) (C.enter θ) (Integral.sample θ a)
  let α:=((C.rating θ)^(Z.power (Arm.pub u)))⁻¹
  change α • (L z:ℂ) = (L (α • z):ℂ)
  rw [map_smul];exact (Complex.ofRealCLM.map_smul α (L z)).symm

variable {G:Gauge}{n N:Side}{V X ι:Type}[DecidableEq V]{o:Passport n V}{J:Census V}
    (h:n.val∣N.val)(M:ι→Row o J G X)(t:X)(s:J.Mode)(v:s.val)
    {w:V→ℝ}{grades:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf)(hs:0<σ)(cut:ι→Prop)
    (b:PagesOf n N)(clock:UnitCost)(pole:ℕ)(quiet:ℝ → Config G N → ℝ)

local notation "Z" => ink h (crop M cut) t s v b pole quiet
local notation "row" => reportedRow h M t s v cut b clock pole
local notation "germ" => localField h (crop M cut) t s v b

include stock hs in
theorem finite (e:ℕ):Valence.Level (e+pole:ℕ) (row e quiet):=by
  have ok:=WilsonCapturedPinnedGroupClock.regular h (crop M cut) t s v (earned M stock cut) hs b
  have read:row e quiet=born (layers germ) clock (-(pole:ℤ)) (pole+e) (pole+e):=by
    unfold reportedRow
    rw [WilsonCapturedPinnedGroupClock.clock]
    exact funext (WilsonCapturedOccupiedClockTaylor.original clock pole _ germ ok.contDiffAt)
  rw [read,Nat.add_comm e pole]
  exact apportion clock _ _ (WilsonCapturedOccupiedClockTaylor.grades germ ok.contDiffAt _) _ le_rfl (by intro j hj;exact_mod_cast hj.le)

include stock hs in
theorem seenChannel (L:ℂ→L[ℝ]ℝ)(e:ℕ)(a:Link G N):
    See.noseC (Stock.census Unit) () clock (channel L (Z)) e (Stationary.arm G N 1 a)=(L (row e quiet a):ℂ):=by
  let D:=Complex.ofRealCLM ∘L L
  have actual:Arm.shineM clock (Z) () (Stationary.arm G N 1 a)=
      fun θ:ℝ=>((clock.rating θ)^pole)⁻¹ • germ (WilsonCapturedOriginalClockTaylor.ray clock a θ):=by
    funext θ
    change _ • group h (crop M cut) t s v b (clock.enter θ) _=_
    rw [draw]
    exact congrArg (((clock.rating θ)^pole)⁻¹ • ·) (seen h (crop M cut) t s v b (clock.enter θ,θ • a))
  have basis:ContDiffAt ℝ ω (WilsonCapturedOriginalClockTaylor.ray clock a) 0:=
    clock.here.prodMk (contDiffAt_id.smul contDiffAt_const)
  have shape:=WilsonCapturedPinnedGroupClock.regular h (crop M cut) t s v (earned M stock cut) hs b
  have path : ContDiffAt ℝ ω (Arm.shineM clock (Z) () (Stationary.arm G N 1 a)) 0:=by
    rw [actual]
    exact ((clock.smooth.pow _).inv (by simp [clock.origin])).smul (shape.contDiffAt.comp _ basis)
  unfold See.noseC
  rw [commutes]
  exact (Assembly.jet_apply_left D _ _ (path.of_le le_top) 1).symm

include stock hs in
theorem filed (L:ℂ→L[ℝ]ℝ)(H:ℕ):
    Arm.Single clock (channel L (Z))
      (WilsonCapturedRealFiledKernel.entries (fun e=>L ∘ row e quiet)) () H pole:=by
  apply WilsonCapturedRealFiledKernel.original
  · intro e
    have g:=finite h M t s v stock hs cut b clock pole quiet e
    refine ⟨L.contDiff.comp g.smooth,?_⟩
    intro r high x
    rw [L.iteratedFDeriv_comp_left (g.smooth.contDiffAt : ContDiffAt ℝ ω _ x) le_top,g.high r high x]
    ext xs;change L (0:ℂ)=0;exact L.map_zero
  · intro e _ a;exact seenChannel h M t s v stock hs cut b clock pole quiet L e a

include stock hs in
theorem coefficient (L:ℂ→L[ℝ]ℝ)(e r:ℕ)(x:Fin r→Site N×Loc G 1):
    WilsonCapturedRealFiledKernel.entries (fun e=>L ∘ row e quiet) e r x=
      (r.factorial:ℝ)⁻¹ • L (WilsonOriginalLinkedAngularPage.coefficient r (row e quiet) x):=by
  have lev:=finite h M t s v stock hs cut b clock pole quiet e
  change (r.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ r (L ∘ row e quiet) (0:Link G N) _=_
  rw [L.iteratedFDeriv_comp_left (lev.smooth.contDiffAt : ContDiffAt ℝ ω (row e quiet) (0:Link G N)) (show (r:WithTop ℕ∞)≤ω from le_top)]
  rfl

end YM.Integration.WilsonCapturedPinnedColorFile
