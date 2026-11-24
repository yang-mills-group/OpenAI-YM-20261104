import YM.Gaps1020.Local.Verified
import YM.Integration.ActualRunSpring
import YM.Integration.OriginalMarkedSpringInstallation

/-! The purchased signed physical action on the local integration step
carried by an already selected Run. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice RG Wilson RG.Supply Pressure Extra.Histories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open GapsLocal.Renew
open scoped Classical
variable {G : Gauge} (R : Run G) {N p m : ℕ} (hm : m<N)
local notation "step" => ActualRunSpring.selected R N p m hm
local notation "out" => R.family.path.rep N p m
local notation "B" => R.alloy.B.a.budget m
local notation "price" d:max => (Real.sqrt 2 * Pert.Asymptotics.regulatorRun R.family N p (m+1))^(d+1)

abbrev approximation (d : ℕ) := presentation (premium d) (step).spring (step).point
abbrev remainder (d : ℕ) := ignored (premium d) (step).spring (step).point

private theorem log_factor {a b t : ℝ} (factor : a=b*Real.exp (-t)) (pos : 0<a) :
    -Real.log a+Real.log b = t := by
  have hb : b≠0 := by
    intro h
    rw [h,zero_mul] at factor
    exact pos.ne' factor
  rw [factor,Real.log_mul hb (Real.exp_ne_zero _),Real.log_exp]
  ring

section packet
variable (S : ActualRunSpring.Packet R N p m hm) (d : ℕ)
local notation "keep" => presentation (premium d) S.spring S.point
local notation "err" => ignored (premium d) S.spring S.point

structure Receipt : Prop where
  posterior : Posterior (premium d) S.spring S.point (price d)
  path : (keep).path = (out).path
  clip : (keep).clip = (out).clip
  coupling : (keep).beta = (out).beta
  vacuum : (keep).v = (out).v
  forced : (keep).activities.forced = (out).activities.forced
  charges : (keep).activities.K = (out).activities.K
  signed (U : Config G (R.family.side m p)) :
    -Real.log ((out).eval U)+Real.log ((keep).eval U) = (err).additive B U

private theorem input_price :
    (Real.sqrt 2*GapsLocal.Vacuum.nativeG (S.input S.point.val).beta)^(d+1) = price d := by
  change (Real.sqrt 2*(Real.sqrt (S.input S.point.val).beta)⁻¹)^(d+1) =
    (Real.sqrt 2*(Real.sqrt (R.family.path.rep N p (m+1)).beta)⁻¹)^(d+1)
  rw [S.input_beta]

private theorem posterior (hG : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fee : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (order : premium d ≤ R.alloy.B.a.clock.J (m+1)) : Posterior (premium d) S.spring S.point (price d) := by
  rw [← input_price R hm S d]
  exact presentB (premium d) S.spring S.point hm marks order hG fee rfl

private theorem path_receipt : (keep).path = (out).path := by
  have kept : (keep).path = (S.spring.result S.point.val).path := rfl
  have outputEq : (S.spring.result S.point.val).path = (R.family.path.rep N p m).path :=
    congrArg (fun X : Rep G (R.family.side m p) => X.path) S.coarse.symm
  exact kept.trans outputEq

private theorem clip_receipt : (keep).clip = (out).clip := by
  have kept : (keep).clip = (S.spring.result S.point.val).clip := rfl
  have outputEq : (S.spring.result S.point.val).clip = (R.family.path.rep N p m).clip :=
    congrArg (fun X : Rep G (R.family.side m p) => X.clip) S.coarse.symm
  exact kept.trans outputEq

private theorem coupling_receipt : (keep).beta = (out).beta := S.output_beta

private theorem vacuum_receipt : (keep).v = (out).v := by
  have kept : (keep).v = (S.spring.result S.point.val).v := rfl
  have outputEq : (S.spring.result S.point.val).v = (R.family.path.rep N p m).v :=
    congrArg (fun X : Rep G (R.family.side m p) => X.v) S.coarse.symm
  exact kept.trans outputEq

private theorem forced_receipt : (keep).activities.forced = (out).activities.forced := by
  have kept : (keep).activities.forced = (S.spring.result S.point.val).activities.forced :=
    (OriginalMarkedSpringInstallation.presentation S.spring S.point (premium d)).forced
  have outputEq : (S.spring.result S.point.val).activities.forced = (R.family.path.rep N p m).activities.forced :=
    congrArg (@Activities.forced G (R.family.side m p)) S.output_activities
  exact kept.trans outputEq

private theorem charges_receipt : (keep).activities.K = (out).activities.K := by
  have kept : (keep).activities.K = (S.spring.result S.point.val).activities.K :=
    (OriginalMarkedSpringInstallation.presentation S.spring S.point (premium d)).charges
  have outputEq : (S.spring.result S.point.val).activities.K = (R.family.path.rep N p m).activities.K :=
    congrArg (@Activities.K G (R.family.side m p)) S.output_activities
  exact kept.trans outputEq

private theorem factor_receipt (F : Posterior (premium d) S.spring S.point (price d))
    (U : Config G (R.family.side m p)) : (out).eval U =
      (keep).eval U * Real.exp (-(err).additive B U) :=
  (congrArg (fun X : Rep G (R.family.side m p) => X.eval U) S.coarse).trans (F.matters U)

private theorem signed_receipt (F : Posterior (premium d) S.spring S.point (price d))
    (U : Config G (R.family.side m p)) :
    -Real.log ((out).eval U)+Real.log ((keep).eval U) = (err).additive B U :=
  log_factor (factor_receipt R hm S d F U)
    (Multi.AxisShift.chosen_positive (H:=R.family.path) R.makes.wilson hm.le U)

private theorem from_posterior (F : Posterior (premium d) S.spring S.point (price d)) :
    Receipt R hm S d :=
  ⟨F,path_receipt R hm S d,clip_receipt R hm S d,coupling_receipt R hm S d,
    vacuum_receipt R hm S d,forced_receipt R hm S d,charges_receipt R hm S d,signed_receipt R hm S d F⟩

end packet

abbrev Comparison (d : ℕ) := Receipt R hm (ActualRunSpring.selected R N p m hm) d

/-- Every field and forced charge is retained on the selected packet.
The original posterior prices the derivative, support, coupling and
vacuum errors using the true fine coupling. -/
theorem purchased (hG : G.Simple) (d : ℕ)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fee : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (order : premium d ≤ R.alloy.B.a.clock.J (m+1)) : Comparison R (p:=p) hm d :=
  from_posterior R hm (step) d (posterior R hm (step) d hG marks fee order)

/-- The same preselected Run and its genuine Spring answer every period
and upper cutoff after a single level threshold for each order. -/
theorem calendar (hG : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fee : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) :
    ∀ d : ℕ, ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ) (hm:m<N), Comparison R (p:=p) hm d := by
  intro d
  filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop (premium d)] with m order N p hm
  exact purchased R hm hG d marks fee (order.trans (R.alloy.B.a.fits.mono (Nat.le_succ m)))

end YM.Integration.OriginalMarkedRunAction
