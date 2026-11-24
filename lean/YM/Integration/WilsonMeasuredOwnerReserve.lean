import YM.Integration.WilsonMeasuredOwnerPicture
import YM.Integration.WilsonMeasuredCourseQuietSlots
import YM.Integration.WilsonCenteredDividedRoom

/-! One occupied scalar on the same course, priced at the original hard
divisor.  Its quiet and fired fields are the complete Wilson densities. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerReserve
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Tree AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal.Advent
open Push Push.Local Push.PriceCompiler AnalyticBridge VerifiedReset RemainderComparison
open AllOrder.Transit WheelP PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pressure ConnectedActivityE6 Filter
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 1)

def disk (_ : Fin 1) : Set ℂ := {x | ‖x‖≤1}
def kernel (_ : Fin 1) : Submodule ℝ ℂ := ⊥
def test (x:Wallet disk) : ℂ := (x 0).val

theorem listens : Attn kernel disk {0} test :=by
  refine ⟨fun x y eq=>congrArg Subtype.val (eq 0 (mem_singleton_self _)),?_,?_⟩
  · intro j hj x s t u a b hu
    obtain rfl:=mem_singleton.mp hj
    simpa only [test,Function.update_self] using hu
  · intro j hj x hx
    obtain rfl:=mem_singleton.mp hj
    exact (Submodule.mem_bot ℝ).mp hx

variable {G:Gauge} (R : Run G)

theorem room (simple : G.Simple) : ∀ᶠ i:ℕ in atTop,
    R.family.path.levels.clock.forcedAllowance i ≤ LocalComparison.forcedDivisor R.family i / 2 :=by
  let A:=R.family.path.levels
  have rate:=(RG01.Physical.shrink simple A 0).eventually_le_const (by norm_num : (0:ℝ)<1/4)
  filter_upwards [rate] with i hi
  have cap : A.clock.forcedAllowance i≤1/4 :=by simpa using hi
  have pos := allowance_pos A.clock i
  have sq := Real.sq_sqrt pos.le
  change A.clock.forcedAllowance i≤Real.sqrt (A.clock.forcedAllowance i)/2
  have half : Real.sqrt (A.clock.forcedAllowance i)≤1/2 :=by
    nlinarith [Real.sqrt_nonneg (A.clock.forcedAllowance i)]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg (A.clock.forcedAllowance i))
    (sub_nonpos.mpr half)]

variable {m N per k i : ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ a,Rep G (R.family.side a per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (begun : m ≤ i) (live : i ≤ N)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "cash" => R.family.path.levels.clock.forcedAllowance i
local notation "W" => (Ψ i)
local notation "P" => R.family.path.rep N per i

include course begun live in
theorem original (small : cash≤κ/2) {d:ℕ} {F:Frame G d} (S:SectionData F) (A:Hol G)
    (y:Site (R.family.side i per)) (q:Coefficient F (R.family.side i per))
    (law:q.Format y A W) (M:ℝ) (bill:q.remBound y W κ M)
    (w:ℝ) (rad:0<w) (testable:w*M≤1/2) :
    let O:=Passport.point (fun _:Fin 1=>y)
    ∃ Z:Tint.Incoming O W (Wallet disk) Empty (J),
      Taut O.support disk kernel Z.old ∧ Crown O.support disk kernel Z.hard ∧
      Z.old.Paid (fun _=>w) (W).p.B ((W).p.supportExponent+1+1) 0 ∧
      Z.hard.Paid (fun _=>w) (W).p.B (W).p.supportExponent κ ∧
      ∀ x U,let M₀:Empty→Row O (J) G (Wallet disk):=Empty.elim
        ((Tint.Patrol.picture M₀ Z).density x U).part (J).quiet=(W).eval U ∧
        ((Tint.Patrol.picture M₀ Z).density x U).part ((J).fire 0)=
          test x*(q.density y S W U-(WilsonPhysicalMarkedDefect.RegularProjection.soft q).density y S P U) :=by
  intro O
  have ok := (later R π Γ Ψ course begun live).truep.valid.labels
  let rented : Hard.Rent (W).activities.forced (W).activities.K (W).p (W).p.supportExponent cash :=
    Hard.rentValid ok.forced ok.boundK
  obtain ⟨budget,owners,-⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course begun live
  have view : (W).eval=(P).eval:=(later R π Γ Ψ course begun live).view
  let fresh := WilsonMeasuredSingleOwner.intake (o:=O.origin) («J»:=J) rented 0 q law test
  obtain ⟨affine,attn⟩:=WilsonMeasuredSingleOwner.admitted (o:=O.origin) («J»:=J) rented 0 q law test listens
  have bounded (x:Wallet disk):‖test x‖≤1:=(x 0).property
  let ww : Fin 1→ℝ := fun _=>w
  have wpos (v:Fin 1):0<ww v:=rad
  obtain ⟨vac,hard,-⟩:=WilsonMeasuredSingleOwner.received (o:=O.origin) («J»:=J) rented 0 q law test ww wpos
    bounded bill budget view owners S
  have zero : 0≤κ:=Real.sqrt_nonneg _
  have spend : cash+w*(κ*M)≤κ:=by nlinarith [mul_le_mul_of_nonneg_left testable zero]
  exact ⟨fresh,affine,attn,vac,Hard.mono _ hard spend,fun x U=>
    WilsonMeasuredOwnerPicture.field (o:=O.origin) («J»:=J) rented 0 q law test ww wpos bounded bill
      budget view owners S x U⟩

end YM.Integration.WilsonMeasuredOwnerReserve
