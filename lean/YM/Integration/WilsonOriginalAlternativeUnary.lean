import YM.Integration.WilsonCenteredReceivedAggregate
import YM.Integration.WilsonMeasuredCourseQuietSlots
import YM.Integration.ActualWilsonPrimaryPreparation

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeUnary
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "account" => (Ω^6)⁻¹*(modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee)
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i


local notation "W_" => Ψ i
local notation "J_" => Stock.census V

include course cut in
/-- At a genuine one-root mode the centered return is entirely housed on the
stated root, regardless of the other roots' positions. Its actual hard address
and all compatible vacuum partners are retained when subtracting a primary. -/
theorem original (way:WayStation R.kit) (simple:G.Simple) (late:WilsonCenteredCaptureClock.first R simple ≤ i)
    (d:ℕ) (start:R.family.ref d ≤ i) (x:Wallet actors) (j:V) (v:R.family.label d) :
    let F:=R.family.labels.level d
    let y:=homes j
    let S:=R.family.localSection d
    let μ:=Next.Foundations.price G (max (W_).p.order (W_).p.power)
    let sale:=WilsonCenteredGalleryCapture.fare (W_).p S R.family.params weights ((J_).fire j)
      (∅:Finset V) (fun _=>0) {y} 0 account κ (R.alloy.B.a.clock.forcedAllowance i) μ
    ∃ q h:Coefficient F (R.family.side i per),
      q.Format y R.family.params (W_) ∧ q.remBound y (W_) κ sale ∧
      (∀U,q.density y S (W_) U=((value) (physical x) U).part ((J_).fire j)) ∧
      h.Format y R.family.params (W_) ∧ h.remBound y (W_) κ sale ∧
      h.x=v-q.x ∧ (∀z U,h.forced z U= -q.forced z U) ∧
      (∀U,h.density y S (W_) U=((W_).eval U:ℂ)*Extra.Histories.part S y (W_) U v-
        ((value) (physical x) U).part ((J_).fire j)) ∧
      ∀ probe:Probe G d,probe.2.val=0 → runProbe F probe q.x=
        ((W_).eval (1:configuration):ℂ)⁻¹*((value) (physical x) 1).part ((J_).fire j) := by
  intro F y S μ sale
  have point:(R.family.path.rep N per i).p=(W_).p:=
    (WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course hi cut.le).1
  have he:Readable R.family.params S (W_).p (R.family.side i per) μ:=by
    dsimp only [μ]
    rw [←point]
    exact ActualWilsonPrimaryPreparation.original R d N per i start cut.le
  have house (z:V)(inFire:z∈((J_).fire j).val):z=j:=Finset.mem_singleton.mp inFire
  have dom (z:V)(hz:z∈((J_).fire j).val):homes z∈({y}:Support (R.family.side i per)):=by
    rw [house z hz]
    exact Finset.mem_singleton_self _
  have near (z:V)(hz:z∈((J_).fire j).val):separation (homes z) y≤0:=by
    rw [house z hz]
    exact (Lattice.separation_self y).le
  have zero:∀z∈(∅:Finset V),homes z∈({y}:Support (R.family.side i per)):=by simp
  have empty:∀z∈(∅:Finset V),separation (homes z) y≤0:=by simp
  obtain ⟨q,form,paid,all,probe⟩:=WilsonCenteredReceivedAggregate.original R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P way simple late x ((J_).fire j) ∅
    (fun _=>0) {y} y (Finset.mem_singleton_self _) dom zero 0 near empty S R.family.params he
  simp only [Finset.sum_empty,sub_zero] at all probe
  have div:0<κ:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec i late |>.1
  let core:Coefficient F (R.family.side i per):=Extra.Histories.primary y v
  have cf:core.Format y R.family.params (W_):=Extra.Histories.primary_format v
  have cb:core.remBound y (W_) κ 0:=Extra.Histories.primary_rem v div
  let h:=Push.RelayDifference.combine core q
  refine ⟨q,h,form,paid,all,Push.RelayDifference.combo_format cf form,?_,rfl,?_,?_,probe⟩
  · simpa only [zero_add] using Push.RelayDifference.combo_cap cf form cb paid
  · intro z U
    change (0:ℂ)-q.forced z U=_
    exact zero_sub _
  · intro U
    rw [show h.density y S (W_) U=core.density y S (W_) U-q.density y S (W_) U from
      congrFun (Push.RelayDifference.combo_density cf form cb paid (course.1.walk i hi cut.le).truep.valid S) U,
      show core.density y S (W_) U=_ from Extra.Histories.primary_density S (W_) v U,all U]

end YM.Integration.WilsonOriginalAlternativeUnary
