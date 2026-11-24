import YM.Integration.WilsonMeasuredOwnerBlank
import YM.Integration.WilsonMeasuredRankedFiledPrimary
import YM.Integration.WilsonCapturedPrimarySection

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerRank
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
open ProjectorNext.Equivariance

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

local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "debt" => (⟨P.output.old,P.output.hard⟩ :
  Gallery (Wallet actors) P.outputIndex homes (Ψ i) (Stock.census V))
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta


variable (rank:ℕ)
local notation "F₀" => R.family.labels.level rank
local notation "S₀" => R.family.localSection rank
local notation "Y₀" => R.family.params
local notation "μ₀" => Next.Foundations.price G (max (Ψ i).p.order (Ψ i).p.power)
local notation "wp" => R.alloy.B.a.clock.forcedAllowance i

include course cut in
/-- The whole original push from a zero-cost analytic inlet, as one ranked
coefficient on its measured outgoing representation and at its actual origin. -/
theorem original [Nonempty V] (cost:P.cost=0) (way:WayStation R.kit) (simple:G.Simple)
    (late:WilsonCenteredCaptureClock.first R simple ≤ i) (p q:ℕ)
    (ready:q ≤ R.alloy.B.a.clock.J i) (deep:2*(p+1)+8 ≤ order) (aged:p+4 ≤ 3*k+2)
    {ε:ℝ} (ep:0<ε)
    (opening:WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (date:R.t rank ≤ i) (x:Wallet actors) (v:V) :
    let y:=homes v
    let u:=(Stock.census V).fire v
    let E:=(8*Ω^P.op.count)*P.rent+ε*gf^p
    let b:=WilsonOlderSignedSingletonFare.fare (Ψ i).p S₀ Y₀ weights u 1 {y} 0
      ((Ω^6)⁻¹*E) (βhat^(-(q:ℝ))*κ) κ wp (R.family.path.levels.params i).columns
    let r:=4*E
    let s:=(factor Y₀ S₀ (Ψ i).p.supportExponent μ₀*((Ψ i).p.order.factorial:ℝ))*r
    let c:=((Ψ i).p.order.factorial:ℝ)*r+s+P.w v*(Ψ i).p.mass ((S₀).footprint y) (μ₀*(s/P.w v))
    ∃ A:Coefficient F₀ (R.family.side i per), A.Format y Y₀ (Ψ i) ∧ A.remBound y (Ψ i) κ b ∧
      (∀U,A.density y S₀ (Ψ i) U=(LocalComparison.actualPush R.family N per i (physical x) U).part u) ∧
      (F₀).coeffSize A.x ≤ 2*(r+s)/P.w v+WilsonMeasuredRankedGerm.wrapCost F₀ Y₀ *
        wraps (Ψ i).p (R.family.side i per)*(b+c/P.w v) := by
  intro y u E b r s c
  letI:=P.outputCount
  letI:Nonempty (Wallet actors):=⟨x⟩
  have tr:=(course.1.walk i hi cut.le).truep
  have measured:=(R.makes.wilson.represents N per i cut.le).vac
  have shared:(Ψ i).p=(R.family.path.rep N per i).p:=tr.point.trans measured.symm
  have dims:=dimensions rank N per i R.makes date cut.le
  have read:Readable Y₀ S₀ (Ψ i).p (R.family.side i per) μ₀:=by
    rw [shared]
    exact ActualWilsonPrimaryPreparation.original R rank N per i date cut.le
  have first:rank ≤ (Ψ i).p.order:=by rw [shared];exact dims.1
  have second:rank ≤ (Ψ i).p.power:=by rw [shared];exact dims.2
  have cash:=(WilsonCapturedPrimarySection.original R date (Ψ i) tr.point).1
  obtain ⟨A,shape,paid,profile⟩:=WilsonOlderSignedOneMarkStep.original R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P way simple late p q ready deep aged ep opening
    x v {y} y (Finset.mem_singleton_self _) (Finset.mem_singleton_self _) 0 (YM.Lattice.separation_self y).le S₀ Y₀ cash
  have zero:=WilsonMeasuredOwnerBlank.original R hk D Q π Γ Ψ books hi ahead actors pieces grades order shelf seats physical P cost x
  have zp (s : (Stock.census V).Mode) : (0:Poly (Stock.census V)).part s=0:=rfl
  have field (U):A.density y S₀ (Ψ i) U=(LocalComparison.actualPush R.family N per i (physical x) U).part u:=by
    simpa only [u,zero U,zp,mul_zero,sub_zero] using profile U
  have inc:=WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged ep opening
  have reg:(debt).E.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) E:=by
    simpa only [add_assoc,one_add_one_eq_two] using P.output.old.loan_monotone P.issued.tuition inc
  have signed:A.density y S₀ (Ψ i)=ᶠ[𝓝 1] fun U=>((Ψ i).eval U:ℂ)*((debt).E.log x U).part u :=by
    filter_upwards [Juniper.Caret.flat_flags (R.family.side i per) (Ψ i).p.threshold (Ψ i).p.threshold_pos] with U clear
    have lit:=WilsonMeasuredRankedLights.unmasked lamps x U clear
    change (lamps).log x U=Spill.Foundry.uncut student oldG x U at lit
    have old:=WilsonMeasuredRankedLights.original R hk D Q π Γ Ψ books hi ahead actors pieces grades order shelf seats
      physical P x v U clear
    rw [field,old,←lit,zero U]
    simp [u]
  have res:=WilsonMeasuredRankedGerm.regular debt P.issued.earning.positive
    (Real.sqrt_pos.mpr (Extra.Histories.forcedPos R.family.path.levels i)) tr.valid.labels.forced
    reg P.issued.paidForce x v Y₀ S₀ read (R.makes.places rank i per date) first second
    (sections_visit R.makes date y) A shape paid signed
  exact ⟨A,shape,paid,field,res⟩

end YM.Integration.WilsonMeasuredOwnerRank
