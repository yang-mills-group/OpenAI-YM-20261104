import YM.Integration.WilsonMeasuredHardWalletBorn
import YM.Integration.WilsonReceivedForcedExit

/-! The genuine fired face of a received physical program, before every earlier
integration, and the native charge on its very same complete returned hard family. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredReturnedHardField
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)


variable (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor physical)
open Progress.DirectedRecipe QuadraticLocal.Tint
open Source Labels Extra.Trajectories Extra.Histories Comparison.RG02.Cumulants
open Push Push.Local Push.PriceCompiler AnalyticBridge VerifiedReset RemainderComparison
local notation "gs" => Coat.gStep (Ψ (i+1)).beta
local notation "model" => Oak.student (n:=per) R hk D Q π Γ books floor P.op P.lesson ahead actors
  P.model order P.voter
local notation "gallery" => Tint.Patrol.report model P.output gs
local notation "origins" => (P.passport.coarser (R.family.path.levels.clock.op i per).ratio).origin
local notation "heat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "J" => Stock.census V

theorem original (live:i<N) (way:WayStation R.kit)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (q:ℕ)
    (active:q+6*seats≤R.alloy.B.a.clock.J i) {d:ℕ} {F:Frame G d}
    (S:SectionData F) (Y:Hol G) (x:Wallet actors) (v:V) :
    let h:=WilsonMeasuredSingletonForce.row (F:=F) P.output.hard x v
    h.Format (origins v) Y (Ψ i) ∧ h.remBound (origins v) (Ψ i) κ ((P.w v)⁻¹*heat^(-(q:ℝ))) ∧
    h.x=0 ∧ h.regular=0 ∧ (∀j U,h.forced j U=(P.output.hard.hard x j U).part ((J).fire v)) ∧
    ∀U, (LocalComparison.actualPush R.family N per i (physical x) U).part ((J).fire v) =
      ((Ψ i).eval U:ℂ)*((gallery).E.log x U).part ((J).fire v)+h.density (origins v) S (Ψ i) U :=by
  have cap:=WilsonReceivedForcedExit.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    floor physical P live way course q active
  have pos : 0<κ := Real.sqrt_pos.2 (allowance_pos R.family.path.levels.clock i)
  have heatpos : 0≤heat := zero_le_one.trans (R.alloy.B.a.fits.delayed _).le
  have pay : P.output.hard.Paid P.w (Ψ i).p.B (Ψ i).p.supportExponent (κ*heat^(-(q:ℝ))) :=by
    rw [mul_comm];exact cap
  obtain ⟨fmt,rem,x0,r0,each,onField⟩:=WilsonMeasuredHardWalletBorn.original P.output.hard P.w
    P.salary.positive S Y x v pos (Real.rpow_nonneg heatpos _) pay
  refine ⟨fmt,rem,x0,r0,each,?_⟩
  intro U
  have actual:=congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades order
    shelf seats i floor physical P x) U
  have hard:=WilsonMeasuredHardWalletBorn.summable P.output.hard P.w P.salary.positive (Ψ i).p.exponent_pos.le cap x U
  let A:=(gallery)
  let l:=A.E.log x U
  have zero:l.part (J).quiet=0:=by
    by_cases summ:Summable (fun j=>A.E.frame j x U)
    · exact Lamps.quiet_of_hasSum x U summ
    · simp [l,Lamps.log,tsum_eq_zero_of_not_summable summ]
  have regular:(Poly.pass l).part ((J).fire v)=l.part ((J).fire v) :=by
    rw [←lamp v _ (Poly.pass_part l zero),Comparison.RG02.Cumulants.connected_pass zero]
  have vacuum:=(Hard.packet_of_quiet A.K x U hard)
  change (A.gas x U).part (J).quiet=((Ψ i).activities.gas (Ψ i).p U:ℂ) at vacuum
  rw [actual,onField U]
  change (A.density x U).part ((J).fire v)=((Ψ i).eval U:ℂ)*l.part ((J).fire v)+
    (Real.exp ((Ψ i).exponent U):ℂ)*(A.gas x U).part ((J).fire v)
  simp only [Gallery.density,Poly.part_smul,Multi.first_mul]
  rw [regular,Poly.pass_part l zero,vacuum,RG.Rep.eval,Complex.ofReal_mul]
  dsimp [l]
  ring_nf
  ac_rfl

end YM.Integration.WilsonMeasuredReturnedHardField
