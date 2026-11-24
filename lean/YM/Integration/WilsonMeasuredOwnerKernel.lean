import YM.Integration.WilsonMeasuredOwnerRank
import YM.Integration.WilsonSingleHardMarginal

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerKernel
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open MeasureTheory QuadraticLocal.Tint
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


local notation "input" => Ψ (i+1)
local notation "gallery" => Tint.Patrol.picture P.model P.input

include course cut in
/-- The original funded full density is integrable before extracting a signed
source face, including every retained old hard partner. -/
theorem integrable [Countable P.inputIndex] (x:Wallet actors) :
    Integrable (physical x) (prior G _) := by
  letI:=P.modelCount
  have costPos:=Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have paid:=P.issued.Waffle.converted costPos P.affordable
  have old:=Lamps.tenure _ P.w P.salary.positive P.regular
    (show (input).p.supportExponent ≤ (input).p.supportExponent+1+1 by linarith)
  obtain ⟨B,_⟩:=Tint.Campus.Investor.pays P.model P.input P.w P.salary.positive grades P.salary
    paid.breeze (show _ ≤ 2-P.rent from paid.fits.trans (by linarith [P.small]))
    ((mul_le_of_le_one_left (by positivity) paid.fits).trans paid.past) old P.forced
  rw [←P.represented x]
  exact QuadraticLocal.Tariff.integrable (Stock.census V) P.passport.origin P.w P.salary.positive
    (gallery) x (Travel.pays _ _ B) (input).p.exponent_pos.le
    (course.1.walk (i+1) (hi.trans i.le_succ) cut).truep.valid

include course cut in
theorem transition [Countable P.inputIndex] (x:Wallet actors) (s:(Stock.census V).Mode) (d:ℕ)
    (f:Config G (R.family.side (i+1) per)→ℂ) (issued:∀W,(physical x W).part s=f W) :
    GermGraph.transition (C:=R.family) d N per i f=((R.family.S.block i).val:ℂ)^d •
      fun U=>(LocalComparison.actualPush R.family N per i (physical x) U).part s := by
  have all:=integrable R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P x
  have field:(fun W=>(physical x W).part s)=f:=funext issued
  rw [←field]
  funext U
  apply congrArg ((fun z:ℂ=>((R.family.S.block i).val:ℂ)^d*z))
  exact (congrFun (MergeProof.Accent.push_get (R.family.path.levels.transition_mass ..) all s) U).symm

end YM.Integration.WilsonMeasuredOwnerKernel
