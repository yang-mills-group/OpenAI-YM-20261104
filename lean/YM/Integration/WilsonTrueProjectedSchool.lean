import YM.Integration.WilsonTrueProjectedUpperSource
import YM.Integration.WilsonMeasuredOwnerStrictReturn

/-! The original receiving posts pay every old compulsory return on their
own representation. Only the fresh signed comparison and the registered
initial source occur in the quantitative estimate. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedSchool
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof Org QuadraticLocal QuadraticLocal.Advent
open QuadraticLocal.Mentor QuadraticLocal.Advent.Oak
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open PhysicalNext Repeat Legato Graces Roost Pert.Asymptotics Push Push.PriceCompiler
open RemainderComparison QuadraticLocal.Affinity ConnectedActivityE6
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonTrueProjectedDualHistory WilsonTrueProjectedTransportedFare WilsonTrueProjectedCourse
open scoped Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G)
local notation "𝓒" => R.family

/-- The original accountable posts may be selected for the actual submitted
fields after fixing the common physical course. The date threshold precedes
both regulators, all such posts and every member of their old hard accounts. -/
theorem original (simple : G.Simple) (d target q k order shelf seats : ℕ)
    (menu : WilsonMeasuredRankedMenu.Menu R d)
    (slow : ∀j, ((R.family.S.block j).val : ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (accuracy : 2*d+5 ≤ q) (deep : 2*(q+4+1)+8 ≤ order) (aged : q+4+4 ≤ 3*k+2)
    (size : seats ≤ Burn.horizon k+2) {δ γ ε : ℝ} (gap : δ < GermGraph.rate)
    (hγ : 0 < γ) (hε : 0 < ε)
    {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
    [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
    (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ) (ticket : V) :
    ∀ᶠ first : ℕ in atTop, ∀ m stop N per : ℕ, m ≤ first → first ≤ stop → stop ≤ N →
    ∀ (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G ((𝓒).side j per))
      (φ : ℕ → ℕ) (books : Mentor.Offices.Books D R.rolls Q φ)
      (ahead : Mentor.Forecast D R.rolls Q φ books)
      (scroll : VowsR.LawScroll G φ),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → VowsR.Chamber scroll R.kit D Q books →
    Pass D Q R.alloy R.kit → MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay →
    WayStation R.kit →
    (∀ j ≥ first, j < stop → ((𝓒).path.levels.budget j).supportExponent ≤ 100) →
    (∀ j ≥ first, j < stop → ∃ physical : Wallet actors → Config G ((𝓒).side (j+1) per) →
          Marker.Poly (Stock.census V), ∃ hj : m ≤ j,
       Nonempty (WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
         order shelf seats j hj physical)) →
    ∀ (F : Spaces R per) (price : ℕ → ℝ) (boundary M : ℝ), 0 ≤ M →
    (∀ j ≥ first, j < stop → WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F j (price j)) →
    (∀ j ≥ first, j < stop → (2+4*stock (𝓒) j)*price j ≤
      (1-(3:ℝ)^(δ-GermGraph.rate))*(M*power R target j*growth (𝓒) δ first j)) →
    WilsonTrueProjectedUpperSource.Launch R d N Ψ F stop boundary →
    ∃ v, Full R (d:=d) (N:=N) Ψ F first v
      (Real.exp (-GermGraph.rate*((𝓒).S.scale stop-(𝓒).S.scale first))*boundary
        + M*power R target first) ∧
      (first < stop → ∃ (s : store (𝓒) d per first) (a : ℝ), reads d N per first s a ∧
         F first =ᶠ[𝓝 1] value (C:=𝓒) d N per first s ∧
         measuring (𝓒) d N per first v = page (C:=𝓒) d per first s) := by
  obtain ⟨onset,ready⟩ := eventually_atTop.mp
    (WilsonMeasuredOwnerAppointments.original R simple d q k order shelf menu slow prepared accuracy deep aged)
  filter_upwards [Filter.eventually_ge_atTop onset,
    ActualOneMarkGraphStep.gates R simple d hγ hε,
    WilsonTrueProjectedReconstruction.original R simple d target gap hγ hε] with first begins gates run
  intro m stop N per mfirst inc top hk D Q π Γ Ψ φ books ahead scroll course chamber pass hospital
    way fixed posts F price boundary M hM fresh fee launch
  have hard (j : ℕ) (fj : first ≤ j) (js : j < stop) :
      HardReturn R (d:=d) (N:=N) Ψ j 0 := by
    obtain ⟨physical,hj,⟨P⟩⟩ := posts j fj js
    intro h B hb
    obtain ⟨z,u,zp,head,push,charge⟩ := WilsonMeasuredOwnerStrictReturn.original R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats hj physical P d ticket (js.trans_le top) simple course scroll chamber pass
      hospital size way menu slow prepared (fixed j fj js) q deep aged accuracy
      (ready j (begins.trans fj)) h B hb
    refine ⟨z,u,zp,head,push,?_⟩
    rw [add_zero]
    exact charge
  have openTop := (gates stop inc per (stop+1) (Nat.lt_succ_self stop)).1.1
  have start := WilsonTrueProjectedUpperSource.admitted R Ψ course (mfirst.trans inc) top openTop F launch
  refine run m stop N per k mfirst inc top π Γ Ψ course F price (fun _ => 0) boundary M hM fresh hard ?_ start
  intro j fj js
  simpa only [localBill,add_zero] using fee j fj js

end YM.Integration.WilsonTrueProjectedSchool
