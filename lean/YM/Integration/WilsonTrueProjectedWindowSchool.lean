import YM.Integration.WilsonTrueProjectedPhysicalWindow

/-! One physical school pays the complete exceptional input on every date
of the finite measured corridor. The upper coordinate is the submitted one. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedWindowSchool
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

theorem original (simple : G.Simple) (d q k order shelf seats : ℕ)
    (menu : WilsonMeasuredRankedMenu.Menu R d)
    (slow : ∀j, ((R.family.S.block j).val : ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (accuracy : 2*d+5 ≤ q) (deep : 2*(q+4+1)+8 ≤ order) (aged : q+4+4 ≤ 3*k+2)
    (size : seats ≤ Burn.horizon k+2)
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
    ∀ (F : Spaces R per) (price : ℕ → ℝ) (cap : ℝ) (y : (𝓒).label d), 0 ≤ cap →
    (∀ j ≥ first, j < stop → WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F j (price j)) →
    (∀ j ≥ first, j < stop → (2+4*stock (𝓒) j)*price j ≤ (1-(3:ℝ)^(-GermGraph.rate))*cap) →
    (F stop = calValues (C:=𝓒) d N per stop y ∨
      (stop=N ∧ ∃ raw : (𝓒).label d,
        y=((𝓒).labels.level d).scaled ((𝓒).path.levels.clock.threshold N) raw ∧
        ∀ W,F N W=((Ψ N).eval W:ℂ)*((𝓒).localSection d).places raw 0 W)) →
    ∃ v, Full R (d:=d) (N:=N) Ψ F first v cap ∧
      ((𝓒).labels.level d).coeffSize (measuring (𝓒) d N per first y-measuring (𝓒) d N per first v) ≤
        4*((𝓒).S.a first/(𝓒).S.a stop)^(d+2)*cap ∧
      (first < stop → ∃ (s : store (𝓒) d per first) (a : ℝ), reads d N per first s a ∧
         F first =ᶠ[𝓝 1] value (C:=𝓒) d N per first s ∧
         measuring (𝓒) d N per first v = page (C:=𝓒) d per first s) := by
  obtain ⟨onset,ready⟩ := eventually_atTop.mp
    (WilsonMeasuredOwnerAppointments.original R simple d q k order shelf menu slow prepared accuracy deep aged)
  filter_upwards [Filter.eventually_ge_atTop onset,ActualOneMarkGraphStep.gates R simple d
    (γ:=1) (ε:=1) zero_lt_one zero_lt_one] with first begins gates
  intro m stop N per mfirst inc top hk D Q π Γ Ψ φ books ahead scroll course chamber pass hospital
    way fixed posts F price cap y capPos fresh fee launch
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
  have initial : Full R (d:=d) (N:=N) Ψ F stop y 0 := by
    rcases launch with head | ⟨rfl,raw,rfl,head⟩
    · exact WilsonTrueProjectedUpperSource.matched R Ψ course openTop.post (mfirst.trans inc) top F y head
    · exact WilsonTrueProjectedUpperSource.bare R Ψ course openTop.post (mfirst.trans inc) F raw head
  apply WilsonTrueProjectedPhysicalWindow.original R π Γ Ψ course mfirst inc top (γ:=1) (ε:=1) le_rfl
    (gates first le_rfl per (first+1) (Nat.lt_succ_self first)).1.1
    (fun j fj js => (gates j fj per N (js.trans_le top)).1.1)
    (fun j fj js => (gates j fj per N (js.trans_le top)).2)
    F price (fun _ => 0) fresh hard y 0 cap initial capPos capPos
  intro j fj js
  simpa only [localBill,add_zero] using fee j fj js

end YM.Integration.WilsonTrueProjectedWindowSchool
