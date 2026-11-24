import YM.Integration.WilsonTrueProjectedOriginalReturn
import YM.Integration.WilsonTrueProjectedGermIncome

/-! Reconstruct the receiving germ directly from the original signed
one-block comparisons. The finite qualitative representation is selected
after each cutoff and incurs no tariff in the uniform quantitative bound. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedReconstruction
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source
open Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open PhysicalNext Repeat Legato Graces Roost Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open WilsonMeasuredCoefficientTransport WilsonTrueProjectedDualHistory WilsonTrueProjectedGermIncome
open WilsonTrueProjectedTransportedFare WilsonTrueProjectedCourse
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d N p i m k : ℕ}
local notation "𝓒" => R.family
local notation "Q" => store R.family d p
local notation "V" => value (C:=R.family) d N p
local notation "Y" => calValues (C:=R.family) d N p
local notation "S" => R.family.localSection d

theorem extend (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    (start : m ≤ i) (hi : i < N) (hc : Opened (𝓒) d i p) {γ ε : ℝ}
    (gate : Gate (𝓒) d N p i γ ε) (F : Spaces R p) {b t bound : ℝ} (v : (𝓒).label d)
    (upper : Full R (d:=d) (N:=N) Ψ F (i+1) v bound)
    (fresh : WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i b)
    (old : HardReturn R (d:=d) (N:=N) Ψ i t) :
    Realizes (C:=𝓒) d N p i (F i) ∧ ∃ x B, Full R (d:=d) (N:=N) Ψ F i x B := by
  have germ := on_course R π₀ Γ Ψ course start hi hc gate F v upper fresh old
  refine ⟨germ,?_⟩
  obtain ⟨template,M,base,near⟩ := germ
  obtain ⟨q,h,r,B,paid,pn,hpaid,_,inlet⟩ := upper
  obtain ⟨e,eprom,ex,fstep⟩ := fresh
  obtain ⟨z,u,zprom,zx,hstep,_⟩ := old h B hpaid
  obtain ⟨fmt,fee,s,_,sr,sz,_,_,out⟩ := WilsonTrueProjectedDualAppointment.original
    R π₀ Γ Ψ course start hi hc gate v q h e z template (F (i+1)) (F i) paid pn hpaid
    ⟨eprom.1,eprom.2,ex⟩ ⟨zprom.1,zprom.2,zx⟩ near base (by rw [inlet]; abel) fstep hstep
  exact ⟨_,_,s,beside e z,_,_,sr,sz,⟨fmt,fee⟩,le_rfl,out⟩

theorem original (simple : G.Simple) (d order : ℕ) {δ γ ε : ℝ} (gap : δ < GermGraph.rate)
    (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ first : ℕ in atTop, ∀ m stop N p k : ℕ, m ≤ first → first ≤ stop → stop ≤ N →
    ∀ (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)),
    Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ →
    ∀ (F : Spaces R p) (price spare : ℕ → ℝ) (boundary M : ℝ), 0 ≤ M →
    (∀ j ≥ first, j < stop → WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F j (price j)) →
    (∀ j ≥ first, j < stop → HardReturn R (d:=d) (N:=N) Ψ j (spare j)) →
    (∀ j ≥ first, j < stop → localBill R price spare j ≤
      (1-(3:ℝ)^(δ-GermGraph.rate))*(M*power R order j*growth (𝓒) δ first j)) →
    (∃ v, Full R (d:=d) (N:=N) Ψ F stop v boundary) →
    ∃ v, Full R (d:=d) (N:=N) Ψ F first v
      (Real.exp (-GermGraph.rate*((𝓒).S.scale stop-(𝓒).S.scale first))*boundary + M*power R order first) ∧
      (first < stop → ∃ (s : store (𝓒) d p first) (a : ℝ), reads d N p first s a ∧
         F first =ᶠ[𝓝 1] value (C:=𝓒) d N p first s ∧
         measuring (𝓒) d N p first v = page (C:=𝓒) d p first s) := by
  classical
  filter_upwards [ActualOneMarkGraphStep.gates R simple d hγ hε,
    WilsonTrueProjectedOriginalReturn.original R simple d order gap hγ hε] with first gates run
  intro m stop N p k mfirst inc top π₀ Γ Ψ course F price spare boundary M hM fresh old funds init
  have available (j : ℕ) (fj : first ≤ j) (jb : j ≤ stop) :
      (∃ v B, Full R (d:=d) (N:=N) Ψ F j v B) ∧ (j < stop → Realizes (C:=𝓒) d N p j (F j)) := by
    induction jb using Nat.decreasingInduction with
    | self =>
      obtain ⟨x,hx⟩ := init
      exact ⟨⟨x,boundary,hx⟩,by omega⟩
    | of_succ j jb ih =>
      obtain ⟨⟨x,B,hx⟩,_⟩ := ih (by omega)
      obtain ⟨openj,gate⟩ := gates j fj p N (jb.trans_le top)
      obtain ⟨germ,paid⟩ := extend R π₀ Γ Ψ course (mfirst.trans fj) (jb.trans_le top) openj.1
        gate F x hx (fresh j fj jb) (old j fj jb)
      exact ⟨paid,fun _ => germ⟩
  let witness (j : ℕ) (owns : first ≤ j ∧ j < stop) := (available j owns.1 owns.2.le).2 owns.2
  let filed (j : ℕ) := if owns : first ≤ j ∧ j < stop then (witness j owns).choose
    else ((𝓒).factory d N p).entries j 0
  have room (j : ℕ) (fj : first ≤ j) (jb : j < stop) :
      F j =ᶠ[𝓝 1] value (C:=𝓒) d N p j (filed j) ∧ ∃ a, reads d N p j (filed j) a := by
    have owns : first ≤ j ∧ j < stop := ⟨fj,jb⟩
    obtain ⟨a,h,f⟩ := (witness j owns).choose_spec
    simpa only [filed,dif_pos owns] using And.intro f (Exists.intro a h)
  obtain ⟨v,total,coord⟩ := run m stop N p k mfirst inc top π₀ Γ Ψ course F filed
    price spare boundary M hM room fresh old funds init
  refine ⟨v,total,?_⟩
  intro live
  obtain ⟨f,a,h⟩ := room first le_rfl live
  exact ⟨filed first,a,h,f,coord live⟩

end YM.Integration.WilsonTrueProjectedReconstruction
