import YM.Integration.WilsonTrueProjectedDualHistory
import YM.Integration.WilsonTrueProjectedTransportedFare

/-! The elected nonbare Wilson course and its canonical stable gate
retain the exact upper-boundary factor, also for a dated single-column
invoice growing by a small power of the physical mesh ratio. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedOriginalReturn
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source
open Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open PhysicalNext Repeat Legato Graces Roost Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open WilsonTrueProjectedDualHistory WilsonTrueProjectedTransportedFare WilsonTrueProjectedCourse
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G)
local notation "𝓒" => R.family

theorem original (simple : G.Simple) (d order : ℕ) {δ γ ε : ℝ} (gap : δ < GermGraph.rate)
    (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ first : ℕ in atTop, ∀ m stop N p k : ℕ, m ≤ first → first ≤ stop → stop ≤ N →
    ∀ (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)),
    Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ →
    ∀ (F : Spaces R p) (template : ∀ j, store (𝓒) d p j) (price spare : ℕ → ℝ)
      (boundary M : ℝ), 0 ≤ M →
    (∀ j ≥ first, j < stop → F j =ᶠ[𝓝 1] value (C:=𝓒) d N p j (template j) ∧
      ∃ t, reads d N p j (template j) t) →
    (∀ j ≥ first, j < stop → WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F j (price j)) →
    (∀ j ≥ first, j < stop → WilsonTrueProjectedDualHistory.HardReturn R (d:=d) (N:=N) Ψ j (spare j)) →
    (∀ j ≥ first, j < stop → localBill R price spare j ≤
      (1-(3:ℝ)^(δ-GermGraph.rate))*(M*power R order j*growth (𝓒) δ first j)) →
    (∃ v, Full R (d:=d) (N:=N) Ψ F stop v boundary) →
    ∃ v, Full R (d:=d) (N:=N) Ψ F first v
      (Real.exp (-GermGraph.rate*((𝓒).S.scale stop-(𝓒).S.scale first))*boundary + M*power R order first) ∧
      (first < stop → measuring (𝓒) d N p first v = page (C:=𝓒) d p first (template first)) := by
  filter_upwards [ActualOneMarkGraphStep.gates R simple d hγ hε] with first gates
  intro m stop N p k mfirst inc top π₀ Γ Ψ course F template price spare boundary M hM models fresh old funds start
  obtain ⟨v,⟨q,h,r,B,paid,pn,hpaid,total,representation⟩,field⟩ :=
    WilsonTrueProjectedDualHistory.history R Ψ π₀ Γ course mfirst top F template price spare
      (fun j fj jb => (gates j fj p N (jb.trans_le top)).1.1)
      (fun j fj jb => (gates j fj p N (jb.trans_le top)).2)
      models fresh old boundary start first le_rfl inc
  have limit := scheduled R simple order gap hM inc boundary (localBill R price spare) funds
  exact ⟨v,⟨q,h,r,B,paid,pn,hpaid,total.trans limit,representation⟩,field⟩

end YM.Integration.WilsonTrueProjectedOriginalReturn
