import YM.Integration.WilsonTrueProjectedWindowSchool

/-! The transported coordinate is the intrinsic germ of the submitted
field. This includes restart dates and actual independently filed pupils
on the elected Wilson representation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedIntrinsic
open Filter Finset Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open PhysicalNext Repeat Legato Graces Roost
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonTrueProjectedDualHistory WilsonTrueProjectedGermIncome
open scoped Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d m N p k j : ℕ}
local notation "𝓒" => R.family
local notation "X" => measuring (𝓒) d N p
local notation "π" => page (C:=𝓒) d p
local notation "V" => value (C:=𝓒) d N p
local notation "Y" => calValues (C:=𝓒) d N p
local notation "Q" => store (𝓒) d p
local notation "S" => (𝓒).localSection d

theorem original {Ψ : ∀ l, Rep G ((𝓒).side l p)} {F : Spaces R p} {v : (𝓒).label d} {cap : ℝ} (hr : (𝓒).ref d ≤ j) (hn : j ≤ N)
    (bank : Full R (d:=d) (N:=N) Ψ F j v cap) (row : Q j) {allowance : ℝ}
    (inscribed : reads d N p j row allowance) (same : F j =ᶠ[𝓝 1] V j row) : X j v = π j row := by
  obtain ⟨q,h,r,B,qs,qn,hs,_,balance⟩ := bank
  have joint : reads d N p j (beside q row) (r+allowance) := presentation qs.1 qs.2 inscribed.1 inscribed.2
  have numerator : V j (beside q row) = V j q+V j row :=
    plus (R.makes.wilson.represents N p j hn).good qs.2 inscribed.2 S
  have clean : Y j v =ᶠ[𝓝 1] V j (beside q row) := by
    rw [numerator]
    filter_upwards [WilsonTrueProjectedTwoCarrierStep.clear (Ψ j) h hs.1,same] with U quiet filed
    have reading := congrFun balance U
    change V j q U + account h (Ψ j) U = Y j v U - F j U at reading
    change account h (Ψ j) U = 0 at quiet
    rw [quiet,add_zero,filed] at reading
    exact (sub_eq_iff_eq_add.mp reading.symm)
  have coord := same_page R.makes hn hr (entryOk d N p j R.makes hr hn v) joint clean
  change X j v = π j (beside q row) at coord
  simpa only [addPage d N p j q row R.makes hr hn qs inscribed,qn,zero_add] using coord

theorem filed {Ψ : ∀ l, Rep G ((𝓒).side l p)} {F : Spaces R p} {v : (𝓒).label d} {cap : ℝ} (hr : (𝓒).ref d ≤ j) (hn : j ≤ N)
    (bank : Full R (d:=d) (N:=N) Ψ F j v cap) :
    ∃ (s : Q j) (r : ℝ), reads d N p j s r ∧ F j =ᶠ[𝓝 1] V j s ∧ X j v = π j s := by
  have income := bank
  obtain ⟨q,h,_,_,qs,_,hs,_,balance⟩ := income
  have actual : F j =ᶠ[𝓝 1] Y j v + -(V j q) := by
    filter_upwards [WilsonTrueProjectedTwoCarrierStep.clear (Ψ j) h hs.1] with U quiet
    have reading := congrFun balance U
    change V j q U + account h (Ψ j) U = Y j v U - F j U at reading
    change account h (Ψ j) U = 0 at quiet
    rw [quiet,add_zero] at reading
    change F j U = Y j v U + -(V j q U)
    rw [reading]
    abel
  obtain ⟨s,r,sr,report⟩ := WilsonTrueProjectedGermIncome.add R.makes hn
    (WilsonTrueProjectedGermIncome.column R.makes hr hn v)
    (WilsonTrueProjectedGermIncome.neg (WilsonTrueProjectedGermIncome.word qs))
  exact ⟨s,r,sr,actual.trans report,original R hr hn bank s sr (actual.trans report)⟩

theorem unique {Ψ : ∀ l, Rep G ((𝓒).side l p)} {F : Spaces R p} {v : (𝓒).label d} {cap : ℝ} (hc : Opened (𝓒) d j p) (hn : j ≤ N)
    (bank : Full R (d:=d) (N:=N) Ψ F j v cap)
    {Ξ : ∀ l, Rep G ((𝓒).side l p)} {K : Spaces R p} {w : (𝓒).label d} {B : ℝ}
    (other : Full R (d:=d) (N:=N) Ξ K j w B) (germ : F j =ᶠ[𝓝 1] K j) : v = w := by
  obtain ⟨row,_,paid,record,witness⟩ := filed R hc.post hn other
  have same := (original R hc.post hn bank row paid (germ.trans record)).trans witness.symm
  exact (fitting d N p j R.makes hc hn).injective same

theorem issued {Ψ : ∀ l, Rep G ((𝓒).side l p)} {F : Spaces R p} {v : (𝓒).label d} {cap : ℝ} (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    (hj : m ≤ j) (hn : j ≤ N) (hr : (𝓒).ref d ≤ j)
    (bank : Full R (d:=d) (N:=N) Ψ F j v cap) (row : Q j) {B : ℝ}
    (paid : Admitted R (d:=d) Ψ j row B)
    (record : F j =ᶠ[𝓝 1] row.density 0 S (Ψ j)) : X j v = π j (soft row) := by
  obtain ⟨point,owners,_⟩ := WilsonMeasuredCourseQuietSlots.selected R π₀ Γ Ψ course hj hn
  obtain ⟨fmt,bill,eq,_⟩ := WilsonMeasuredOnlyHard.original row ((𝓒).path.rep N p j) (Ψ j) point
    (course.1.walk j hj hn).view owners S (𝓒).params 0 (safety (𝓒) j) B paid.1 paid.2
  apply original R hr hn bank (soft row) ⟨fmt,bill⟩
  apply record.trans
  filter_upwards [WilsonTrueProjectedTwoCarrierStep.clear (Ψ j) row paid.1] with U clear
  change account row (Ψ j) U = 0 at clear
  simpa only [clear,add_zero] using eq U

end YM.Integration.WilsonTrueProjectedIntrinsic
