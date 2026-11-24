import YM.Integration.WilsonTrueProjectedTwoCarrierStep
import YM.Integration.WilsonMeasuredOwnerIntegrable

/-! Close one actual nonbare appointment with the canonical stable field
and the separate hard numerator of its elected course. All comparisons of
the vacuum and reserved addresses are supplied by this course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedDualAppointment
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source
open Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open PhysicalNext Repeat Legato Graces Roost Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} (R : Run G) {d m i N p k : ℕ}
    (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j p))
    (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
local notation "𝓒" => R.family
local notation "σ" => (R.family.labels.level d).coeffSize
local notation "Q" => GermGraph.store R.family d p
local notation "V" => GermGraph.value (C:=R.family) d N p
local notation "Y" => GermGraph.calValues (C:=R.family) d N p
local notation "π" => GermGraph.page (C:=R.family) d p
local notation "X" => GermGraph.measuring R.family d N p
local notation "U" => GermGraph.transition (C:=R.family) d N p i
local notation "S" => R.family.localSection d
local notation "κ" => safety R.family

include course in
theorem original (start : m ≤ i) (hi : i < N) (hc : Opened (𝓒) d i p)
    {γ ε r B b u M : ℝ} (gate : Gate (𝓒) d N p i γ ε)
    (y : (𝓒).label d) (q h : Q (i+1)) (e z template : Q i)
    (fine : Config G ((𝓒).side (i+1) p) → ℂ) (lower : Config G ((𝓒).side i p) → ℂ)
    (seated : reads d N p (i+1) q r) (null : π (i+1) q=0)
    (hard : h.Format 0 (𝓒).params (Ψ (i+1)) ∧ h.remBound 0 (Ψ (i+1)) (κ (i+1)) B)
    (earned : e.Format 0 (𝓒).params (Ψ i) ∧ e.remBound 0 (Ψ i) (κ i) b ∧ σ e.x ≤ b)
    (heard : z.Format 0 (𝓒).params (Ψ i) ∧ z.remBound 0 (Ψ i) (κ i) u ∧ σ z.x ≤ u)
    (nearTemplate : lower =ᶠ[𝓝 1] V i template) (templateBill : reads d N p i template M)
    (input : Y (i+1) y = fine + (V (i+1) q + account h (Ψ (i+1))))
    (fresh : U fine = lower + e.density 0 S (Ψ i))
    (old : U (account h (Ψ (i+1))) = z.density 0 S (Ψ i)) :
    let mix := beside e z
    let loss := (factor (𝓒) i)^(-GermGraph.rate)
    let fit := fitting d N p i R.makes hc hi.le
    mix.Format 0 (𝓒).params (Ψ i) ∧ mix.remBound 0 (Ψ i) (κ i) (b+u) ∧
    ∃ (next : Q i) (feed : (𝓒).label d),
      reads d N p i next (loss*r+(1+4*stock (𝓒) i)*(b+u)) ∧ π i next=0 ∧
      σ (X i feed) ≤ ε*r*loss ∧ X i y-π i template = X i feed + π i (soft mix) ∧
      V i next + account mix (Ψ i) = Y i (fit.symm (π i template))-lower := by
  intro mix loss fit
  obtain ⟨point,owners,_⟩ := WilsonMeasuredCourseQuietSlots.selected R π₀ Γ Ψ course start hi.le
  have quiet := (course.1.walk i start hi.le).view
  have law := (course.1.walk i start hi.le).truep.valid
  have held := WilsonMeasuredOwnerIntegrable.original R π₀ Γ Ψ course (start.trans i.le_succ) hi
    S (𝓒).params 0 h hard.1 hard.2
  have booked : mix.Format 0 (𝓒).params (Ψ i) ∧ mix.remBound 0 (Ψ i) (κ i) (b+u) :=
    presentation earned.1 earned.2.1 heard.1 heard.2.1
  obtain ⟨good,price,_,_⟩ := WilsonMeasuredOnlyHard.original mix ((𝓒).path.rep N p i) (Ψ i)
    point quiet owners S (𝓒).params 0 (κ i) (b+u) booked.1 booked.2
  have amount : σ (soft mix).x ≤ b+u := by
    change σ (beside e z).x ≤ b+u
    rw [reckon]
    exact (Size.add ((𝓒).labels.level d) e.x z.x).trans (add_le_add earned.2.2 heard.2.2)
  have cap := control_page R.makes hc hi.le (soft mix) ⟨good,price⟩ amount
  obtain ⟨g,w,next,feed,paid,pn,pf,payout,out⟩ := WilsonTrueProjectedTwoCarrierStep.original
    R.makes hi hc gate (Ψ i) (Ψ (i+1)) point owners quiet law y q h e z template fine lower
    seated null ⟨earned.1,earned.2.1⟩ ⟨heard.1,heard.2.1⟩ nearTemplate templateBill held input fresh old cap
  refine ⟨g,w,next,feed,?_,pn,pf,payout,out⟩
  rw [show loss*r+(1+4*stock (𝓒) i)*(b+u) = loss*r+(b+u+2*stock (𝓒) i*(2*(b+u))) by ring]
  exact paid

end YM.Integration.WilsonTrueProjectedDualAppointment
