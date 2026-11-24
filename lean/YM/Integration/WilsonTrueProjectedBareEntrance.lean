import YM.Integration.WilsonTrueProjectedReconstruction

/-! Start from a registered group-field coefficient on its actual
incoming representation. The upper boundary price includes the true
primary and one hard divisor. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedBareEntrance
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source
open Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open PhysicalNext Repeat Legato Graces Roost Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport WilsonTrueProjectedDualHistory
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d m j N p k : ℕ}
local notation "𝓒" => R.family
local notation "σ" => (R.family.labels.level d).coeffSize
local notation "Q" => store R.family d p
local notation "V" => value (C:=R.family) d N p
local notation "Y" => calValues (C:=R.family) d N p
local notation "π" => page (C:=R.family) d p
local notation "S" => R.family.localSection d
local notation "κ" => safety R.family
theorem original (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ i, RG.Rep G ((𝓒).side i p)) (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    (start : m ≤ j) (hj : j ≤ N) (hc : Opened (𝓒) d j p)
    (F : Spaces R p) (a : Q j) {B : ℝ}
    (ad : Admitted R Ψ j a B) (coordinate : σ a.x ≤ B) (printed : F j = a.density 0 S (Ψ j)) :
    ∃ v, Full R (d:=d) (N:=N) Ψ F j v ((2+4*stock (𝓒) j)*B) := by
  let h := stretch (-1) a
  have ha : Admitted R Ψ j h B := by
    refine ⟨stretch_format _ ad.1,?_⟩
    simpa using stretch_rem (-1) ad.2
  have orig : h.density 0 S (Ψ j) = -F j := by
    rw [printed]
    funext W
    change (stretch (-1) a).density 0 S (Ψ j) W = -_
    rw [stretch_density]
    simp
  obtain ⟨point,owners,_⟩ := WilsonMeasuredCourseQuietSlots.selected R π₀ Γ Ψ course start hj
  have quiet := (course.1.walk j start hj).view
  obtain ⟨fmt,rem,identity,_⟩ := WilsonMeasuredOnlyHard.original h ((𝓒).path.rep N p j) (Ψ j)
    point quiet owners S (𝓒).params 0 (κ j) B ha.1 ha.2
  have paid : reads d N p j (soft h) B := ⟨fmt,rem⟩
  have unit : σ (soft h).x ≤ B := by
    change σ ((-1:ℂ) • a.x) ≤ B
    simpa only [Size.smul,norm_neg,norm_one,one_mul] using coordinate
  have price := control_page R.makes hc hj (soft h) paid unit
  obtain ⟨z,x,bill,proj,breakdown,_⟩ := fresh_split0 R.makes hc hj (soft h) paid
  have joined : h.density 0 S (Ψ j) = V j (soft h)+account h (Ψ j) := funext identity
  have negative : Y j (-x) = -(Y j x) :=
    eq_neg_of_add_eq_zero_left (negative_cal R.makes hc hj x)
  refine ⟨-x,⟨z,h,_,B,bill,proj,ha,?_,?_⟩⟩
  · have stockNonnegative : 0 ≤ 2*stock (𝓒) j := mul_nonneg zero_le_two
      (zero_le_one.trans (stage (𝓒) j).columns_ge)
    calc
      _ ≤ (B+2*stock (𝓒) j*(2*B))+B :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left price stockNonnegative)) le_rfl
      _ = _ := by ring
  · have balance : -F j = (V j z+Y j x)+account h (Ψ j) := orig.symm.trans
      (joined.trans (congrArg (fun f => f+account h (Ψ j)) breakdown))
    rw [negative,sub_eq_add_neg,balance]
    abel

end YM.Integration.WilsonTrueProjectedBareEntrance
