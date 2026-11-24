import YangMills.WilsonProof.NativeSupport.IssuedBridge.FullPhysicalReconstruction
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedGroupCalendar
open YangMills YangMills.Wilson YM.Integration
open WilsonOriginalAllOrderCalendar

private def age (k : Key) : ℕ :=
  k.1.sum + k.2.1 + k.2.2.1 + k.2.2.2.1 + k.2.2.2.2

def schedule (g : GaugeGroup) : WilsonOriginalAllOrderCourse.Schedule g.core where
  cap k := age k + 1
  chronology k := Encodable.encode k
  neutral k := {
    radius := fun _ j H => 1 / ((age k + j + H + 1 : ℕ) : ℝ)
    positive := by intros; positivity
    multiplier := fun H => (age k + H + 1 : ℕ)
    grows := by intros; positivity
    entrance := fun _ j _ => Encodable.encode k + j }
  extraStrip k := {
    cap := fun _ j H => 1 / ((age k + j + H + 1 : ℕ) : ℝ)
    positive := by intros; positivity
    threshold := fun _ j => Encodable.encode k + j
    bill := fun _ j H => (age k + j + H + 1 : ℕ) }
  gearBill k j _ := (age k + j + 1 : ℕ)
  fixedDigit k j := {
    names := k.1.length + 1
    D := fun i => k.1.getD i.val k.2.1
    k := fun i => i.val + j + k.2.2.1
    order := max k.2.1 k.2.2.1
    q := k.2.2.1
    r := k.2.2.2.1
    grade := le_max_right _ _
    subset := Finset.univ
    front := 0
    present := Finset.mem_univ _
    inlet := fun _ => (age k + j + 1 : ℕ)
    positive := by intros; positivity }

theorem original (g : GaugeGroup) (hg : g.IsSimple) :
    let B := IssuedMaxwell.Reference.issued g
    ∃ run : Construction g, WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧
      run.originalPointReturns ∧ ∃ D : WilsonData B run.family, ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let chosen := run.refine p hp
        WilsonReconstruction B chosen.hierarchy ∧ chosen.hierarchy.Reconstructed ∧
        D.AdjointOn chosen.hierarchy ∧ run.family.Converges (p ∘ chosen.indices)
          (fun v => chosen.hierarchy.correlation none (chosen.hierarchy.project ∘ v)) :=
  FullPhysicalReconstruction.original YM.timeAxis hg (ε:=1) zero_lt_one (schedule g)

end IssuedBridge.PostedGroupCalendar
end
