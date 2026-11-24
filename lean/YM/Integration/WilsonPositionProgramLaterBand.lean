import YM.Integration.WilsonPositionProgramReporterBand

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramLaterBand
open Filter Lattice RG PhysicalNext.Repeat.Legato
open WilsonPositionProgramReporterBand
variable {G : Gauge} {C : Run G} {D : XSpace.Run} {stage : ℕ}

def shift (B : Band C D stage) (start : ℕ) : Band C D stage where
  reporter := B.reporter+start
  lower := fun t=>B.lower (t+start)
  span := fun t=>B.span (t+start)
  upper := fun t=>B.upper (t+start)
  index := fun t=>B.index (t+start)
  powers := fun t=>B.powers (t+start)
  blocks := fun t=>B.blocks (t+start)
  extent := fun t=>B.extent (t+start)
  ready := fun t=>B.ready (t+start)
  mature := fun t=>B.mature (t+start)
  age := fun t=>B.age (t+start)
  top := fun t=>by simpa only [Nat.add_right_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using B.top (t+start)
  higher := fun t=>B.higher (t+start)
  spacing := fun t=>by simpa only [Nat.add_right_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using B.spacing (t+start)
  floor := fun t=>by simpa only [Nat.add_right_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using B.floor (t+start)
  ceiling := fun t=>by simpa only [Nat.add_right_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using B.ceiling (t+start)
  cofinal := B.cofinal.comp (tendsto_add_atTop_nat start)

theorem original (B : Band C D stage) (floor : ℕ) :
    ∃ B' : Band C D stage, ∀ t, floor ≤ B'.index t := by
  obtain ⟨start,late⟩ := eventually_atTop.mp (B.cofinal.eventually_ge_atTop floor)
  exact ⟨shift B start,fun t=>late (t+start) (Nat.le_add_left start t)⟩
end YM.Integration.WilsonPositionProgramLaterBand
