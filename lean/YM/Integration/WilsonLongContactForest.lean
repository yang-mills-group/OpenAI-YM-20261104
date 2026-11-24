import YM.Integration.WilsonLongContactAddress
import YM.Integration.ActualNormalizedPush
import YM.QCDVacuum.Stall.Faction

/-! Original anchored forest disintegration of one previously merged regular coefficient. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactForest
open Lattice RG RG.Patch Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Legato
open ConnectedActivityE6 Push Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector
open scoped Classical BigOperators
variable {G : Gauge} {c f : Side} {Q : Rep G f}

def blade (S : StepData c f) (L : Leaf Q) : Blade S Q where
  turn := L.turn
  ingredient := L.ingredient
  scopedR := L.scopedR
  grant := by
    intro U hu i h
    have yes := L.grant U hu
    rwa [h] at yes
  blank := L.blank
  weight := L.weight
  earn := L.earn
  glows k _ U := L.glows k U
  borel := L.borel

def one {S : StepData c f} (B : Blade S Q) : Faction S Q where
  own := {B}
  alone := by
    intro i hi j hj _
    have hi' : i = B := by simpa using hi
    have hj' : j = B := by simpa using hj
    exact hi'.trans hj'.symm

theorem cost {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    (L : Leaf Q) (X : Coat T F) (a : ℝ) (u : Directions G f) :
    ‖(blade S L).paidU X a u‖ ≤ L.weight := (blade S L).coin X a u

theorem prepared (S : StepData c f) (L : Leaf Q) (i : ℕ) (key : L.turn = .logKey i)
    (U : Config G f) : (one (blade S L)).cicada U = L.ingredient U * Q.eval U := by
  let B := blade S L
  let M := one B
  have kb : B.turn = .logKey i := key
  have gas : M.gasDue = ∅ := by
    ext v
    simp [M,one,Faction.asked,kb]
  have ing : M.ingredients U = L.ingredient U := by simp [M,Faction.ingredients,one,B,blade]
  have hb (k : Finset ℕ) : M.bun k U = L.ingredient U * Q.activities.gasOccurrence Q.p k U := by
    unfold Faction.bun Faction.bill Activities.gasOccurrence
    by_cases ha : Q.activities.admissible Q.p U k <;> simp [ha,gas,ing]
  change M.cicada U = _
  unfold Faction.cicada Rep.eval Activities.gas
  simp_rw [hb]
  rw [tsum_mul_left]
  ring

/-- The enrolled old density, forest, sector mask and coarse field are all retained. -/
theorem original (A : Run G) (N per j : ℕ) (hj : j < N)
    {x w : ℝ} (D : Allocation G (A.family.path.levels.clock.op j per) x w)
    (F : Forest (A.family.path.levels.clock.op j per).ratio)
    (L : Leaf (A.family.path.rep N per (j+1))) (i : ℕ) (key : L.turn = .logKey i)
    (V : Config G (A.family.S.side j per)) :
    let S := A.family.path.levels.clock.op j per
    let Q := A.family.path.rep N per (j+1)
    let M := one (blade S L)
    (∑ a, output D F Q.beta M.cicada a V)/(A.family.path.rep N per j).eval V =
      actualAverage A.family (N:=N) L.ingredient V := by
  intro S Q M
  obtain ⟨env,anch⟩ := M.sells (A.makes.wilson.represents N per (j+1) hj).good
  rw [push_anchors D F Q.beta M.cicada (A.family.path.levels.blocks j per).branches env anch,
    actualAverage_push]
  have e : M.cicada = fun U => Q.eval U • L.ingredient U :=
    funext fun U => (prepared S L i key U).trans (mul_comm _ _)
  rw [e]
  change _ / _ = _⁻¹ * _
  rw [div_eq_inv_mul]

end YM.Integration.WilsonLongContactForest
