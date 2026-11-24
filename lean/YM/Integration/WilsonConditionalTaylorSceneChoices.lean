import YM.Integration.WilsonConditionalTaylorForestHaar
import YM.Integration.WilsonMarkedOffsetGaussian
import YM.MSbar.Chord.Locks

/-! The forests and kernel choices that actually produced one realized
finite-volume history, with a prescribed change at a single physical step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorSceneChoices

open RG Tree Lattice RGComparison.Core16 PhysicalNext.Repeat.Legato MSbar.Midpoint
open scoped Classical

variable {G : Gauge} (R : Run G) {N n k r : ℕ} {S : Scene R.family.path.levels n r} {v : G.Color}
    (scene : Realized R.alloy.B.kin N n k r v S)

/-- The only unconstrained indices lie outside the given realized history. -/
def forests : Slices R.family.path.levels n := fun i=>
  if h : k ≤ i ∧ i < N then (scene.step i h.2 h.1).choose else someSlices R.family.path.levels n i

theorem atStep (i : ℕ) (lo : k ≤ i) (hi : i < N) :
    forests R scene i=(scene.step i hi lo).choose := by simp [forests,lo,hi]

def issued (i : ℕ) (lo : k ≤ i) (hi : i < N) : (R.family.path.levels.clock.op i n).Choices :=
  (scene.step i hi lo).choose_spec.choose

def retag (j : ℕ) (v : (R.family.path.levels.clock.op j n).Choices) (i : ℕ) (lo : k ≤ i) (hi : i < N) :
    (R.family.path.levels.clock.op i n).Choices :=
  if h : i=j then h.symm ▸ v else issued R scene i lo hi

theorem chosen (j : ℕ) (v : (R.family.path.levels.clock.op j n).Choices) (lo : k ≤ j) (hi : j < N) :
    retag R scene j v j lo hi=v := by simp [retag]

theorem unchanged (i j : ℕ) (v : (R.family.path.levels.clock.op j n).Choices)
    (lo : k ≤ i) (hi : i < N) (different : i ≠ j) : retag R scene j v i lo hi=issued R scene i lo hi := by
  simp [retag,different]

def entire (j : ℕ) (lo : k ≤ j) (hi : j ≤ N) : (traversal (forests R scene) hi).Tags :=
  WilsonConditionalTaylorForestHaar.tags (forests R scene) (issued R scene) hi lo

def altered {j : ℕ} (F : Forest (R.family.path.levels.clock.op j n).ratio)
    (v : (R.family.path.levels.clock.op j n).Choices) (i : ℕ) (lo : k ≤ i) (hi : i ≤ N) :
    (traversal (WilsonConditionalTaylorForestHaar.replace (forests R scene) j F) hi).Tags :=
  WilsonConditionalTaylorForestHaar.tags _ (retag R scene j v) hi lo

end YM.Integration.WilsonConditionalTaylorSceneChoices
end

