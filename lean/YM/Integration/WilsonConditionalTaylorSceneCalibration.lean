import YM.Integration.WilsonConditionalTaylorSceneChoices
import YM.MSbar.Alto.Halo

/-! The actual scalar kinetic calibration of a realized scene, before
comparing it to an independently prescribed coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorSceneCalibration

open Lattice RG Wilson Tree Precision Exterior Push.Uniform MSbar MSbar.Rolling MSbar.Rolling.Price
open MSbar.Midpoint MSbar.Wave MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal PowerSeries
open PhysicalNext.Repeat.Legato RGComparison.Core16 WilsonConditionalTaylorSceneChoices
open scoped Classical

variable {G : Gauge} (R : Run G) {N n k r : ℕ} {S : Scene R.family.path.levels n r} {u : G.ColorIndex}
  (scene : Realized R.alloy.B.kin N n k r (Lis.sun G u) S)

def untuned (j : ℕ) (lo : k ≤ j) (hi : j < N) : Nesting G (R.family.side j n) :=
  let F:=(scene.step j hi lo).choose
  let t:=issued R scene j lo hi
  colorCut F t (R.alloy.B.kin.path N (j+1)) (R.family.path.levels.params (j+1)).clip R.metals.O
    (S.Poly (j+1)) (R.alloy.B.kin.stationary N j n F)

def inkAt (N n j : ℕ) : Pot (Primary (R.family.side j n) G) :=
  ink (R.family.side j n) (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j)

theorem received (j : ℕ) (lo : k ≤ j) (hi : j < N) :
    coeff 0 (S.action j)=1 ∧ Kind (untuned R scene j lo hi) ∧
      S.Poly j=bley (S.action j) (untuned R scene j lo hi) (inkAt R N n j) ∧
      ∀ i≤r, caliper (R.family.side j n) (Lis.sun G u) (coeff i (S.Poly j))=0 := by
  let F:=(scene.step j hi lo).choose
  let t:=issued R scene j lo hi
  obtain ⟨head,_,eqn⟩:=(scene.step j hi lo).choose_spec.choose_spec
  refine ⟨head,?_,eqn,(scene.budget j hi.le lo).2.sitting⟩
  apply Bakery.hush
  apply toneG
  exact (scene.budget (j+1) hi (lo.trans (Nat.le_succ j))).1

include scene in
/-- The periodized physical two-leg income is near the original negative
two, with its resolved sign, rather than being set equal to `-2`. -/
theorem charged (j : ℕ) (lo : k ≤ j) (hi : j ≤ N)
    (paid : Alto.Sampled (R.family.side j n) (R.family.path.levels.params j)) :
    |caliper (R.family.side j n) (Lis.sun G u) (inkAt R N n j)+2|≤1 := by
  let U:=R.family.path.levels.params j
  let K:=RunFormalChain.fromRun R
  obtain ⟨v,hv,bound⟩:=paid.bound
  have s:= (scene.budget j hi lo).1.quiet
  have test:=congrArg (stackH (R.family.side j n) (Lis.sun G u)) (ion (R.alloy.B.kin.path N j) U.clip s)
  change caliper (R.family.side j n) (Lis.sun G u) (inkAt R N n j)=_ at test
  rw [test]
  exact (sampled (Lis.sun G u) (R.alloy.B.kin.path N j) U.clip (K.planned.cap N j hi) v hv (Lis.sunny ..)).trans bound

/-- First unsettled coupling grade in the real original convention. The
right-hand side is evaluated on the *actual* unretuned finite action. -/
theorem unsettled (j : ℕ) (lo : k ≤ j) (hi : j < N) (a : PowerSeries ℝ) {i : ℕ} (pos : 0 < i)
    (due : i ≤ r) (earlier : Hush (S.action j) a i) :
    let z:=caliper (R.family.side j n) (Lis.sun G u)
    z (coeff i (bley a (untuned R scene j lo hi) (inkAt R N n j))) =
      -(2*(coeff i a-coeff i (S.action j))*z (inkAt R N n j)) := by
  intro z
  obtain ⟨head,kind,paid,cleared⟩:=received R scene j lo hi
  have h:=Hush.wagon (T:=untuned R scene j lo hi) (c:=inkAt R N n j) kind earlier head pos
  rw [h,←paid,_root_.map_sub,map_smul,cleared i due,zero_sub]
  rfl

end YM.Integration.WilsonConditionalTaylorSceneCalibration
end

