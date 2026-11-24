import YM.Integration.WilsonMovingMentorConcourseRows
import YM.AllOrder.Till.Glace

/-! The signed compression error at one actual site, uniformly in all torus sides
and exterior gauge fields. The two prices are on the true long paths and their
compressed local copies, with the width of the original entered age. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusSites
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Till Extra.Iteration Push.AbsoluteSums Plateau
open scoped BigOperators Classical Topology
variable {G : Gauge}

def site {r : ℕ} {n : Side} (A : ℕ → Atom G r) (U : Config G n) (x : Site n) :=
  ∑' i,(A i).unmasked U x

private theorem held {n : Side} {r : ℕ} {σ C : ℝ} (A : ℕ → Atom G r)
    (warm : 0<σ) (paid : Charged A σ C) (U : Config G n) (x : Site n) :
    |site A U x|≤C*2^r := by
  let f := fun i : ℕ => (A i).unmasked U x
  have upper (i : ℕ) : ‖f i‖≤(A i).budget σ*2^r :=
    ((A i).unmasked_bound _ _).trans (mul_le_mul_of_nonneg_right ((A i).lower_budget _ warm) (by positivity))
  have gross := paid.2.1.mul_right ((2:ℝ)^r)
  have normed := Summable.of_nonneg_of_le (fun i => norm_nonneg (f i)) upper gross
  apply (norm_tsum_le_tsum_norm normed).trans ((normed.tsum_le_tsum upper gross).trans ?_)
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right paid.2.2 (by positivity)

theorem rooted {n : Side} {r : ℕ} {σ C : ℝ} (A : ℕ → Atom G r)
    (warm : 0<σ) (paid : Charged A σ C) (b : ℕ) (U : Config G n) (x : Site n) :
    |site A U x - site (legible A b) U x| ≤
      2*(Real.exp (-(σ/2)*b)*C)*2^r := by
  let X := Plateau.leaf b ∘ A
  let Y := legible X b
  have half : 0<σ/2 := half_pos warm
  have hx := Plateau.release A warm paid b
  have hy := leg_pays X hx half b
  have joined : site A U x - site (legible A b) U x = site X U x - site Y U x := by
    unfold site
    rw [←(summation A warm paid U x).tsum_sub (summation _ warm (leg_pays A paid warm _) U x),
      ←(summation X half hx U x).tsum_sub (summation Y half hy U x)]
    apply tsum_congr
    intro i
    unfold legible Y X
    simp only [Function.comp_apply]
    unfold Plateau.leaf
    split
    next small => rw [scheme_of_fits _ (A i) small, scheme_of_fits _ (mute (A i)) small];simp
    next => rfl
  rw [joined]
  calc
    _ ≤ |site X U x|+|site Y U x| := abs_sub _ _
    _ ≤ _ := (add_le_add (held X half hx U x) (held Y half hy U x)).trans_eq (by ring)

theorem history (R : Run G)
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q : r.Tab R.rolls} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin} {m N j h : ℕ}
    (route : PlanV.Path r R.alloy Q h N m π Γ) (before : m≤j) (after : j≤N)
    (i : Age) (active : i∈Age.scope (h+2)) (n : Side) (U : Config G n) (x : Site n) :
    let σ := r.pre h (R.alloy.B.a.clock.J j) i
    let C := PlanV.capprice R.alloy h j i
    let b := (R.alloy.B.a.budget j).B
    |site (π j i) U x-site (legible (π j i) b) U x|≤2*(Real.exp (-(σ/2)*b)*C)*2^i.r := by
  exact rooted (π j i) ((r.shape h).pos _ _) (route.1 j before after i active).pay _ U x

end YM.Integration.WilsonVacuumPreResetTorusSites

