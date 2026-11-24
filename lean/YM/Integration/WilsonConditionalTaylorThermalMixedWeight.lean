import YM.Integration.WilsonConditionalTaylorThermalInteractionDifference

/-! The exact second finite difference of the physical temperature weight.
Both direction factors are measured on the same previously issued history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalMixedWeight
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial
open WilsonConditionalTaylorThermalWeight WilsonConditionalTaylorThermalLaplace
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d

def heat (t : d.Tags) (u : ℕ→ℝ) (x : Fields G d) := Real.exp (-account t u x)
def increment (t : d.Tags) (u : ℕ→ℝ) (x : Fields G d) := heat t u x-1
def joint (t : d.Tags) (z a b : ℕ→ℝ) (f : Config G n→ℝ) (x : Fields G d) :=
  heat t z x*((increment t a x*increment t b x)*f (d.fine 1 x))

theorem together (t : d.Tags) (z a b : ℕ→ℝ) (f : Config G n→ℝ) :
    (d.resetTerms (z+a+b) f t - d.resetTerms (z+a) f t) -
      (d.resetTerms (z+b) f t-d.resetTerms z f t) = joint t z a b f := by
  funext x
  have add (u v : ℕ→ℝ) : account t (u+v) x=account t u x+account t v x := by
    have e := account_sub t (u+v) u (1:Config G c) x
    rw [add_sub_cancel_left] at e
    change _ = _-_ at e
    dsimp only [WilsonConditionalTaylorThermalWeight.account]
    linarith
  change heat t (z+a+b) x*f (d.fine 1 x)-heat t (z+a) x*f (d.fine 1 x)-
    (heat t (z+b) x*f (d.fine 1 x)-heat t z x*f (d.fine 1 x))=_
  simp only [joint,increment,heat,add,neg_add_rev,Real.exp_add]
  ring

theorem neat (ok : d.OK G) (t : d.Tags) (u : ℕ→ℝ) :
    d.SmoothAtFlat (increment (G:=G) t u) := ((smoothAccount ok t u).neg.exp).sub contDiffAt_const

private theorem difference (t : d.Tags) (u : ℕ→ℝ) :
    increment (G:=G) t u ∘ d.tablePath =
      (excess t u ∘ d.tablePath)-(account t u ∘ d.tablePath) := by
  funext x
  simp only [Function.comp_apply,Pi.sub_apply,increment,heat,excess]
  ring

theorem grade (ok : d.OK G) (t : d.Tags) (u : ℕ→ℝ) :
    RadialOrder 2 (increment (G:=G) t u ∘ d.tablePath) := by
  rw [difference]
  intro x
  simpa only [Pi.sub_apply,sub_eq_add_neg] using!
    bill_add (bill_ge (excessGrade ok t u x) (show 2≤4 by decide)) (bill_neg (accountGrade ok t u x))

theorem principal (ok : d.OK G) (t : d.Tags) (u : ℕ→ℝ) (x : E) :
    jet (increment t u ∘ d.tablePath) 2 x = -vertex t u x := by
  rw [difference]
  have vanish := congrFun (jets_vanish (smoothExcess ok t u) (excessGrade ok t u) (show 2<4 by decide)) x
  have e : jet ((excess (G:=G) t u ∘ d.tablePath)-(WilsonConditionalTaylorThermalWeight.account t u ∘ d.tablePath)) 2 x =
      jet (excess t u ∘ d.tablePath) 2 x-vertex t u x := by
    unfold vertex jet
    rw [iteratedFDeriv_sub_apply (contDiffAt_infty.mp (smoothExcess ok t u) 2)
      (contDiffAt_infty.mp (smoothAccount ok t u) 2)]
    exact mul_sub .. 
  rw [e,vanish]
  simp

theorem regular (ok : d.OK G) (t : d.Tags) (z a b : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) :
    d.SmoothAtFlat (joint t z a b f) :=
  ((smoothAccount ok t z).neg.exp).mul (((neat ok t a).mul (neat ok t b)).mul test.smooth)

theorem rank (ok : d.OK G) (t : d.Tags) (z a b : ℕ→ℝ) {f : Config G n→ℝ}
    {w : ℕ} (old : d.grade f w) :
    RadialOrder (w+4) (joint t z a b f ∘ d.tablePath) := by
  intro x
  have fl := bill_mul (bill_mul (grade ok t a x) (grade ok t b x)) (old x)
  have ht : d.SmoothAtFlat (heat t z) := (smoothAccount ok t z).neg.exp
  simpa only [Nat.zero_add,show 2+2+w=w+4 by omega] using! bill_mul (directions ht x).bounded fl

theorem head (ok : d.OK G) (t : d.Tags) (z a b : ℕ→ℝ) {f : Config G n→ℝ}
    (test : d.Testable f) {w : ℕ} (old : d.grade f w) (x : E) :
    jet (joint t z a b f ∘ d.tablePath) (w+4) x = vertex t a x*vertex t b x*field (d:=d) f w x := by
  let A := increment (G:=G) t a ∘ d.tablePath
  let B := increment (G:=G) t b ∘ d.tablePath
  let F := f ∘ d.fine 1 ∘ d.tablePath
  let H := heat (G:=G) t z ∘ d.tablePath
  have hA := neat ok t a
  have hB := neat ok t b
  have hH : ContDiffAt ℝ ∞ H 0 := (smoothAccount ok t z).neg.exp
  have ab : RadialOrder 4 (A*B) := fun y => bill_mul (grade ok t a y) (grade ok t b y)
  have full : RadialOrder (4+w) ((A*B)*F) := fun y => bill_mul (ab y) (old y)
  have h₀ := head_product (A:=H) (f:=(A*B)*F) hH ((hA.mul hB).mul test.smooth) (k:=0)
    (fun y => (directions hH y).bounded) full x
  have h₁ := head_product (A:=A*B) (f:=F) (hA.mul hB) test.smooth ab old x
  have h₂ := head_product (A:=A) (f:=B) hA hB (grade ok t a) (grade ok t b) x
  change jet (H*((A*B)*F)) (w+4) x = _
  simp only [Nat.zero_add] at h₀
  rw [Nat.add_comm w 4,h₀,h₁,h₂,jet_zero]
  have zero : H 0 = 1 := by simp [H,heat,WilsonConditionalTaylorThermalWeight.account,tablePath_zero,account_flat ok]
  rw [zero,one_mul,principal ok t a,principal ok t b]
  change _ = _*_*jet F w x
  ring

end YM.Integration.WilsonConditionalTaylorThermalMixedWeight
