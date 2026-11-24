import YM.RG04B.Start.Issued
import YM.RG03.IndexedBoards

/-!
# Sharing one remodeled representation per step

`Render`: values ON FULL ADDRESS before masking. Interface to hold e.g. Fk's
independently given `V[e,r]` packets with their prechosen renders, through THIS
beta and thresholds. This type is a *container*, not asserting the rows are
Fk/WilsonX: proof they implement that prescription, use of C.path kinematics,
etc owed by suppliers. (Top convention pinned separately; there's a necessary
startup test because our constructor uses a particular local top.) They may
reserve inactive addresses for analytic alignment. Do not depend on which
re-expression the continuation will find. All budgeting is on literal
addresses, including empty when permitted. `P` order index in APIs means
fluctuation power, not valence degree. Extensive vs action coordinate split
unchanged.

After kino reset `ω*`, beta reading perturbation is a field of the EXACT OTHER
rep -- using that as kernel beta is invalid. Row.mask fits both.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B.Vac
open Function Filter Lattice RG Wilson Real RG03.Indexed
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}

structure Render (C : Family G) where
  /-- Predicted log regular extra packets (in Rep exponent sign convention),
  evaluated in step m units on its horizon. Include nonlinear gauge completes. Pass
  in *one* such table on the trajectory, not obtained using `Sliced`. -/
  regular (N p m e : ℕ) : ℕ → Config G (C.side m p) → ℝ
  wherePlaced (N p m e : ℕ) : ℕ → RegularAddress (C.side m p)
  /-- omega_e in gAt C N p (m+1) units, predicting beta m - beta (m+1).
  Unmasked cover/bulk convention. -/
  omega (N m e : ℕ) : ℝ

variable {C : Family G} (M : Render C) (N p m e : ℕ)

def OrderedStart : Prop := ∀ e ≥ 2, ∀ N p,
    let X := C.path.rep N p N
    M.regular N p N e = Startup.chart G (C.side N p) X.clip X.beta (e+2) ∧
    ∀ i, M.regular N p N e i ≠ 0 → M.wherePlaced N p N e i=X.activities.reg i

def model (X : Rep G (C.side m p)) := setE X.activities (M.regular N p m e)
def error (X : Rep G (C.side m p)) := setE X.activities (X.activities.E - M.regular N p m e)

structure Sliced (X : Rep G (C.side m p)) (r : ℝ) : Prop where
  same : Remodeled C N p m X
  seats : ∀ i, M.regular N p m e i ≠ 0 → M.wherePlaced N p m e i=X.activities.reg i
  openE : (error M N p m e X).RegularFamily X.p
  budget : (error M N p m e X).EBound X.p r

/-- Fk normalization convention: WHOLE integrated/base correction through this order,
no SSR resetting at a calendar variant. e runs 1..d inclusive, bare exponent beta.
Doesn't assume convergent / parity or any ratio estimate. This bookkeeping is also
compatible with a vanishing e=1 term (expected in Fk). -/
def guess (M : Render C) (e N p m : ℕ) : ℝ := C.path.β N p (m+1)+
  ∑ i ∈ Finset.Icc (1:ℕ) e, M.omega N m i * gAt C N p (m+1) ^ ((i:ℝ)-2)

private lemma reverseFamily (m : BudgetPoint) {n : Side} (A : Activities G n)
    (f g : ℕ → Config G n → ℝ) (h : (setE A f).RegularFamily m) (hv : (setE A g).RegularFamily m) :
    (setE A (f-g)).RegularFamily m := by
  refine ⟨fun i=>?_,fun i=>?_,fun i hz x y hx hy=>?_⟩
  · change m.Regular (A.reg i).support (f i-g i)
    rw [sub_eq_add_neg,← neg_one_smul ℝ (g i)]
    exact regular_plus _ (h.smooth i) (WilsonStartup.Start.times_reg _ (hv.smooth _))
  · change f i 1-g i 1=0; rw [show f i 1=0 from h.at_flat _,show g i 1=0 from hv.at_flat _,sub_self]
  have hs := WilsonStartup.Start.times_reg (-1) (hv.smooth i)
  change logHessian (f i-g i) x y=0
  rw [sub_eq_add_neg,←neg_one_smul ℝ (g i),hess_plus m (S:=(A.reg i).support) (f:=f i) (g:=(-1:ℝ)•g i) (h.smooth i) hs,
    show logHessian (f i) x y=0 from h.vanish i hz x y hx hy,zero_add,
    neg_one_smul]
  unfold logHessian
  change iteratedFDeriv ℝ 2 (fun u => - g i (increment 1 u)) 0 ![x,y] = 0
  rw [show (fun u=> -g i (increment 1 u)) = -(g i ∘ increment 1) from rfl]
  rw [iteratedFDeriv_neg_apply]
  change -logHessian (g i) x y=0; rw [show logHessian (g i) x y=0 from hv.vanish i hz x y hx hy,neg_zero]

private lemma reverseBound (m : BudgetPoint) {n : Side} (A : Activities G n) {r s : ℝ}
    (f g : ℕ → Config G n → ℝ) (hh : (setE A f).RegularFamily m) (hG : (setE A g).RegularFamily m)
    (h : (setE A f).EBound m r) (hv : (setE A g).EBound m s) : (setE A (f-g)).EBound m (r+s) := by
  obtain ⟨b,hb,hx⟩:=h; obtain ⟨c,hc,ht⟩:=hv
  refine ⟨fun i=> b i+c i,fun i=>?_,fun i=>?_⟩
  · change m.supBounds (A.reg i).site (A.reg i).support (f i - g i) _; rw [sub_eq_add_neg,←neg_one_smul ℝ (g i)]
    have hg:= WilsonStartup.Start.times_bound (-1) (hc i)
    rw [norm_neg,norm_one,one_mul] at hg
    exact bound_plus m (A.reg i).site (hh.smooth _) (WilsonStartup.Start.times_reg _ (hG.smooth _)) (hb _) hg
  convert Push.AbsoluteSums.budget_plus (hx i) (ht i) using 1
  funext j; simp only [setE,BudgetPoint.mass,mul_add]; split <;> simp [*]

namespace Sliced
variable {M N p m e} {X : Rep G (C.side m p)} {r s : ℝ} (S : Sliced M N p m e X r)
include S
lemma widen (h : r ≤ s) : Sliced M N p m e X s := by
  obtain ⟨b,hb,ht⟩:= S.budget
  exact ⟨S.same,S.seats,S.openE,b,hb,fun i=> Push.AbsoluteSums.budget_loosen (ht i) h⟩

lemma regularModels : (model M N p m e X).RegularFamily X.p ∧
    (model M N p m e X).EBound X.p (C.path.levels.clock.allowance m+r) := by
  obtain hK:= S.same.valid.labels
  let Y := M.regular N p m e
  have ht := reverseFamily X.p X.activities X.activities.E (X.activities.E-Y) hK.regular S.openE
  have hr := reverseBound X.p X.activities X.activities.E (X.activities.E-Y) hK.regular S.openE hK.boundE S.budget
  rw [sub_sub_self] at ht hr
  exact ⟨ht,hr⟩

/-- Cost paid before reconstructing any sums. -/
theorem additive : X.activities.additive X.p = (model M N p m e X).additive X.p +
    (error M N p m e X).additive X.p := by
  let h:= error M N p m e X
  have hh:=exponential_add X.activities X.p _ _ (S.regularModels).2 S.budget
  rw [add_sub_cancel] at hh; exact hh

lemma invoice {U : Config G (C.side m p)} :
    let Z : Rep G (C.side m p) := {X with activities:=model M N p m e X}
    X.eval U= Real.exp (Z.exponent U - (error M N p m e X).additive X.p U) * X.activities.gas X.p U := by
   intro Z
   simp only [Rep.eval,Rep.exponent,S.additive,Z,Pi.add_apply,sub_sub, add_assoc]
end Sliced
end YM.RG04B.Vac
