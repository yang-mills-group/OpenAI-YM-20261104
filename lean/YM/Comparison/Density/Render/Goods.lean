import YM.Comparison.Density.Render.Season

/-!
Rank TWO canonical extra packet at output. Terms requested
translation-signed average and clover read normal; refers to same
clover-filter energies in physical units. Correction K setup separate
(theorem `supplies`). No projection-null inferred from evaluation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Render
open Fusing Markers RG Lattice Function Finset MeasureTheory Filter Wilson
open Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo Next.Scheduling Next.Scheduling.Wages Precision Work.F03 Work.G07 StressFlux
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff InnerProductSpace
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {B : BudgetPoint}

namespace Frame
variable (F : ℕ→Atom G 2) (n : Side) (a : ℝ)

def rosebud (i : ℕ) := (F i).footprint (0:Site n) ∪ halo 2 {0}
def echo (i) := baseLine (0:Site n) (F i)-pollen 0 (F i)

def makeRose (p : ℕ →Prop) : Frame G n where
    footprint :=rosebud F n
    pivot _:= mem_union_right _ (halo_subset 2 {0} (mem_singleton_self _))
    dataF i := recipe a p i • Frame.echo F n i

def fairFee (p : ℕ→Prop) (B : BudgetPoint) (i : ℕ):= |recipe a p i| *(price B (F i)+(F i).magnitude*bloom G B* B.threshold^2)
lemma rose_era (p : ℕ→Prop) (hF : ∀ i,(F i).Invariant) (B: BudgetPoint): Frame.Fair (Frame.makeRose F n a p) B (Frame.fairFee F a p B):= by
  have he i := (credit_pair (0:Site n) (F i) (B:=B) (hF i) (Finset.subset_union_right (s₁:=(F i).footprint (0:Site n))) subset_union_left)
  exact ⟨fun i=> AnalyticBridge.CouplingShape.reg_scale _ (he i).1,fun i=>AnalyticBridge.CouplingShape.sup_scale _ (he i).2⟩
lemma scalar_H {X : Support n} {f : Pot G n} (x y) (h : B.Regular X f) : logHessian (a • f) x y = a * logHessian f x y :=
    (AnalyticBridge.CouplingShape.log_eq_H ..).trans ((AnalyticBridge.CouplingShape.scalar_jet h a ..).trans (congrArg _ ((AnalyticBridge.CouplingShape.log_eq_H ..).symm)))
lemma rose_stars (g : G.Simple) (p : ℕ→Prop) (hF : ∀ i,(F i).Invariant) (B: BudgetPoint) (hn : 20<n.val) : Frame.Nulls (Frame.makeRose F n a p):= by
  refine ⟨fun i=>?_,fun i hi x y hx hy=>?_⟩
  · dsimp only [makeRose]; simp [Frame.echo,baseLine,base_zero,pollen_zero]
  have ht:=rebases (0:Site n) (F i) g (hF i) B subset_union_right subset_union_left (show Nonwrapping (rosebud F n i) 0 from hi) hn x y hx hy
  change logHessian (recipe a p i • _) x y=0
  rw [show logHessian (recipe a p i • Frame.echo F n i) x y= recipe a p i*logHessian (baseLine 0 (F i)-pollen 0 (F i)) x y from
    scalar_H n _ x y (credit_pair (0:Site n) (F i) (B:=B) (hF i) (Finset.subset_union_right (s₁:=(F i).footprint (0:Site n))) subset_union_left).1, ht,mul_zero]

variable {σ C : ℝ} (h : 0<σ) (hX : B.supportExponent / B.B ≤ σ/4) (hc : 2 ≤ B.B)

def alto (B : BudgetPoint) (σ : ℝ):= fund G B.power B.order 2 B.supportExponent σ
-- extra cost 81 when enlarging; ∼:
private def one_canon (B : BudgetPoint) := startup G 2 B.power B.order
private lemma start_hi : 1 ≤ one_canon (G:=G) B := by
  have hx := one_le_pow₀ (a:=(2:ℝ)) (by norm_num) (n:=B.order); unfold one_canon startup
  exact one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hx (Wages.slot_ge ..)))
private lemma bloom_nn (G : Gauge) (B : BudgetPoint): 0≤ bloom G B:= mul_nonneg (by positivity) (sq_nonneg _)

private lemma pac (j : Atom G 2) : j.magnitude*B.threshold^2 ≤ price B j := by
  rw [scan]; let x:ℝ:= j.magnitude; have hx : 0≤x:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  apply le_trans _ (le_mul_of_one_le_right ?_ ?_)
  · refine le_trans (b:= 1* B.threshold^2 * x) ?_ ?_
    · rw [one_mul,mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right start_hi (sq_nonneg _)) hx
  · exact mul_nonneg (mul_nonneg (zero_le_one.trans start_hi) (sq_nonneg _)) hx
  exact one_le_pow₀ (by simp)

def roseCharge (a σ : ℝ) (G : Gauge) (B : BudgetPoint):= |factor*a| *(1+bloom G B)*Real.exp (81*B.supportExponent)* (alto (G:=G) B σ*B.threshold^2)
private lemma h_price (p : ℕ → Prop) i : 0 ≤ fairFee F a p B i:= by
  unfold fairFee; refine mul_nonneg (abs_nonneg _) (add_nonneg ?_ ?_)
  · exact (Wages.fin B (F i) (0:Site ⟨2,two_pos⟩)).nonneg
  exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _=> abs_nonneg _) (bloom_nn ..)) (sq_nonneg _)

include h hX hc
private lemma t_pays (hs : SumBudget (fun i=> (F i).budget σ) C) (p : ℕ→Prop): SumBudget (fun i=> B.mass (rosebud F n i) (Real.exp ((σ/4)*(F i).length) * fairFee F a p B i)) (roseCharge a σ G B * C):= by
  let D:=Real.exp (81*B.supportExponent); let K:= |factor*a| *(1+bloom G B)
  have hk: 0≤K:= mul_nonneg (abs_nonneg _) (add_nonneg zero_le_one (bloom_nn ..))
  change SumBudget _ ((K*D)*_*C); rw [mul_assoc (K*D)]
  refine Cost.mono (Cost.scale (Wages.ticket B σ C h hX F hs (0:Site n)) (K*D) (mul_nonneg hk (Real.exp_pos _).le)) (fun i=>mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (h_price F a ..))) fun i=>?_
  let S:= (F i).footprint (0:Site n); let j:= F i; let r:RegularAddress n:= ⟨0,S,(rack n F a p).pivot _⟩
  have ht : B.supportExponent* coverNumber B.B (rosebud F n i) ≤ 81*B.supportExponent+B.supportExponent*coverNumber B.B S:= by
    have hp : (coverNumber B.B (expand r):ℝ) ≤ coverNumber B.B S+81:= by exact_mod_cast (Geo.enlarge B r hc)
    exact (mul_le_mul_of_nonneg_left hp B.exponent_pos.le).trans (by linarith)
  have hh: fairFee F a p B i ≤ K*price B j:= by
    have hP : |recipe a p i| ≤ |factor*a|:= by unfold recipe; split; exact le_rfl; rw [abs_zero]; exact abs_nonneg _
    apply le_trans (mul_le_mul_of_nonneg_right hP (show 0 ≤ price B (F i)+(F i).magnitude*bloom G B*B.threshold^2 from add_nonneg ((Wages.fin B _ (0:Site n)).nonneg) (mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _=> abs_nonneg _) (bloom_nn ..)) (sq_nonneg _))))
    unfold K; rw [mul_assoc |factor*a| (1+bloom G B)]; refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (factor*a))
    rw [add_mul,one_mul]; exact add_le_add_right ((by linarith only [mul_le_mul_of_nonneg_left (pac j (B:=B)) (bloom_nn G B)] : j.magnitude*bloom G B*B.threshold^2 ≤ bloom G B*price B j)) _
  apply le_trans (mul_le_mul (Real.exp_monotone ht) (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (h_price F a ..)) (Real.exp_pos _).le)
  unfold D BudgetPoint.mass toll; rw [Real.exp_add]; dsimp only [S,j]; apply le_of_eq; ring
lemma in_time (p : ℕ→Prop) (hs : SumBudget (fun i=> (F i).budget σ) C) : SumBudget (fun i=> B.mass (rosebud F n i) (fairFee F a p B i)) (roseCharge a σ G B*C) := by
  apply Cost.mono (t_pays F n a h hX hc hs p)
  · intro i; exact mul_nonneg (Real.exp_pos _).le (h_price F a ..)
  intro i; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (h_price F a ..) (Real.one_le_exp (mul_nonneg (by positivity :0 ≤σ/4) (Nat.cast_nonneg _)))) (Real.exp_pos _).le
lemma rose_far {A:Activities G n} (hf : ∀ i,(F i).Invariant) (hs : SumBudget (fun i=> (F i).budget σ) C) (m : ℕ):
    ((makeRose F n a (postW F m)).coffee A).EBound B (cost B * ((Real.exp ((σ/4)*m))⁻¹*(roseCharge a σ G B*C))) := by
  apply Frame.economics A (rose_era F n a _ hf B)
  have H:= t_pays F n a h hX hc hs (postW F m)
  have hh := wax (h_price F a (postW F m) (B:=B)) (postW F m) (fun i ht=> mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (show (m:ℝ)≤ ((F i).length:ℝ) from by exact_mod_cast ht) (show 0≤σ/4 by positivity))) (h_price F a (postW F m) i)) (Real.exp_pos _) H
  convert hh using 2 with i; split_ifs; exact rfl
  next hx=> simp only [makeRose,fairFee,recipe,if_neg hx,abs_zero,zero_mul]
end Frame
end YM.Comparison.Density.Render
