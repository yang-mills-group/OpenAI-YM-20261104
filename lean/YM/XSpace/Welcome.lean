import YM.XSpace.Tamarack
/-! # Reparameterized X-space positions and g sensor

Effects computed on the SAME charts after expressing in their announced position-coupling. Including commutation of taking connected. Orientation Budget exact and through arbitrary orders on each finite regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter PowerSeries Cirrus Photo Normalize Structure1 Retirement Maxwell Graph3 MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(W: Initialize G) {V:Store G}(Y:Rose.Pick V)(l: Mesh){n:ℕ}(d:ℕ)(g:G.Simple)
local notation "Ξ"=> χ W Y l
lemma conditions (H:V.Meets W l d)(i:ℕ): (V.measure d).D (proposed W Y l d i)= if i=0 then (V.measure d).D (reference G d) else 0:=by
  unfold proposed; by_cases h:i=0; · subst i; rw [turn_rest]; apply H.2.1
  rw [if_neg h,turn,map_sum]; apply Finset.sum_eq_zero; intro x _; rw [map_smul, H.2.1 x]; split_ifs with hx; · rw [hx,α,pow_zero, coeff_one i,if_neg h]; simp
  rw [smul_zero]
lemma horizon (p:ℕ)(S: d≤p) : ∀ᶠ l in Front, ∀ n:ℕ, recruit (up S) (proposed W Y l p n)= proposed W Y l d n:=by
  filter_upwards [V.cumulative W Cirrus.frontier S] with l h i; unfold proposed turn; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [show recruit (up S) (α W Y l i j • V.opens W l p j)=α W Y l i j • recruit (up S) (V.opens W l p j) from by ext n t p; rw [recruits]; rfl]; exact congr_arg (_ • ·) (h j)
lemma real_system (H:V.Meets W l d): Respect (proposed W Y l d):=by
  intro i n v t; rw [sent,sent]; unfold turn; rw [star_sum]; apply Finset.sum_congr rfl; intro j _; rw [star_smul,star_trivial]; dsimp only; rw [H.2.2.2.2.1 j n v t]
lemma turnInv {P:PS} (H:constantCoeff P=0)(h:inversion P= -P)(v:PS): inversion (v.subst P)=(inversion v).subst P:=by rw [inversion,FPS.rescale_substitute v P H,(show rescale (-1:ℂ) P= -P from h), rescale_flip v P H]
lemma proper (H:V.Meets W l d) (C: V.Meets W l 6) : Forward (proposed W Y l d):=by
  intro i; ext1 n; ext1 t; ext1 p; rw [recruits]; let f(n':ℕ):= V.opens W l d n' n t p; let q:= hinge d ∘ p; let x(n'): ℂ:= V.opens W l d n' n t q; have he(n':ℕ): x n'= (-1:ℂ)^n' * f n' := by
    have he: x n'=(-1:ℝ)^n' • f n':=congr_arg (fun R:Prediction G d=>R n t p) (H.2.2.2.1 n'); rw [he]; simp [Complex.real_smul]
  change proposed W Y l d i n t q = (-1:ℝ)^i • (proposed W Y l d i n t p); rw [sent,sent]; change turn W Y l x i= (-1:ℝ)^i • turn W Y l f i; simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,turn_coins, ← coeff_rescale]; rw [show rescale (-1:ℂ) ((mk f).subst Ξ)=_ from turnInv (χzero ..) (χodd W Y l C) (mk f), show mk x=inversion (mk f) from ?_]; apply PowerSeries.ext; intro n; rw [inversion,coeff_rescale,coeff_mk,coeff_mk,he] -- direction ambiguous
-- post-condition coupling
lemma posed (k:Cirrus.Sample 3)(p:Badge): batchT (measureₓ W Y 6 k) p=(batchT (cooked W V 6 k) p).subst (χ W Y k.F):= PowerSeries.ext fun n=> by unfold batchT; rw [coeff_mk,measure_paid,turn_coins]
def checkDetector : PS:= PowerSeries.mk (fun i=> Deposit l (fun x=>coeff i (b3 (batchT (measureₓ W Y 6 x)))) (test Y))
lemma check : checkDetector W Y l=(Detector W Y l).subst Ξ:=by
  apply PowerSeries.ext; intro i; rw [Detector,← turn_coins,checkDetector]; have hh(k:Sample 3): b3 (batchT (measureₓ W Y 6 k))= (together W V k).subst (χ W Y k.F):=by unfold together b3; simp_rw [posed]; simp only [two_smul, subst_add (χday ..),subst_mul (χday ..),subst_sub (χday ..)] -- instance Mv problem
  have he (x:Sample 3): coeff i ((together W V x).subst (χ W Y x.F)) = turn W Y x.F (fun j=> coeff j (together W V x)) i:=by rw [turn_coins, show (mk fun j => coeff j (together W V x))=together W V x from PowerSeries.ext fun j=> coeff_mk ..]; -- test
  rw [coeff_mk]; simp_rw [hh,he]; unfold turn Deposit; simp_rw [Finset.mul_sum, Complex.real_smul,← mul_assoc]; rw [Finset.sum_comm (t:=Finset.range (i+1))]; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; ring
lemma exact_χ (H:V.Meets W l 6)(h:Use W Y l): checkDetector W Y l=(↑(c_T Y):ℂ) • X:=by
  have hr : Detector W Y l = (↑(c_T Y):ℂ) • chosen W Y l:=by unfold chosen; rw [odds W Y l H,map_zero,sub_zero]; have h':(↑(c_T Y):ℂ)≠0:= Complex.ofReal_ne_zero.mpr Y.fresh.ne; rw [smul_inv_smul₀ h']
  rw [check,hr, subst_smul (χday W Y l),invertsX W Y l h]; -- defeq
include g in
theorem welcomed (d:ℕ) : ∀ᶠ i in Front,(V.Meets W i d)∧ (V.Meets W i 6)∧ Use W Y i∧ Forward (proposed W Y i d) ∧ Respect (proposed W Y i d) ∧(∀ k,(V.measure d).D (proposed W Y i d k)=if k=0 then (V.measure d).D (reference G d) else 0)∧checkDetector W Y i=(↑(c_T Y):ℂ) • X:=by
  filter_upwards [(V.nested_solution W d Cirrus.frontier).2,(V.nested_solution W 6 Cirrus.frontier).2, usable W Y g] with i ⟨H,_⟩ ⟨K,_⟩ h; exact ⟨H,K,h,proper _ _ i d H K,real_system W Y i d H, conditions W Y i d H, exact_χ W Y i K h⟩
end YM.XSpace.Rose
