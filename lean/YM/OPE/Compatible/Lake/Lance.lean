import YM.OPE.Compatible.Lake.Encore
/-! Scaling remedy. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof
open Next.Rank Extraction
open ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G}
variable {d i:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)] [∀ i,FiniteDimensional ℂ (E i)]
local notation "I"=> Fin (d+1)

-- material step model rubric. actual residual style
structure Treaty (L η U:ℝ)(F: Dock E≃L[ℂ] Dock E) :Prop where
    toC : team F.toContinuousLinearMap
    ofC : team F.symm.toContinuousLinearMap
    grace (i:I): ‖route F.toContinuousLinearMap i i‖ ≤ L^(d-i.val)*η
    value (i:I): ‖route F.symm.toContinuousLinearMap i i‖≤ (L^(d-i.val))⁻¹*η
    charge : ‖F.toContinuousLinearMap‖ ≤ U
    inverse : ‖F.symm.toContinuousLinearMap‖ ≤ U
omit [∀ i,FiniteDimensional ℂ (E i)] -- continuous pi can explicit
private def levelLine (x:ℝ) :Train E:=ContinuousLinearMap.pi (fun i=> ((Real.exp (x*(i.val:ℝ)):ℝ):ℂ) • ContinuousLinearMap.proj i)
def guardF (x:ℝ): Dock E ≃L[ℂ] Dock E :=
 { (levelLine x (E:=E)) with
    invFun := levelLine (-x)
    left_inv:=fun v=>by ext1 i; change (↑(Real.exp (-x * (i.val:ℝ))):ℂ) • ((↑(Real.exp (x * (i.val:ℝ))):ℂ) • v i) = _; rw [smul_smul, neg_mul,Real.exp_neg, Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), one_smul]
    right_inv:=fun v=>by ext1 i; change (↑(Real.exp (x*(i.val:ℝ))):ℂ) • ((↑(Real.exp (-x*(i.val:ℝ))):ℂ) • v i) = _; rw [smul_smul,neg_mul,Real.exp_neg, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),one_smul]
    continuous_toFun:= by apply (levelLine x).continuous
    continuous_invFun:= by apply (levelLine (-x)).continuous }
lemma barInverse (x:ℝ): (guardF x (E:=E)).symm=guardF (-x):=by ext1;rfl
abbrev cram (C:Family G)(E: Fin (d+1)→Type)[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℂ (E i)](s:ℝ)(i:ℕ) := guardF (E:=E) (-s*hill C i)
lemma voyage (x y:ℝ)(F: Dock E ≃L[ℂ] Dock E)(i j:I): route ((guardF x |>.trans F).trans (guardF y)).toContinuousLinearMap i j= (((Real.exp (x*j.val+y*i.val)):ℝ):ℂ) • route F.toContinuousLinearMap i j:=by
   ext1 u
   rw [Real.exp_add]; unfold route; change (↑(Real.exp (y*↑i.val)):ℂ) • (F (guardF x (ContinuousLinearMap.single ℂ E j u))) i = (↑(Real.exp (x*↑j.val)*Real.exp (y*↑i.val)):ℂ) • (route F.toContinuousLinearMap i j u)
   rw [show guardF x (ContinuousLinearMap.single ℂ E j u) = (↑(Real.exp (x*↑j.val)):ℂ) • (ContinuousLinearMap.single ℂ E j u) from ?_, F.map_smul,Pi.smul_apply,smul_smul,Complex.ofReal_mul,mul_comm]
   · rfl
   ext1 l; by_cases h:l=j; subst l; rfl
   change ((↑(Real.exp _)):ℂ) • Pi.single j u l=(_ : ℂ) • Pi.single j u l; rw [Pi.single_eq_of_ne h]; simp
lemma barCost (x:ℝ)(z:ℝ) (hz:∀ i:I, x*(i.val:ℝ)≤z): ‖(guardF (E:=E) x).toContinuousLinearMap‖ ≤ Real.exp z:= by
   apply opNorm_le_bound _ (Real.exp_nonneg _); intro p; refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).2 fun i=>?_ ; change ‖(↑(Real.exp _):ℂ) • (p i)‖≤_; rw [norm_smul,Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]; exact mul_le_mul (Real.exp_monotone (hz i)) (norm_le_pi_norm p i) (norm_nonneg _) (Real.exp_nonneg _)
lemma sand (C:Family G){s:ℝ}(hs:0 ≤ s) (i:ℕ): ‖(cram C E s i).toContinuousLinearMap‖ ≤ 1 ∧ ‖(cram C E s i).symm.toContinuousLinearMap‖ ≤ Real.exp ((d:ℝ)*s*hill C i):=by
   constructor
   · rw [← Real.exp_zero]; refine barCost _ _ fun j=> mul_nonpos_of_nonpos_of_nonneg ?_ (Nat.cast_nonneg _); exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (hill_pos C _|>.le)
   rw [cram,barInverse]; refine barCost _ _ fun j=>?_ ; linarith only [mul_le_mul_of_nonneg_left (show (j.val:ℝ)≤(d:ℝ) by exact_mod_cast Nat.le_of_lt_succ j.isLt) (mul_nonneg hs (hill_pos C i|>.le))]
namespace Treaty
variable (h:G.Simple)
variable {U s t:ℝ}(F:Dock E≃L[ℂ] Dock E)(H:Treaty (extent C i) (Real.exp (t*levy C i)) U F)

abbrev rescale (F:Dock E≃L[ℂ]Dock E)(V W: Dock E≃L[ℂ] Dock E):Dock E≃L[ℂ]Dock E:=(V.symm.trans F).trans W
local notation "X"=> rescale F (cram C E s (i+1)) (cram C E s i)
local notation "f"=> -(s*hill C i)
local notation "g"=> -(s*hill C (i+1))
local notation "c(i)"=> f --test
-- strict upper
lemma axesX (j k:I): route (X).toContinuousLinearMap j k= ((Real.exp ((-g)*k.val+f*j.val):ℝ):ℂ) • route F.toContinuousLinearMap j k ∧ route (X).symm.toContinuousLinearMap j k= ((Real.exp ((-f)*k.val+g*j.val):ℝ):ℂ) • route F.symm.toContinuousLinearMap j k:=by
     let a:= cram C E s (i+1); let b:= cram C E s i
     have he: a=guardF g:=by unfold a cram; rw [neg_mul]
     have hh: b=guardF f:=by unfold b cram; rw [neg_mul]
     constructor
     · change route (rescale _ a b).toContinuousLinearMap j k=_; rw [he,hh,rescale,barInverse]; exact voyage ..
     rw [show (X).symm=(b.symm.trans F.symm).trans a from rfl,he,hh,barInverse]; exact voyage ..

include H
end Treaty
end YM.OPE.Lake
