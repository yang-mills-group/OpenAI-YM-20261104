import YM.FormalBulk08.Plait.Lam

/-! Read H and zero mark via letters, full derivative not assuming projected chart. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Filter Wick Orb Series Jets PowerSeries Lava Gorge Mesa Broc
open Matrix (of)
open scoped BigOperators Topology Classical Matrix ContDiff
variable {V I:Type*} [Fintype V][Fintype I]

def scars {T:Type*}(x:I→T)[Zero T]:= Sum.elim (0:V→T) x
def scalpel (V I:Type*)[Fintype V][Fintype I]: Jets.Rays I→L[ℝ] Jets.Rays (V⊕I):= LinearMap.toContinuousLinearMap {
   toFun x:= Sum.elim 0 x
   map_add' x y:= funext fun j=> by cases j <;> simp
   map_smul' c x:= funext fun j=> by cases j <;> simp }
lemma nerve (i:V⊕I): motor (scalpel V I) i = C (aftEval V I (MvPolynomial.X i)) := by
   unfold motor; cases i with
   | inl i=> rw [show (fun x=> scalpel V I x (.inl i))= (fun _: Jets.Rays I=> 0) from rfl,paste_flat]; ext1 n; simp [aftEval]
   | inr i=> rw [show (fun x=> scalpel V I x (.inr i))= (fun x=> x i) from rfl,paste_index]; ext1 n;cases n <;> simp [aftEval,coeff_X]
omit [Fintype V][Fintype I] in
lemma roots_col (p:Pap (V⊕I)): MvPolynomial.constantCoeff (emer V I (coeff 0 p))=aftEval V I (coeff 0 p):= by rw [remap]; unfold emer; rw [AlgEquiv.symm_apply_apply]
omit [Fintype V][Fintype I] in
lemma root_up (L:TypeR (V⊕I)): MvPolynomial.constantCoeff (emer V I L)=aftEval V I L:= by rw [remap]; unfold emer; rw [AlgEquiv.symm_apply_apply]
omit [Fintype V][Fintype I] in lemma roots_ink (p:Pap (V⊕I)): PowerSeries.map MvPolynomial.constantCoeff (PowerSeries.map (emer V I).toAlgHom.toRingHom p)=PowerSeries.map (aftEval V I).toRingHom p:= by ext1 n; simp only [coeff_map]; apply root_up
lemma scalpel_run (p:Pap (V⊕I)): roam ℝ (motor (scalpel V I)) p=PowerSeries.map (aftEval V I).toRingHom p:= by rw [roam, show insertAt ℝ _= C.comp (aftEval V I).toRingHom from ?_,pure_map]; ext <;> simp [nerve,aftEval]
lemma scales_pin (f: Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ∞ f 0)(n): MvPolynomial.constantCoeff (emer V I (coeff n (paste f)))=coeff n (paste (f∘ scalpel V I)):= by rw [paste_steps f _ h (scalpel V I).contDiff.contDiffAt (map_zero _),scalpel_run,coeff_map]; apply root_up

def chord (p:Pap (V⊕I))(n:ℕ):=emer V I (coeff n p)
def pearlD (f:Jets.Rays V→ℝ)(a:V)(v: Jets.Rays V): ℝ:= fderiv ℝ f v (dotI a)
lemma pearl_air (f:Jets.Rays V→ℝ)(a:V)(h:ContDiffAt ℝ ∞ f 0): ContDiffAt ℝ ∞ (pearlD f a) 0:= ContDiffAt.clm_apply (f:= fderiv ℝ f) (g:=fun _=>dotI a) (h.fderiv_right (by norm_num)) contDiffAt_const
lemma chord_grad (f: Jets.Rays (V⊕I)→ℝ)(h : ContDiffAt ℝ ∞ f 0)(a:V)(i): MvPolynomial.pderiv a (chord (paste f) (i+1))=chord (paste (pearlD f (Sum.inl a))) i := by
   rw [chord,emer,MvPolynomial.pderiv_sumAlgEquiv,← coeff_shaft,gradient f _ h,coeff_succ_X_mul]; rfl
lemma chord_sym (f: Jets.Rays (V⊕I)→ℝ)(_: ContDiffAt ℝ ∞ f 0)(i): Tally (chord (paste f) i) i:= by
   rw [Tally,chord,emer, AlgEquiv.symm_apply_apply]; exact paste_grade ..
lemma chord_root (f:Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ∞ f 0)(i): MvPolynomial.constantCoeff (chord (paste f) i) = coeff i (paste (f ∘ scalpel V I)):= scales_pin f h i
-- critical data
def gateP (f:Jets.Rays (V⊕I)→ℝ): Matrix V V (Jets.Rays I→ℝ):= of fun a b=> pearlD (pearlD f (.inl b)) (.inl a) ∘ scalpel V I
lemma gale_caps (f:Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ∞ f 0)(i j): ContDiffAt ℝ ∞ (gateP f i j) 0:= by simp only [gateP,Matrix.of_apply]; exact ContDiffAt.comp _ (by rw [map_zero]; exact pearl_air _ _ (pearl_air _ _ h)) (scalpel V I).contDiff.contDiffAt
lemma chord_money (f:Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ∞ f 0)(i:ℕ)(a b: V): MvPolynomial.constantCoeff (MvPolynomial.pderiv a (MvPolynomial.pderiv b (chord (paste f) (i+2))))=(fort (litR (gateP f)) i) a b := by
    rw [chord_grad f h, chord_grad _ (pearl_air _ _ h), chord_root _ (pearl_air _ _ (pearl_air _ _ h))];rfl
lemma chord_gate (f: Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ∞ f 0)(i): (fort (litR (gateP f)) i)ᵀ=fort (litR (gateP f)) i:= by
   ext1 a b; simp only [Matrix.transpose_apply,← chord_money f h, Wick.alphabet_swap b a]

def Chilly (f:Jets.Rays (V⊕I)→ℝ):= ∀ i:V, (pearlD f (.inl i) ∘ scalpel V I) =ᶠ[𝓝 0] 0
lemma unpaid (f:Jets.Rays (V⊕I)→ℝ)(h: ContDiffAt ℝ ∞ f 0)(p:Chilly f)(i n): MvPolynomial.constantCoeff (MvPolynomial.pderiv i (chord (paste f) (n+1)))=0 := by
    rw [chord_grad f h,chord_root _ (pearl_air _ _ h), paste_replace (p i), show paste (0:Jets.Rays I→ℝ)=0 by change paste (fun _=>0)=_; simp only [paste_flat,map_zero],map_zero]
-- use active-count proof: residual cubic absent in degree2
omit [Fintype V][Fintype I] in lemma life_low {p:Pairs V I}(h:Tally p 0): p=MvPolynomial.C (MvPolynomial.constantCoeff p) := by
    let F:= MvPolynomial.sumAlgEquiv ℝ V I; have he: ∃ a:ℝ, F.symm p=MvPolynomial.C a:= ⟨_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp (Nat.le_zero.mp (MvPolynomial.IsHomogeneous.totalDegree_le h))⟩
    obtain ⟨a,ha⟩:=he; have ht:p=_:=(F.apply_symm_apply p).symm.trans (congr_arg F ha);rw [ht]; simp only [F, MvPolynomial.sumAlgEquiv_C_inl,MvPolynomial.constantCoeff_C]
lemma chord_sight (f: Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ∞ f 0)(a b:V): MvPolynomial.pderiv a (MvPolynomial.pderiv b (chord (paste f) 2))= MvPolynomial.C ((fort (litR (gateP f)) 0) a b):= by
    rw [←chord_money f h]; exact life_low (p:= MvPolynomial.pderiv a (MvPolynomial.pderiv b _)) (((chord_sym f h 2).step b).step a)
lemma chord_center (f:Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ∞ f 0)(hp:Chilly f):
    let B:= fort (litR (gateP f)) 0;
    -chord (paste f) 2=MvPolynomial.C (-coeff 2 (paste (f∘ scalpel V I))) + rect B := by
   intro B; apply pin_check
   · intro i; apply pin_check
     · intro j; rw [map_neg,map_neg,map_add,MvPolynomial.pderiv_C,zero_add, chord_sight f h j i,rect_cease (chord_gate f h 0)]
     rw [map_add,MvPolynomial.pderiv_C,zero_add, rect_trim (chord_gate f h 0),map_neg,map_neg,show MvPolynomial.constantCoeff _=_ from unpaid f h hp i 1,neg_zero]
   rw [map_neg,chord_root f h,map_add,rect_corner,MvPolynomial.constantCoeff_C,add_zero]
end YM.FormalBulk08.Plait
