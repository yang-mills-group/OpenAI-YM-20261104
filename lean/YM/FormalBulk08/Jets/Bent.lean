import YM.FormalBulk08.Orb.Waft

/-! Analytic adapter for the Jacobian and leading shift of a slice map. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Jets
open Series Wick Orb Matrix PowerSeries Function Filter Set
open scoped BigOperators Classical Topology ContDiff
variable {V I : Type*} [Fintype V] [Fintype I] (F : Rays (V⊕I)→ Rays V) (h : F 0=0) (H : ContDiffAt ℝ ∞ F 0)
-- matrix derivative spelling
variable [DecidableEq V]
def dollars (x : Rays (V⊕I)) : Matrix V V ℝ := Matrix.of fun i j=> fderiv ℝ (fun x=>F x i) x (dotI (Sum.inl j))
omit [DecidableEq V] in
lemma inlay_zero (i : V) (p:Rays (V⊕I)) : traceP p (coeff 0 (motor F i))=fderiv ℝ (fun x=> F x i) 0 p := by
   simp_rw [motor,after_one,trace_paste]; simp [PertExtension.Series.Radial.jet]
lemma solitary (i : V) (p:Rays (V⊕I)) : fderiv ℝ (fun x=>F x i) 0 p=
    ∑ j,dollars F 0 i j * p (Sum.inl j) + ∑ j:I,p (Sum.inr j) * (fderiv ℝ (fun x=>F x i) 0 (dotI (Sum.inr j))) := by
    nth_rw 1 [← show ∑ j,p j • dotI j=p from (by ext a; simp [dotI,Pi.single_apply,mul_ite])];
    rw [map_sum,Fintype.sum_sum_type]; simp_rw [map_smul,smul_eq_mul];congr 1
    apply Finset.sum_congr rfl; intro j _; exact mul_comm ..
lemma inlay : ∃ Z,∀ i,coeff 0 (motor F i)=glide (dollars F 0) Z i := by
   refine ⟨fun i=> ∑ j, MvPolynomial.X j * MvPolynomial.C (fderiv ℝ (fun x=> F x i) 0 (dotI (Sum.inr j))), fun i=>?_⟩
   apply orbit_ext; intro x; rw [inlay_zero,solitary]; simp [glide,traceP, mixRows]
section
include H
omit [DecidableEq V] in
lemma collar (i j) : ContDiffAt ℝ ∞ (fun z=>dollars F z i j) 0 := by
   apply ContDiffAt.clm_apply (f:=fderiv ℝ (fun x=> F x i)) (g:=fun _ => dotI (Sum.inl j)) _ contDiffAt_const
   exact (coord_diff F H i).fderiv_right (by norm_num)

omit H in
lemma dollars_act (x : Rays (V⊕I)) (hp : DifferentiableAt ℝ F x) : (LinearMap.toMatrix' (fderiv ℝ F x).toLinearMap).submatrix id Sum.inl = dollars F x := by
   ext1 i j
   have he := ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : V=>ℝ) i).hasFDerivAt.comp x hp.hasFDerivAt).fderiv
   dsimp only [dollars,Matrix.of_apply, Matrix.submatrix_apply,id_eq]; rw [LinearMap.toMatrix'_apply]; change fderiv ℝ (fun x=> F x i) x=_ at he; rw [he]; simp [dotI]; congr!
end

omit [Fintype V] [DecidableEq V] in
lemma drawing (f : V→Rays I→ℝ) (u : Finset V) (hf : ∀ i∈u,ContDiffAt ℝ ∞ (f i) 0) : ContDiffAt ℝ ∞ (∏ i∈u,f i) 0 := by
   induction u using Finset.induction_on with
   | empty=> rw [Finset.prod_empty]; exact contDiffAt_const
   | insert i u hi ih=> rw [Finset.prod_insert hi]; exact (hf i (by simp)).mul (ih (fun j hj=>hf j (by simp [hj])))

omit [Fintype V] [DecidableEq V] in
lemma shaving (f : V→Rays I→ℝ) (u : Finset V) (hf : ∀ i∈u,ContDiffAt ℝ ∞ (f i) 0) : paste (∏ i∈u,f i)=∏ i∈u,paste (f i) := by
   induction u using Finset.induction_on with
   | empty=> rw [Finset.prod_empty,Finset.prod_empty]; exact (show paste (fun _ : Rays I=> (1:ℝ))=1 by rw [paste_flat,map_one,map_one])
   | insert i u hi ih=>
     have hp (j) (h:j∈u) := hf j (Finset.mem_insert_of_mem h)
     rw [Finset.prod_insert hi, Finset.prod_insert hi,paste_mul _ _ (hf i (by simp)) (drawing _ _ hp),ih hp]

omit [Fintype V] [DecidableEq V] in
lemma garter (f : V→Rays I→ℝ) (u : Finset V) (hf : ∀ i∈u,ContDiffAt ℝ ∞ (f i) 0) : paste (∑ i∈u,f i)=∑ i∈u,paste (f i) := by
   induction u using Finset.induction_on with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact (show paste (fun _ : Rays I=> (0:ℝ))=0 by rw [paste_flat,map_zero,map_zero])
   | insert i u hi ih=>
     have hp (j) (h:j∈u) := hf j (Finset.mem_insert_of_mem h)
     have he : ContDiffAt ℝ ∞ (∑ i∈u,f i) 0 := by convert! ContDiffAt.sum hp using 1; ext; simp
     rw [Finset.sum_insert hi, Finset.sum_insert hi,paste_sum _ _ (hf i (by simp)) he,ih hp]

section
include h H
lemma rent : (inset (motor F)).det = paste (fun p => (dollars F p).det) := by
   let v (a : Equiv.Perm V) (j : V) := fun p:Rays (V⊕I)=> dollars F p (a j) j
   let s (a : Equiv.Perm V) := fun _: Rays (V⊕I)=> (↑(a.sign : ℤ):ℝ)
   have he a: ContDiffAt ℝ ∞ (s a*(∏ j,v a j)) 0:= contDiffAt_const.mul (drawing _ _ (fun i _=> collar F H _ _))
   rw [show (fun p => (dollars F p).det) = ∑ a,s a*(∏ j,v a j) from funext fun x=> by simp [s,v,Finset.prod_apply,Matrix.det_apply'], garter _ _ (fun a _ => he a)]
   rw [Matrix.det_apply'];refine Finset.sum_congr rfl fun i _=> ?_
   rw [paste_mul _ _ (contDiffAt_const (c:=(s i 0))) (drawing _ _ (fun j _ => collar F H (i j) j)), shaving _ _ (fun j _=> collar F H (i j) j)]
   simp only [s, paste_flat,map_intCast]; congr 1; apply Finset.prod_congr rfl;intro j _; exact motor_diff F h H _ _
end
end YM.FormalBulk08.Jets
