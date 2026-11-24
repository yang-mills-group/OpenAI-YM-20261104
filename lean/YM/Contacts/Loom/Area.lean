import YM.Contacts.Loom.Index
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
variable {x: Frame α E}{d:ℕ→ℝ}{g:Shelf E α F}
variable {v: Shelf E α V}{u:Shelf E α F}
open ContinuousLinearMap
lemma Rush.fromOne (h:∀ᶠ i in atTop, ‖f i‖≤1): N.Rush 0 f:= (Rush.settle (M:=N) 1).view (h.mono fun i hi=> (norm_one (α:=ℝ)).symm ▸ hi) -- Meter binder
lemma Budget.operator {L : Shelf E α fun i=>(F i→L[ℝ] V i)} (h: Budget N x k p L) (hv:Budget N x k q u)(hh:p+q=r): Budget N x k r (fun i j x=> L i j x (u i j x)):= by
   let A i:= (ContinuousLinearMap.apply ℝ (V i) (E:=F i)).flip; have hA i: ‖A i‖≤1:= by apply opNorm_le_bound _ zero_le_one; intro u; apply opNorm_le_bound _ (by positivity); intro v; rw [one_mul]; exact u.le_opNorm v
   exact h.twins A hv (Rush.fromOne (Eventually.of_forall fun i=> by rw [Real.norm_of_nonneg (norm_nonneg (A i))]; exact hA i)) (by rw [hh,add_zero])
lemma Arms.pick_const {f:Shelf E α V}(h: Arms N x k p d f): N.Funds (fun i t=> ∀ j:α i, ‖f i j (x i j)‖≤t) p:= h.lift le_rfl (Eventually.of_forall fun i b _ h x=> (h x).bound)
lemma Budget.stack (h:Budget N x k p u)(he: Budget N x k p v): Budget N x k p (fun i j t=> (u i j t,v i j t)):= by
    let f (i:ℕ):= ContinuousLinearMap.inl ℝ (F i) (V i); let g (i:ℕ):= ContinuousLinearMap.inr ℝ (F i) (V i); have hf i: ‖f i‖ ≤ 1:= by apply opNorm_le_bound _ zero_le_one; intro x; simp [f]
    have hg i: ‖g i‖ ≤ 1:= by apply opNorm_le_bound _ zero_le_one; intro x; simp [g]
    exact Arms.sum (Arms.project f h (Rush.fromOne (Eventually.of_forall fun i=> by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using! hf i)) (add_zero p)) (Arms.project g he (Rush.fromOne (Eventually.of_forall fun i=> by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using! hg i)) (add_zero p)) |>.reveal (Eventually.of_forall fun i=>fun j=> Eventually.of_forall (fun k=> by simp only [f,g]; exact (Prod.ext (add_zero (u i j k)).symm (zero_add _).symm))) le_rfl le_rfl
lemma Budget.id (h: N.Funds (fun i b=> ∀ j:α i, ‖x i j‖≤ b) 0): Budget N x k 0 (fun i _ t=>t):= by obtain ⟨f,hf,H⟩:=h.cap; refine ⟨_,hf.blend (Rush.settle 1),H.mono (fun i hi=>?_ )⟩; refine ⟨add_nonneg hi.1 zero_le_one,fun j=> Brush.linearB (ContinuousLinearMap.id ℝ (E i)) ((hi.2 _).trans (le_add_of_nonneg_right zero_le_one)) (norm_id_le.trans ((by simpa using (le_add_of_nonneg_left hi.1 : (1:ℝ)≤f i+1)): (1:ℝ)≤ (f i+1)*1)) zero_le_one⟩
lemma Budget.natural {S:Shelf E α V}(L:∀ i,V i →L[ℝ] Y i)(h: Budget N x k p S)(ht:∀ i t, ‖L i t‖ ≤ ‖t‖): Budget N x k p (fun i j=> L i ∘ S i j) := by
   have he i: ‖L i‖ ≤ 1:= opNorm_le_bound _ zero_le_one fun x=> (ht i x).trans_eq (one_mul _).symm; exact Arms.project L h (Rush.fromOne (Eventually.of_forall fun i=> by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact he i)) (add_zero p)
local notation "μ" => Tensor.T
namespace Budget
open Arms
variable {S:Shelf E α fun i=> Tensor.T (F i) (V i) j}
section ply
variable {K J M : Type}[NormedAddCommGroup K][NormedSpace ℝ K][NormedAddCommGroup J][NormedSpace ℝ J][NormedAddCommGroup M][NormedSpace ℝ M]
variable {β:K}{Ω:K→μ J M j}{Β:K→J}
lemma bill_le {S:K→(J→L[ℝ] M)}(ht: Brush k p 1 S β)(hv:Brush k q 1 Β β): Brush k (p*q*3^k) 1 (fun x=> S x (Β x)) β:= by
    let F: (J→L[ℝ] M)→L[ℝ] J →L[ℝ] M:= (ContinuousLinearMap.apply ℝ M).flip
    have h: ‖F‖ ≤ 1:= opNorm_le_bound _ zero_le_one (fun y=>by rw [one_mul]; apply opNorm_le_bound _ (norm_nonneg _); exact fun x=> y.le_opNorm x)
    apply ((ht.twins hv F).trim).climb _ le_rfl; rw [show (1+(1+1):ℝ)=3 by norm_num]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (mul_nonneg ht.nonneg hv.nonneg) h) (by positivity)
lemma spaceShift {Q:K→J}(L:J ≃ₗᵢ[ℝ] M)(h:Brush k p 1 Q β): Brush k p 1 (fun x=> L (Q x)) β:= by rw [← one_mul p]; exact Brush.report h L.toContinuousLinearEquiv.toContinuousLinearMap (opNorm_le_bound _ zero_le_one (fun x=> L.norm_map x|>.le.trans_eq (one_mul _).symm))
lemma shine (h:Brush k q 1 Β β)(hf: Brush k p 1 Ω β): Brush k (p*(q*3^k)^j) 1 (fun x=>Tensor.diagonal (Ω x) (Β x)) β:= by
    induction j generalizing p with
    | zero=>
        rw [pow_zero,mul_one]; let L: μ J M 0→L[ℝ] M:=ContinuousMultilinearMap.apply ℝ _ _ 0; have he: ‖L‖≤1:=opNorm_le_bound _ zero_le_one (fun x=> (ContinuousMultilinearMap.fin0_apply_norm (x:=0) x).le.trans_eq (one_mul _).symm); rw [← one_mul p]; exact (hf.report L he).shimmy (Eventually.of_forall (fun x=> congr_arg (Ω x) (Subsingleton.elim (fun i₁:Fin 0=>Β x) 0)))
    | succ j ih =>
        let L:=continuousMultilinearCurryLeftEquiv ℝ (fun _:Fin (j+1)=> J) M; let D:=L.toLinearIsometry.toContinuousLinearMap
        have hS: Brush k p 1 (fun x=> (Ω x).curryLeft) β:= by
           exact spaceShift (M:=J→L[ℝ] J [×j]→L[ℝ] M) L hf
        rw [pow_succ',←mul_assoc, ← mul_assoc p]; exact (ih (bill_le hS h)).shimmy (Eventually.of_forall fun x=> congr_arg (Ω x) (by ext b; cases b using Fin.cases <;> rfl : (fun _:Fin (j+1)=>Β x)=Fin.cons (Β x) (fun _=> Β x)))
end ply
lemma sheet (hf: Budget N x k p S)(hp:Budget N x k q u): Budget N x k (p+q*j) (fun i j x=> Tensor.diagonal (S i j x) (u i j x)):= by
   obtain ⟨f,hf,H⟩:= hf.cap; obtain ⟨g,hg,hT⟩:=hp.cap; refine ⟨_,hf.times ((hg.bind ((3:ℝ)^k)).powers j) rfl,?_ ⟩; filter_upwards [H,hT] with i hi ht using ⟨mul_nonneg hi.1 (pow_nonneg (mul_nonneg ht.1 (by positivity)) j),fun j'=> shine (ht.2 j') (hi.2 j')⟩
lemma spike {X:Type} {s:Finset X}{a:X→ Shelf E α F} (h:∀ i ∈ s,Budget N x k p (a i)) : Budget N x k p (fun i j u => ∑ v∈s,a v i j u) := by
    refine (Arms.spoke s a (Eventually.of_forall fun i:ℕ=> (show 0 ≤ (1:ℕ→ℝ) i from zero_le_one)) h).reveal ?_ le_rfl le_rfl; exact Eventually.of_forall fun x y=> Eventually.of_forall fun z=> by simp only [Finset.sum_apply]
end Budget
-- Capture frames of localized balls. Belt estimate may need *maybe empty* at early clocks. Permit-meter handles.
variable (E)
def Frame.Bank (d:ℕ→ℝ)(i:ℕ): Set (E i):= ball 0 (d i)
abbrev Frame.Port (d:ℕ→ℝ): Frame (fun i=> ↥(Frame.Bank E d i)) E:= fun _=> Subtype.val
variable {E}
-- relaxed nail for only large t (p.Domain inclusion).
variable {A:Frame γ E}
lemma Arms.port {u₀:∀ i,E i→ V i} (h: Arms N (Frame.Port E d) k p f (fun i _=> u₀ i))(he:∀ᶠ i in atTop,∀ j, A i j ∈ Frame.Bank E d i) : Arms N A k p f (fun i _=> u₀ i):= h.lift le_rfl (he.mono fun i hi _ _ h j=> h ⟨_, hi j⟩)
end
end YM.Contacts.Loom
