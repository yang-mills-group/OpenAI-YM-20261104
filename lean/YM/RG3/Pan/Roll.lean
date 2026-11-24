import YM.RG3.Pan.Album
/-!
# A finite-order budget with true scale per Hit

Use in making actual jets from curvature germs, INCLUDING changing paths.
Curry grouping is explicit in derivative dimensions. Don't pay width per
coefficient order without recording. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan
open Function FreeResolvent Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
 [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
 {k : ℕ} {f : E→F} {x : E} {g : F→Y} {A d : ℝ}

structure Bill (k : ℕ) (A d : ℝ) (f : E→F) (x : E) : Prop where
  smooth : ContDiffAt ℝ k f x
  B i : i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ A*d^i

lemma Bill.down (h : Bill k A d f x) {n : ℕ} (hn : n ≤ k) : Bill n A d f x:=
  ⟨h.smooth.of_le (by exact_mod_cast hn),fun j hj => h.B _ (hj.trans hn)⟩

lemma Bill.up {A' : ℝ} (h : Bill k A d f x) (hd : 0 ≤ d) (hA : A ≤ A') : Bill k A' d f x :=
  ⟨h.smooth,fun _ hi => (h.B _ hi).trans (mul_le_mul_of_nonneg_right hA (pow_nonneg hd _))⟩

lemma Bill.drift {d' : ℝ} (h : Bill k A d f x) (hd : 0 ≤ d) (ht : d ≤ d') (hA : 0 ≤ A) : Bill k A d' f x :=
  ⟨h.smooth,fun _ hi=> (h.B _ hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd ht _) hA)⟩

lemma Bill.pos (h : Bill k A d f x) : 0 ≤ A:= by simpa using! ((norm_nonneg _).trans (h.B 0 (Nat.zero_le _)))

lemma Bill.cost (h : Bill k A d f x) : ‖f x‖ ≤ A := by
  simpa only [pow_zero, norm_iteratedFDeriv_zero,mul_one] using h.B 0 (Nat.zero_le _)

def joinFee (k : ℕ) : ℝ := ∑ j∈Finset.range (k+1), Fintype.card (OrderedFinpartition j)
lemma joinFee_nn (k : ℕ) : 0 ≤ joinFee k := Finset.sum_nonneg fun _ _=> Nat.cast_nonneg _
lemma joinFee_ge (k j : ℕ) (h : j ≤ k) : (Fintype.card (OrderedFinpartition j):ℝ) ≤ joinFee k := Finset.single_le_sum
  (f:=fun j : ℕ=> (Fintype.card (OrderedFinpartition j):ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
lemma one_le_joinFee (k : ℕ) : 1 ≤ joinFee k := le_trans (show (1:ℝ)≤ Fintype.card (OrderedFinpartition 0) from by exact_mod_cast Fintype.card_pos (α:=OrderedFinpartition 0)) (joinFee_ge _ _ (Nat.zero_le _))

def cap (k : ℕ) (A C e : ℝ) := joinFee k * C*(1+A*e)^k
lemma cap_nn (k : ℕ) {A C e : ℝ} (hA:0≤A) (hC:0≤C) (he:0≤e) : 0≤ cap k A C e := by
  have := joinFee_nn k; unfold cap; positivity
lemma cap_ge (k : ℕ) {A C e : ℝ} (hA:0≤A) (hC:0≤C) (he:0≤e) : C ≤ cap k A C e := by
  have ho : (1:ℝ)≤(1+A*e)^k:=one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hA he))
  simpa [cap] using! mul_le_mul (mul_le_mul_of_nonneg_right (one_le_joinFee k) hC) ho (show 0≤(1:ℝ) by norm_num) (mul_nonneg (joinFee_nn k) hC)

lemma factors (t A : ℝ) {j} (p : OrderedFinpartition j):
    ∏ r : Fin p.length,(A*t^(p.partSize r)) = A^p.length * t^j := by
  rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  simpa using p.prod_sigma_eq_prod (fun _=>(t:ℝ))

lemma Bill.comp {C e : ℝ} (h : Bill k A d f x) (hg : Bill k C e g (f x)) (he : 0≤e) (hd : 0≤d) :
    Bill k (cap k A C e) d (g ∘ f) x:= by
  have hA:=h.pos; have hC:=hg.pos
  refine ⟨hg.smooth.comp _ h.smooth,fun j hj=>?_⟩
  let p1(j):=iteratedFDeriv ℝ j g (f x)
  let p2(j):=iteratedFDeriv ℝ j f x
  rw [iteratedFDeriv_comp hg.smooth h.smooth (Nat.cast_le.mpr hj), FormalMultilinearSeries.taylorComp]
  refine (norm_sum_le ..).trans ?_
  have hv (p : OrderedFinpartition j) := p.norm_compAlongOrderedFinpartition_le (p1 p.length) (fun i=>p2 (p.partSize i))
  have ht (p : OrderedFinpartition j) : ‖p.compAlongOrderedFinpartition (p1 p.length) (fun i=>p2 (p.partSize i))‖ ≤ C*((1+A*e)^k)*d^j := by
    refine (hv p).trans ((mul_le_mul (hg.B _ (p.length_le.trans hj)) (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _ => h.B _ ((p.partSize_le i).trans hj))) (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) (mul_nonneg hC (pow_nonneg he _))).trans ?_)
    rw [factors]
    calc
      _ = C*(A*e)^p.length*d^j := by rw [mul_pow]; ring
      _ ≤ _ := by
        have he': 1≤1+A*e:= le_add_of_nonneg_right (mul_nonneg hA he)
        gcongr
        exact (pow_le_pow_left₀ (mul_nonneg hA he) (by linarith) _).trans (pow_le_pow_right₀ he' (p.length_le.trans hj))
  refine (Finset.sum_le_sum (fun i _=>ht i)).trans ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold cap
  exact (mul_le_mul_of_nonneg_right (joinFee_ge k j hj) (by positivity)).trans_eq (by ring)

/-- Pi norm with no Fintype.card overhead. -/
lemma Bill.bundle {ι : Type*} [Fintype ι] {F' : ι → E → F} (hA : 0 ≤ A) (hd : 0 ≤ d)
    (h : ∀ i, Bill k A d (F' i) x):Bill k A d (fun z i=> F' i z) x:= by
  have he : ContDiffAt ℝ k (fun z i=>F' i z) x := contDiffAt_pi.mpr (fun i=> (h i).smooth)
  refine ⟨he, fun j hj=>?_⟩
  let V:= fun z i=>F' i z
  let T:=iteratedFDeriv ℝ j V x
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun l=> ?_)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hx := (ContinuousLinearMap.proj (φ:=fun _ : ι=>F) (R:=ℝ) i).iteratedFDeriv_comp_left he (i:=j) (by exact_mod_cast hj)
  have hr : T l i=iteratedFDeriv ℝ j (F' i) x l:= (congr_arg (fun w : E[×j]→L[ℝ] F=> w l) hx).symm
  change ‖T l i‖ ≤ _; rw [hr]; exact (ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ((h _).B _ hj) (by positivity))

/-- Constants may be charged even at arbitrary scale. -/
lemma fixed (z : F) (k : ℕ) (x : E) (hd : 0 ≤ d) : Bill k ‖z‖ d (fun _ : E=>z) x:= by
  refine ⟨contDiffAt_const,fun j _=>?_⟩
  cases j; simp
  rename_i j _; simp only [iteratedFDeriv_succ_const]; simpa only [Pi.zero_apply,norm_zero] using mul_nonneg (norm_nonneg z) (pow_nonneg hd (j+1))

lemma Bill.plus {A' : ℝ} {g : E→F} (h : Bill k A d f x) (hg : Bill k A' d g x) : Bill k (A+A') d (fun z=>f z+g z) x:= by
  refine ⟨h.smooth.add hg.smooth,fun j hj=>?_⟩
  have ht : (j:ℕ∞ω) ≤ k:=by exact_mod_cast hj
  rw [fun_iteratedFDeriv_add_apply (h.smooth.of_le ht) (hg.smooth.of_le ht), add_mul]
  exact (norm_add_le ..).trans (add_le_add (h.B _ hj) (hg.B _ hj))

lemma Bill.minus {A' : ℝ} {g : E→F} (h : Bill k A d f x) (hg : Bill k A' d g x) : Bill k (A+A') d (fun z=>f z-g z) x:= by
  refine ⟨h.smooth.sub hg.smooth,fun j hj=>?_⟩
  have ht : (j:ℕ∞ω) ≤ k:=by exact_mod_cast hj
  change ‖iteratedFDeriv ℝ j (f-g) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (h.smooth.of_le ht) (hg.smooth.of_le ht), add_mul]
  exact (norm_sub_le ..).trans (add_le_add (h.B _ hj) (hg.B _ hj))

/-- Postcompose with a genuinely bounded real linear map (no analyticity
price on target matrix dimensions). -/
lemma Bill.emit {C : ℝ} (L : F→L[ℝ] Y) (hC : 0 ≤ C) (hL : ∀ v, ‖L v‖ ≤ C*‖v‖) (hd : 0 ≤ d)
    (h : Bill k A d f x): Bill k (C*A) d (L ∘ f) x:= by
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth,fun j hj=>?_⟩
  have ht : (j:ℕ∞ω) ≤ k:=by exact_mod_cast hj
  rw [L.iteratedFDeriv_comp_left h.smooth ht]
  refine (FreeResolvent.Affine.slot_op (mul_nonneg (mul_nonneg hC h.pos) (pow_nonneg hd _)) (fun v hv=>?_))
  change ‖L ((iteratedFDeriv ℝ j f x) v)‖ ≤ _; rw [mul_assoc]; refine (hL _).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact ((ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ hv)).trans (by simpa using h.B _ hj)

lemma song_bill {G : Gauge} {ι} {u : ι→E→G.El} (p : List ι) (hA : 0≤A) (ht : 0≤d) (h : ∀ i∈p, GroupHit k A d (u i) x):
    Bill k ‖(1:G.Mat)‖ ((1+2^k*A*p.length)*d) (G.mat∘bands u p) x := by
  obtain ⟨he,h⟩:=chorus u p hA ht h
  refine ⟨he,fun i hi=> (h i hi).trans_eq ?_⟩; unfold light; rw [mul_pow,mul_assoc]

lemma Bill.cast {G : Gauge} {u : E→G.El} (h : Bill k A d (G.mat ∘ u) x) : GroupHit k A d u x:= ⟨h.smooth, fun i _=> h.B i⟩

end YM.RG3.Pan
