import YM.UVExt.MetricPort

/-! Removing only the common, TRUE cover row convolution with parallel root lift in the squared term. Difference-of-routes still paid by the curvature estimate at full lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Wilson Lattice Precision Laurent Exterior Bid Filter Real Set Matrix Bloch Next.Free
open Next.Free.UV Work.F03 Work.F08
open scoped ContDiff Topology Classical InnerProductSpace BigOperators
set_option linter.unusedSectionVars false
variable {G : Gauge} {a : Levels G} {k l : ℝ} {H H' : ℕ→Bed} {M M' : ℕ→PathData G} {p : Clip}
    {σ C Λ σ' C' Λ': ℝ} {W X : Shadow G} {m : ℕ}
    (h : Harbor a m k l H M p) (hT : Passing M W σ C Λ p) (h' : Harbor a m k l H' M' p) (ht : Passing M' X σ' C' Λ' p)

private lemma square_compare {n : Side} {A B : Bed} (c : Clip) (h : (A.full c n).transpose * A.full c n=(B.full c n).transpose*B.full c n) :
    (A.roots.acts n).transpose * A.roots.acts n=(B.roots.acts n).transpose * B.roots.acts n := by
  ext i j
  let low (b : Site n) z := (Real.sqrt c.direct * (1:Matrix (Body 2 n) (Body 2 n) ℝ) (b,z) i)*(Real.sqrt c.direct * (1:Matrix (Body 2 n) (Body 2 n) ℝ) (b,z) j)
  have hZ (A : Bed) : ((A.full c n).transpose * A.full c n) i j = ( ∑ b : Site n, ∑ z:TypeFace 2, low b z) + ((A.roots.acts n).transpose * A.roots.acts n) i j := by
    simp_rw [Matrix.mul_apply,Fintype.sum_prod_type, Fintype.sum_sum_type,Finset.sum_add_distrib]; rfl
  exact (add_right_inj _).mp ((hZ A).symm.trans ((congr_arg (fun x : Matrix _ _ _=> x i j) h).trans (hZ B)))

def correlated (M : Bed) := composeRows (transRows M.roots) M.roots

include h hT h' ht
set_option maxRecDepth 4000 in
lemma correlators : correlated (groundBed W)=correlated (groundBed X) := by
    have hW : (groundBed W).roots.strip σ C := budget_root _ _ (fun r b d=> ground_ties W r d b) hT.limit.row hT.width
    have hX : (groundBed X).roots.strip σ' C' := budget_root _ _ (fun r b d=> ground_ties X r d b) ht.limit.row ht.width
    have hv n := square_compare _ <| h.same_acts hT h' ht n
    have hg n (B : Bed) {u v} (hu : 0≤u) (h : B.roots.strip u v) : (correlated B).acts n= (B.roots.acts n)ᵀ * B.roots.acts n := by
        unfold correlated; rw [acts_compose hu (strip_trans h) h, acts_trans]
    have hB : ∀ n,(correlated (groundBed W)).acts n = (correlated (groundBed X)).acts n := fun n=> by rw [hg _ _ hT.width.le hW,hg _ _ ht.width.le hX]; exact hv n
    have hS (M : Bed) {u v} (hu : 0 ≤ u) (h : M.roots.strip u v) (i j) : Summable (fun t=>‖correlated M i j t‖) := (strip_compose hu (strip_trans h) h i j).summable hu |>.norm
    let D (i : ℕ) : Lattice.Side := ⟨i+1,by omega⟩
    have hD : Tendsto (fun n=> (D n).val) atTop atTop := tendsto_atTop_mono (fun (i:ℕ)=>show id i ≤ i+1 by simp) tendsto_id
    exact restore_rows hD (hS _ hT.width.le hW) (hS _ ht.width.le hX) fun i=>hB (D i)

lemma base_match {n : Side} (v : Dir G n) : qulit W false v p=qulit X false v p := by
  have hsame (t : Rel) : (∑ i:PlaqAxes,reduced (score W i) t)=(∑ i:PlaqAxes,reduced (score X i) t) := by
    show _=_ -- suppress parser
    exact (reduced_root (fun r b d=>ground_ties W r d b) hT.limit.row hT.width t.1 t.2.1 t.2.2).trans <| Eq.trans ((congr_arg (fun A=> A (plaquette t.1) (plaquette t.2.1) t.2.2) (correlators h hT h' ht))) ((reduced_root (fun r b d=>ground_ties X r d b) ht.limit.row ht.width t.1 t.2.1 t.2.2).symm)
  let Q (Z : Shadow G) (v : Dir G n) (x : Site n) (r : ℝ) (i : Rel) := (∑ k:PlaqAxes, reduced (score Z k) i) * ∑ j:G.ColorIndex, stream v x (savePlane i j) r
  have hd {Z : Shadow G} {u C C'} (h : PaidShadow Z C C' u) (hu : 0<u) (v : Dir G n) (x:Site n) (r) :
     HasSum (Q Z v x r) (∑ k:PlaqAxes, liftAir v false x (fun p=>score Z k p.1) r) := by
       dsimp only [Q]
       simp_rw [Finset.sum_mul]
       apply hasSum_sum -- maybe
       exact fun a _ => reduced_air _ (paid_chord Z h a) hu _ _ r
  have hAir (v : Dir G n) (x) : (∑ k:PlaqAxes, liftAir v false x (fun p=>score W k p.1)) = (∑ k:PlaqAxes,liftAir v false x (fun p=>score X k p.1)) := by
    funext r; rw [Finset.sum_apply,Finset.sum_apply]
    exact (Eq.symm (hd hT.limit hT.width v x r).tsum_eq).trans ((tsum_congr fun p=> by unfold Q; rw [hsame]).trans (hd ht.limit ht.width v x r).tsum_eq)
  unfold qulit facet
  apply congr_arg ((Fintype.card Signed:ℝ)⁻¹ • ·) (Finset.sum_congr rfl (fun i _=> ?_))
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.smul_sum,←Finset.smul_sum]
  simp only [Fintype.sum_prod_type]; congr 1; congr 1; exact Finset.sum_congr rfl fun x _=>hAir _ x

lemma upper_residue (n : Side) (q : ℕ) (e : q=3∨q=4) (v : Dir G n) (htC : σ'=σ) (hpC : C'=C) :
    |tag q (payload W v p)-tag q (payload X v p)| ≤ 2*(Fintype.card (Face (Per n)):ℝ)*reel G q C σ ‖v‖ ‖dColor G n 1 v‖ := by
  subst hpC; subst htC
  rw [show tag q _ - tag q _= qulitGap q v W p-qulitGap q v X p by unfold qulitGap; rw [base_match h hT h' ht v]; ring]
  exact (abs_sub _ _).trans ((add_le_add (missing_budget v e hT.width hT.limit) (missing_budget v e hT.width ht.limit)).trans_eq (by ring)) -- abs_sub_le?

omit h' ht
lemma fiscal_given {z : ℕ} : ∀ᶠ i : ℕ in atTop,
      let U := knotted (a.S.side m z) p (M i)
      U 0=0 ∧ fderiv ℝ U 0=0 ∧ ∀ x y, iteratedFDeriv ℝ 2 U 0 ![x,y]=gaugeFiscal (H i) x y := by
  filter_upwards [h.full (a.S.side m z),hT.mask,h.symmetry z,h.ties] with i hf hb hs ht
  obtain ⟨u,v,hf⟩ := hf; dsimp only []
  apply Work.F03.hessian_of_limit ((main_analytic _ hb).of_le le_top) (main_limit hb ht hf hs ·) gaugeFiscal_add
  intro x y
  rw [metric_pair _ hb ht x y hf,metric_pair _ hb ht y x hf]
  refine Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (faceCurl _ y),real_inner_comm (ellLine _ _ y)]

def fiscal (n:Side) (Y : Matrix (Body 2 n) (Body 2 n) ℝ) (x : Dir G n) := ∑ i:G.ColorIndex,dotProduct (parts G 1 x i) ((Precision.K Y) *ᵥ parts G 1 x i)
omit h hT in
private lemma fiscal_tends {n : Side} {Z : Matrix (Body 2 n) (Body 2 n) ℝ} {M : ℕ→Matrix (Body 2 n) (Body 2 n) ℝ} (hh : Tendsto (fun i:ℕ=>M i) atTop (𝓝 Z)) (x : Dir G n) :
    Tendsto (fun i=> fiscal n (M i) x) atTop (𝓝 (fiscal n Z x)) := by
       apply tendsto_finsetSum; intro i _; change Tendsto (fun y : ℕ=> dotProduct _ (_ *ᵥ _)) _ (𝓝 (dotProduct _ (_ *ᵥ _)))
       unfold Precision.K Matrix.mulVec dotProduct
       apply tendsto_finsetSum _ fun j _=> ?_
       simp only [Matrix.mul_apply]
       apply Tendsto.const_mul
       apply tendsto_finsetSum; intro k _
       apply Tendsto.mul_const
       apply tendsto_finsetSum; intro u _
       apply Tendsto.mul_const
       apply tendsto_finsetSum; intro v _
       exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hh v) u).const_mul _ -- indices wrong?
lemma main_basis (j : ℕ) {q : ℕ} (hq : q≤2) (v : Dir G (a.S.side m j)) : tag q (payload W v p)=if q=2 then fiscal _ ((bedFull W p _).transpose*bedFull W p _) v else 0 := by
  let n := a.S.side m j
  /-have hs := tendsto_nhds_unique (hT.flow_jet (e:=q) v) (f:=fun i=>tag q (payload (wick (M i)) v p)) -/
  apply tendsto_nhds_unique (hT.flow_jet (e:=q) v) ((show Tendsto (fun i=>Tensor.diagonal (spray (fun i=>knotted n p (M i)) q i) v) atTop (𝓝 _) from ?_).congr' ((hT.groomed n).and hT.mask |>.mono fun i ⟨hu,hb⟩=> ((Eq.symm (ray_tag (fun u : Dir G n=>knotted n p (M i) u) (hu.of_le (finite_cap q)) v)).trans (Eq.symm (congr_arg (tag q) (payload_main _ _ hb))))))
  by_cases hx : q=2
  · subst q; simp only [if_pos rfl]; exact (fiscal_tends (h.acts hT n) v).congr' ((fiscal_given h hT (z:=j)).mono fun i hi=> Eq.symm ((congr_arg (iteratedFDeriv ℝ 2 _ 0) (constant_two v)).trans (hi.2.2 v v)))
  rw [if_neg hx]
  refine tendsto_const_nhds.congr' ((fiscal_given h hT (z:=j)).mono fun i hi=>?_)
  change 0=iteratedFDeriv ℝ q (knotted n p (M i)) 0 (fun _=>v)
  rcases (Nat.eq_zero_or_pos q) with hx'|hx'
  · subst q; exact hi.1.symm
  obtain rfl := show q=1 by omega
  rw [iteratedFDeriv_one_apply,hi.2.1]; rfl

include h' ht
lemma full_basis (j : ℕ) : Junction (fun i=>knotted (a.S.side m j) p (M i)) (fun i=>knotted _ p (M' i)) 2 := by
  refine viaDiag (hT.groomed _) (ht.groomed _) fun q hq v => ?_
  refine ⟨tag q (payload X v p),?_,(ht.flow_jet (e:=q) v).congr' (ht.mask.mono fun i hi=>(congr_arg (tag q) (payload_main _ v hi)))⟩
  have hw := (hT.flow_jet (e:=q) v).congr' (hT.mask.mono fun i hi=>(congr_arg (tag q) (payload_main _ v hi)))
  rw [main_basis h hT _ hq, Harbor.same_acts h hT h' ht] at hw
  rw [main_basis h' ht _ hq]
  exact hw
end YM.UVExt.Paths
